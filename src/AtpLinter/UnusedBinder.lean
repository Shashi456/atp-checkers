/-
  Unused Quantified Variable Detector

  Detects universally or existentially quantified variables that never
  appear in the body. Common autoformalization error where bound variables
  are introduced but forgotten.

  SUPPRESSION RULES:
  - Binder named `_` (explicitly unused)
  - Typeclass instance binders `[Foo α]`
  - Prop-typed binders (proof hypotheses, proof irrelevance applies)

  SOUNDNESS NOTES:
  - Uses hasLooseBVar to check if binder is referenced
  - Dependent types: binder may be used in later binder types, not just final body
-/

import Lean
import Lean.Elab.Command
import Lean.Meta.Basic
import AtpLinter.Basic

open Lean Elab Meta Term
open AtpLinter (ppExprSimple)

namespace AtpLinter.UnusedBinder

/-- Kind of binder (m2 fix: distinguish existentials from lambdas) -/
inductive BinderKind where
  | forall_  -- Universal quantifier (∀)
  | lambda   -- Lambda abstraction (λ)
  | exists_  -- Existential quantifier (∃)
  deriving Inhabited, BEq, Hashable

/-- Information about an unused binder -/
structure UnusedBinderInfo where
  name : Name
  type : Expr
  kind : BinderKind  -- m2 fix: now tracks forall/lambda/exists
  -- Pretty-printed strings
  nameStr : String := ""
  typeStr : String := ""
  deriving Inhabited


/-- Check if a name looks like an auto-generated underscore name -/
def isUnderscoreName (name : Name) : Bool :=
  let str := name.toString
  str == "_" || str.startsWith "_" || (str.splitOn "_hyg.").length > 1

/-- Check if a binder should be suppressed from unused warnings -/
def shouldSuppressBinder (name : Name) (bi : BinderInfo) (ty : Expr) : MetaM Bool := do
  -- Suppress if explicitly unnamed (includes hygiene-renamed underscores)
  if isUnderscoreName name then return true

  -- Suppress typeclass instances
  if bi == .instImplicit then return true

  -- Suppress implicit binders {α} - common in generic code, too noisy to warn
  if bi == .implicit then return true

  -- Suppress strict implicit binders ⦃α⦄
  if bi == .strictImplicit then return true

  -- Suppress Prop-typed binders (proof hypotheses)
  let isPropTy ← isProp ty
  if isPropTy then return true

  return false

/--
Recursively find unused binders in an expression.
Uses single-binder traversal (not telescope) to track each binder correctly.
-/
partial def findUnusedBinders (e : Expr) : MetaM (Array UnusedBinderInfo) := do
  let mut results := #[]

  match e with
  | .forallE n ty body bi =>
    -- Check if binder is unused: body doesn't reference bvar 0
    let isUnused := !body.hasLooseBVar 0

    if isUnused then
      -- Check if we should suppress this warning
      let suppress ← shouldSuppressBinder n bi ty
      if !suppress then
        let typeStr ← ppExprSimple ty
        results := results.push {
          name := n
          type := ty
          kind := .forall_
          nameStr := n.toString
          typeStr := typeStr
        }

    -- Recurse into body (instantiate to handle nested binders correctly)
    let bodyResults ← withLocalDecl n bi ty fun fvar => do
      findUnusedBinders (body.instantiate1 fvar)
    for r in bodyResults do
      results := results.push r

    -- Also check the type for unused binders (rare but possible)
    let typeResults ← findUnusedBinders ty
    for r in typeResults do
      results := results.push r

  | .lam n ty body bi =>
    let isUnused := !body.hasLooseBVar 0

    if isUnused then
      let suppress ← shouldSuppressBinder n bi ty
      if !suppress then
        let typeStr ← ppExprSimple ty
        -- m2 fix: kind will be set to .exists_ when detected via app case
        results := results.push {
          name := n
          type := ty
          kind := .lambda  -- May be overridden if parent is Exists
          nameStr := n.toString
          typeStr := typeStr
        }

    let bodyResults ← withLocalDecl n bi ty fun fvar => do
      findUnusedBinders (body.instantiate1 fvar)
    for r in bodyResults do
      results := results.push r

    let typeResults ← findUnusedBinders ty
    for r in typeResults do
      results := results.push r

  | .letE name type value body _ =>
    -- For let bindings, we don't report them as "unused quantified variables"
    -- since they're not quantifiers, but we still recurse into their components

    let typeResults ← findUnusedBinders type
    for r in typeResults do
      results := results.push r

    let valueResults ← findUnusedBinders value
    for r in valueResults do
      results := results.push r

    let bodyResults ← withLetDecl name type value fun fvar => do
      findUnusedBinders (body.instantiate1 fvar)
    for r in bodyResults do
      results := results.push r

  | .app f a =>
    -- m2 fix: Check for Exists application to properly label existential binders
    match f with
    | .const ``Exists _ =>
      -- This is an existential: Exists (fun x => body)
      match a with
      | .lam n ty body bi =>
        let isUnused := !body.hasLooseBVar 0
        if isUnused then
          let suppress ← shouldSuppressBinder n bi ty
          if !suppress then
            let typeStr ← ppExprSimple ty
            results := results.push {
              name := n
              type := ty
              kind := .exists_  -- Properly labeled as existential
              nameStr := n.toString
              typeStr := typeStr
            }
        -- Recurse into body
        let bodyResults ← withLocalDecl n bi ty fun fvar => do
          findUnusedBinders (body.instantiate1 fvar)
        for r in bodyResults do
          results := results.push r
        let typeResults ← findUnusedBinders ty
        for r in typeResults do
          results := results.push r
      | _ =>
        -- Exists applied to non-lambda (unusual)
        for r in (← findUnusedBinders a) do
          results := results.push r
    | _ =>
      -- Normal application
      for r in (← findUnusedBinders f) do
        results := results.push r
      for r in (← findUnusedBinders a) do
        results := results.push r

  | .mdata _ inner =>
    for r in (← findUnusedBinders inner) do
      results := results.push r

  | .proj _ _ inner =>
    for r in (← findUnusedBinders inner) do
      results := results.push r

  | _ => pure ()

  return results

/-- Result of analyzing a declaration -/
structure AnalysisResult where
  declName : Name
  unusedBinders : Array UnusedBinderInfo
  deriving Inhabited

/-- Deduplicate by name, type string, and binder kind -/
-- R1 fix: Include kind in key to distinguish ∀ vs λ vs ∃ binders
def deduplicateBinders (binders : Array UnusedBinderInfo) : Array UnusedBinderInfo :=
  let seen : Std.HashSet (String × String × BinderKind) := {}
  binders.foldl (init := (seen, #[])) (fun (seen, acc) binder =>
    let key := (binder.nameStr, binder.typeStr, binder.kind)
    if seen.contains key then
      (seen, acc)
    else
      (seen.insert key, acc.push binder)
  ) |>.2

/-- Analyze a declaration for unused binders -/
def analyzeDecl (declName : Name) : MetaM AnalysisResult := do
  let env ← getEnv
  let some constInfo := env.find? declName
    | throwError "Declaration {declName} not found"

  let type := constInfo.type

  -- Only check Prop-typed declarations (theorems/lemmas)
  -- For non-Prop declarations (defs), parameters in the type signature
  -- are typically used in the value, so flagging them is misleading.
  let isPropType ← isProp type
  if !isPropType then
    return { declName, unusedBinders := #[] }

  -- Analyze the type (statement) for unused binders
  let emptyLCtx : LocalContext := {}
  let unusedBinders ← withLCtx emptyLCtx #[] (findUnusedBinders type)

  -- Deduplicate
  let unusedBinders := deduplicateBinders unusedBinders

  return {
    declName := declName
    unusedBinders := unusedBinders
  }

end AtpLinter.UnusedBinder
