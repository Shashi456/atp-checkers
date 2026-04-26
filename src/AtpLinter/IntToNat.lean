/-
  Int.toNat Detector

  Detects usage of Int.toNat which truncates negative integers to 0.

  `Int.toNat : Int → Nat` returns:
  - n if the input is non-negative (Int.ofNat n)
  - 0 if the input is negative

  This can silently corrupt values when converting from Int to Nat
  without checking that the Int is non-negative.

  SOUNDNESS NOTES:
  - Uses prop-full, data-prefix binder-type analysis: when analyzing a
    binder type, all propositional hypotheses are available regardless of
    binder ordering, but later data binders are excluded to prevent
    circular derived-fact justification (see mkSafeLCtxForType).
    hypotheses are simultaneously available.
  - Int.natAbs is reported separately (not as "guarded") since it has
    different semantics (absolute value, not truncation)
-/

import Lean
import Lean.Elab.Command
import Lean.Meta.Basic
import AtpLinter.Basic
import AtpLinter.SemanticGuards

open Lean Elab Meta Term
open AtpLinter (ppExprSimple mkSafeLCtxForType)
open AtpLinter.SemanticGuards

namespace AtpLinter.IntToNat

/-- Kind of Int-to-Nat conversion -/
inductive ConversionKind where
  | toNat   -- Int.toNat: truncates negatives to 0
  | natAbs  -- Int.natAbs: takes absolute value
  deriving Inhabited, Repr, BEq, Hashable

/-- Information about a detected Int-to-Nat conversion -/
structure ToNatInfo where
  expr : Expr
  argument : Expr
  kind : ConversionKind
  guardEvidence : Option String := none
  unsafetyEvidence : Option String := none  -- Proof that argument < 0 (truncation occurs)
  -- Pretty-printed string captured at analysis time for correct binder names
  argumentStr : String := ""
  -- For deduplication
  exprHash : UInt64 := 0
  deriving Inhabited


/-- Check Int.toNat guard using semantic prover -/
def checkIntToNatGuard (intExpr : Expr) (lctx : LocalContext) (localInsts : LocalInstances) : MetaM (Option String) := do
  let snap : LocalCtxSnapshot := { lctx := lctx, insts := localInsts }
  let result ← withSnapshot snap (proveIntNonneg? intExpr)
  match result with
  | some provedBy => return some provedBy.toString
  | none => return none

/-- Try to prove argument < 0 (unsafety proof for Int.toNat).
    Called when safety proof (0 ≤ x) fails. If this succeeds, the finding
    upgrades from "maybe" to "proven". -/
def checkIntToNatUnsafe (intExpr : Expr) (lctx : LocalContext) (localInsts : LocalInstances) : MetaM (Option String) := do
  let snap : LocalCtxSnapshot := { lctx := lctx, insts := localInsts }
  let goal? ← withSnapshot snap do
    try
      let zero := Lean.mkIntLit 0
      pure (some (← Lean.Meta.mkLt intExpr zero))
    catch _ => pure none
  match goal? with
  | some goal =>
    match ← tryProveUnsafety? goal snap with
    | some pb => return some pb.toString
    | none => return none
  | none => return none

/--
Recursively find all Int.toNat usages in an expression.

When called from `analyzeDecl`, the `lctx` parameter contains the FULL local
context (all hypotheses from the declaration signature), so guard checking sees
all available hypotheses regardless of binder order. For nested binders
encountered during recursion, the context is extended naturally.

Positive-position conjunctions share sibling facts as local hypotheses. This is
polarity-aware: conjunctions under negation or in implication antecedents do not
share guards.
-/
partial def findIntToNat (e : Expr) (lctx : LocalContext) (positive : Bool := true) : MetaM (Array ToNatInfo) := do
  let mut results := #[]
  let localInsts ← getLocalInstances

  -- Check for Int.toNat
  if e.isAppOfArity ``Int.toNat 1 then
    let args := e.getAppArgs
    let argument := args[0]!
    -- Use semantic guard checking
    let guardEvidence ← checkIntToNatGuard argument lctx localInsts
    let unsafetyEvidence ←
      if guardEvidence.isNone then
        checkIntToNatUnsafe argument lctx localInsts
      else pure none
    -- Capture pretty-printed string NOW while in correct context
    let argumentStr ← ppExprSimple argument
    results := results.push {
      expr := e
      argument := argument
      kind := .toNat
      guardEvidence := guardEvidence
      unsafetyEvidence := unsafetyEvidence
      argumentStr := argumentStr
      exprHash := e.hash
    }

  -- Also check for natAbs which has similar issues
  -- (though natAbs returns |n| rather than max(n,0))
  -- NOTE: We report natAbs separately, NOT as "guarded", because it has
  -- different semantics. Users should review if absolute value is intended.
  if e.isAppOfArity ``Int.natAbs 1 then
    let args := e.getAppArgs
    let argument := args[0]!
    let argumentStr ← ppExprSimple argument
    results := results.push {
      expr := e
      argument := argument
      kind := .natAbs
      guardEvidence := none  -- Not "guarded" - flagged for review
      argumentStr := argumentStr
      exprHash := e.hash
    }

  -- Recurse into sub-expressions, extending context for nested binders.
  -- `positive` tracks logical polarity for conjunction sharing.
  let localInsts ← getLocalInstances
  match e with
  | .app f a =>
      if positive && e.isAppOfArity ``And 2 then
        let lhs := e.getAppArgs[0]!
        let rhs := e.getAppArgs[1]!
        let lhsResults ← withLCtx lctx localInsts do
          withLocalDeclD `_atpAnd rhs fun _ => do
            let lctx' ← getLCtx
            findIntToNat lhs lctx' positive
        for r in lhsResults do results := results.push r
        let rhsResults ← withLCtx lctx localInsts do
          withLocalDeclD `_atpAnd lhs fun _ => do
            let lctx' ← getLCtx
            findIntToNat rhs lctx' positive
        for r in rhsResults do results := results.push r
      else if f.isConstOf ``Not then
        for r in (← findIntToNat a lctx (!positive)) do results := results.push r
      else
        for r in (← findIntToNat f lctx positive) do results := results.push r
        for r in (← findIntToNat a lctx positive) do results := results.push r

  | .lam n ty body bi =>
      for r in (← findIntToNat ty lctx positive) do results := results.push r
      let bodyResults ← withLocalDecl n bi ty fun fvar => do
        let lctx' ← getLCtx
        findIntToNat (body.instantiate1 fvar) lctx' positive
      for r in bodyResults do results := results.push r

  | .forallE n ty body bi =>
      for r in (← findIntToNat ty lctx (!positive)) do results := results.push r
      let bodyResults ← withLocalDecl n bi ty fun fvar => do
        let lctx' ← getLCtx
        findIntToNat (body.instantiate1 fvar) lctx' positive
      for r in bodyResults do results := results.push r

  | .letE name type value body _ =>
      for r in (← findIntToNat type lctx positive) do results := results.push r
      for r in (← findIntToNat value lctx positive) do results := results.push r
      let bodyResults ← withLetDecl name type value fun fvar => do
        let lctx' ← getLCtx
        findIntToNat (body.instantiate1 fvar) lctx' positive
      for r in bodyResults do results := results.push r

  | .mdata _ inner =>
      for r in (← findIntToNat inner lctx positive) do results := results.push r

  | .proj _ _ inner =>
      for r in (← findIntToNat inner lctx positive) do results := results.push r

  | _ => pure ()

  return results

/-- Result of analyzing a declaration -/
structure AnalysisResult where
  declName : Name
  conversions : Array ToNatInfo
  unguardedCount : Nat
  deriving Inhabited

/-- Deduplicate conversions by semantic key (pretty-printed argument + guard status).
    Uses insertion-order to guarantee deterministic output. -/
def deduplicateConversions (convs : Array ToNatInfo) : Array ToNatInfo :=
  let init : Std.HashMap (String × ConversionKind × Bool) Nat × Array ToNatInfo := ({}, #[])
  let (_, out) := convs.foldl (init := init) fun (seen, out) conv =>
    let key := (conv.argumentStr, conv.kind, conv.guardEvidence.isSome)
    match seen[key]? with
    | some idx =>
      if (out[idx]!).unsafetyEvidence.isNone && conv.unsafetyEvidence.isSome then
        (seen, out.set! idx conv)
      else
        (seen, out)
    | none => (seen.insert key out.size, out.push conv)
  out

/-- Analyze a declaration for Int.toNat issues -/
def analyzeDecl (declName : Name) : MetaM AnalysisResult := do
  let env ← getEnv
  let some constInfo := env.find? declName
    | throwError "Declaration {declName} not found"

  let type := constInfo.type
  let value? := constInfo.value?

  let emptyLCtx : LocalContext := {}

  let mut allConvs := #[]

  -- Analyze the type: open ALL binders first so every hypothesis is available
  -- for guard checking. Binder-type analysis uses prop-full, data-prefix
  let typeConvs ← withLCtx emptyLCtx #[] do
    forallTelescope type fun fvars body => do
      let fullLCtx ← getLCtx
      let mut convs := #[]
      for j in [:fvars.size] do
        let fvar := fvars[j]!
        let ldecl ← fvar.fvarId!.getDecl
        let lctxForType := ← mkSafeLCtxForType fullLCtx fvars j
        for r in (← findIntToNat ldecl.type lctxForType) do
          convs := convs.push r
      for r in (← findIntToNat body fullLCtx) do
        convs := convs.push r
      return convs
  for r in typeConvs do
    allConvs := allConvs.push r

  -- Analyze value: open all lambda binders first for full-scope guard checking.
  -- Only analyze value for non-Prop definitions (skip proof terms).
  if let some value := value? then
    let isPropType ← isProp type
    if !isPropType then
      let valueConvs ← withLCtx emptyLCtx #[] do
        lambdaTelescope value fun fvars body => do
          let fullLCtx ← getLCtx
          let mut convs := #[]
          for j in [:fvars.size] do
            let fvar := fvars[j]!
            let ldecl ← fvar.fvarId!.getDecl
            let lctxForType := ← mkSafeLCtxForType fullLCtx fvars j
            for r in (← findIntToNat ldecl.type lctxForType) do
              convs := convs.push r
          for r in (← findIntToNat body fullLCtx) do
            convs := convs.push r
          return convs
      for r in valueConvs do
        allConvs := allConvs.push r

  -- Deduplicate findings
  allConvs := deduplicateConversions allConvs

  -- Count unguarded Int.toNat (not natAbs, which is a different category)
  let unguarded := allConvs.filter (fun c => c.guardEvidence.isNone && c.kind == .toNat)

  return {
    declName := declName
    conversions := allConvs
    unguardedCount := unguarded.size
  }

end AtpLinter.IntToNat
