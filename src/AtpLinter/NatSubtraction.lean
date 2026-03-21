/-
  Nat Subtraction Detector

  Detects potentially unsafe natural number subtractions where:
  - `a - b` is used on `Nat` without a guard like `h : b ≤ a` or `h : a ≥ b`

  In Lean 4, Nat subtraction is truncated: if a < b, then a - b = 0
  This is a common source of formalization errors.

  SOUNDNESS NOTES:
  - Uses prop-full, data-prefix binder-type analysis: when analyzing a
    binder type, all propositional hypotheses are available regardless of
    binder ordering, but later data binders are excluded to prevent
    circular derived-fact justification (see mkSafeLCtxForType).
    hypotheses are simultaneously available.
  - Conjunction-aware guard mining is polarity-aware. Sibling conjuncts are
    shared only in positive/asserted position (e.g. `b ≤ a ∧ a - b = c`). They
    are NOT shared through negation or implication antecedents, because those
    contexts do not assert the guard.
  - Uses syntactic zero detection (NOT isDefEq) to avoid runaway reductions
-/

import Lean
import Lean.Elab.Command
import Lean.Meta.Basic
import AtpLinter.Basic
import AtpLinter.SemanticGuards

open Lean Elab Meta Term
open AtpLinter.SemanticGuards
open AtpLinter (isSyntacticZero ppExprSimple)

namespace AtpLinter.NatSubtraction

/-- Information about a detected Nat subtraction -/
structure NatSubInfo where
  expr : Expr
  lhs : Expr
  rhs : Expr
  guardEvidence : Option String := none
  unsafetyEvidence : Option String := none  -- Proof that lhs < rhs (truncation occurs)
  -- Pretty-printed strings captured at analysis time for correct binder names
  lhsStr : String := ""
  rhsStr : String := ""
  -- For deduplication
  exprHash : UInt64 := 0
  deriving Inhabited

/-- Check if an expression is a Nat type (with whnf for robustness) -/
def isNatType (e : Expr) : MetaM Bool := do
  let type ← whnf (← inferType e)
  return type.isConstOf ``Nat

/-- Check subtraction guard using semantic prover -/
def checkSubtractionGuard (lhs rhs : Expr) (lctx : LocalContext) (localInsts : LocalInstances) : MetaM (Option String) := do
  let snap : LocalCtxSnapshot := { lctx := lctx, insts := localInsts }
  let result ← withSnapshot snap (proveNatSubGuard? lhs rhs)
  match result with
  | some provedBy => return some provedBy.toString
  | none => return none

/-- Try to prove lhs < rhs (unsafety proof for Nat subtraction).
    Called when safety proof (rhs ≤ lhs) fails. If this succeeds, the finding
    upgrades from "maybe" to "proven". -/
def checkSubtractionUnsafe (lhs rhs : Expr) (lctx : LocalContext) (localInsts : LocalInstances) : MetaM (Option String) := do
  let snap : LocalCtxSnapshot := { lctx := lctx, insts := localInsts }
  let goal? ← withSnapshot snap do
    try pure (some (← Lean.Meta.mkLt lhs rhs))
    catch _ => pure none
  match goal? with
  | some goal =>
    match ← tryProveUnsafety? goal snap with
    | some pb => return some pb.toString
    | none => return none
  | none => return none

/--
Recursively find all Nat subtractions in an expression.

When called from `analyzeDecl`, the `lctx` parameter contains the FULL local
context (all hypotheses from the declaration signature), so guard checking sees
all available hypotheses regardless of binder order. For nested binders
encountered during recursion, the context is extended naturally.

Positive-position conjunctions share sibling facts as local hypotheses. This is
polarity-aware: conjunctions under negation or in implication antecedents do not
share guards.
-/
partial def findNatSubtractions (e : Expr) (lctx : LocalContext) (positive : Bool := true) : MetaM (Array NatSubInfo) := do
  let mut results := #[]
  let localInsts ← getLocalInstances

  -- Check if this is HSub.hSub (the subtraction operator)
  if e.isAppOfArity ``HSub.hSub 6 then
    let args := e.getAppArgs
    let lhs := args[4]!
    let rhs := args[5]!

    -- Check if operating on Nat
    if ← isNatType lhs then
      -- Skip if rhs is syntactically 0 (a - 0 is always safe)
      if !isSyntacticZero rhs then
        -- Use semantic guard checking
        let guardEvidence ← checkSubtractionGuard lhs rhs lctx localInsts
        let unsafetyEvidence ←
          if guardEvidence.isNone then
            checkSubtractionUnsafe lhs rhs lctx localInsts
          else pure none
        -- Capture pretty-printed strings NOW while in correct context
        let lhsStr ← ppExprSimple lhs
        let rhsStr ← ppExprSimple rhs
        results := results.push {
          expr := e
          lhs := lhs
          rhs := rhs
          guardEvidence := guardEvidence
          unsafetyEvidence := unsafetyEvidence
          lhsStr := lhsStr
          rhsStr := rhsStr
          exprHash := e.hash
        }

  -- Also check for Nat.sub directly (sometimes used instead of HSub.hSub)
  if e.isAppOfArity ``Nat.sub 2 then
    let args := e.getAppArgs
    let lhs := args[0]!
    let rhs := args[1]!

    if !isSyntacticZero rhs then
      let guardEvidence ← checkSubtractionGuard lhs rhs lctx localInsts
      let unsafetyEvidence ←
        if guardEvidence.isNone then
          checkSubtractionUnsafe lhs rhs lctx localInsts
        else pure none
      let lhsStr ← ppExprSimple lhs
      let rhsStr ← ppExprSimple rhs
      results := results.push {
        expr := e
        lhs := lhs
        rhs := rhs
        guardEvidence := guardEvidence
        unsafetyEvidence := unsafetyEvidence
        lhsStr := lhsStr
        rhsStr := rhsStr
        exprHash := e.hash
      }

  -- Recurse into sub-expressions, extending context for nested binders.
  -- `positive` tracks logical polarity: true = asserted, false = negated/hypothesis.
  -- The conjunction rule only fires in positive position.
  match e with
  | .app f a =>
      if positive && e.isAppOfArity ``And 2 then
        -- Conjunction in positive position: share sibling conjuncts as hypotheses
        let lhs := e.getAppArgs[0]!
        let rhs := e.getAppArgs[1]!

        let lhsResults ← withLCtx lctx localInsts do
          withLocalDeclD `_atpAnd rhs fun _ => do
            let lctx' ← getLCtx
            findNatSubtractions lhs lctx' positive
        for r in lhsResults do
          results := results.push r

        let rhsResults ← withLCtx lctx localInsts do
          withLocalDeclD `_atpAnd lhs fun _ => do
            let lctx' ← getLCtx
            findNatSubtractions rhs lctx' positive
        for r in rhsResults do
          results := results.push r
      else if f.isConstOf ``Not then
        -- Negation: flip polarity for the argument
        for r in (← findNatSubtractions a lctx (!positive)) do
          results := results.push r
      else
        for r in (← findNatSubtractions f lctx positive) do
          results := results.push r
        for r in (← findNatSubtractions a lctx positive) do
          results := results.push r

  | .lam n ty body bi =>
      for r in (← findNatSubtractions ty lctx positive) do
        results := results.push r
      let bodyResults ← withLocalDecl n bi ty fun fvar => do
        let lctx' ← getLCtx
        findNatSubtractions (body.instantiate1 fvar) lctx' positive
      for r in bodyResults do
        results := results.push r

  | .forallE n ty body bi =>
      -- Type (hypothesis) is in flipped polarity; body (conclusion) keeps same
      for r in (← findNatSubtractions ty lctx (!positive)) do
        results := results.push r
      let bodyResults ← withLocalDecl n bi ty fun fvar => do
        let lctx' ← getLCtx
        findNatSubtractions (body.instantiate1 fvar) lctx' positive
      for r in bodyResults do
        results := results.push r

  | .letE name type value body _ =>
      for r in (← findNatSubtractions type lctx positive) do
        results := results.push r
      for r in (← findNatSubtractions value lctx positive) do
        results := results.push r
      let bodyResults ← withLetDecl name type value fun fvar => do
        let lctx' ← getLCtx
        findNatSubtractions (body.instantiate1 fvar) lctx' positive
      for r in bodyResults do
        results := results.push r

  | .mdata _ inner =>
      for r in (← findNatSubtractions inner lctx positive) do
        results := results.push r

  | .proj _ _ inner =>
      for r in (← findNatSubtractions inner lctx positive) do
        results := results.push r

  | _ => pure ()

  return results

/-- Result of analyzing a declaration -/
structure AnalysisResult where
  declName : Name
  subtractions : Array NatSubInfo
  unguardedCount : Nat
  deriving Inhabited

/-- Deduplicate subtractions by semantic key (pretty-printed operands + guard status).
    When duplicates collide, the entry with stronger evidence wins.
    Uses insertion-order to guarantee deterministic output. -/
def deduplicateSubtractions (subs : Array NatSubInfo) : Array NatSubInfo :=
  let init : Std.HashMap (String × String × Bool) Nat × Array NatSubInfo := ({}, #[])
  let (_, out) := subs.foldl (init := init) fun (seen, out) sub =>
    let key := (sub.lhsStr, sub.rhsStr, sub.guardEvidence.isSome)
    match seen[key]? with
    | some idx =>
      if (out[idx]!).unsafetyEvidence.isNone && sub.unsafetyEvidence.isSome then
        (seen, out.set! idx sub)
      else
        (seen, out)
    | none => (seen.insert key out.size, out.push sub)
  out

/-- Analyze a declaration for Nat subtraction issues -/
def analyzeDecl (declName : Name) : MetaM AnalysisResult := do
  let env ← getEnv
  let some constInfo := env.find? declName
    | throwError "Declaration {declName} not found"

  let type := constInfo.type
  let value? := constInfo.value?

  let emptyLCtx : LocalContext := {}

  let mut allSubs := #[]

  -- Analyze the type: open ALL binders first so every hypothesis is available
  -- for guard checking. Binder-type analysis uses prop-full, data-prefix
  let typeSubs ← withLCtx emptyLCtx #[] do
    forallTelescope type fun fvars body => do
      let fullLCtx ← getLCtx
      let mut subs := #[]
      for j in [:fvars.size] do
        let fvar := fvars[j]!
        let ldecl ← fvar.fvarId!.getDecl
        -- Only use preceding binders (0..j-1) when analyzing binder j's type.
        -- Later binders did not exist when this type was written, so their
        -- derived facts (Fin.isLt, Subtype.property) must not circularly
        -- justify the type. E.g. (x y : Fin (n - k)) — neither x nor y
        -- should contribute Fin.isLt to prove k ≤ n.
        let lctxForType := ← mkSafeLCtxForType fullLCtx fvars j
        for r in (← findNatSubtractions ldecl.type lctxForType) do
          subs := subs.push r
      for r in (← findNatSubtractions body fullLCtx) do
        subs := subs.push r
      return subs
  for r in typeSubs do
    allSubs := allSubs.push r

  -- Analyze value: open all lambda binders first for full-scope guard checking.
  -- Only analyze value for non-Prop definitions (skip proof terms).
  if let some value := value? then
    let isPropType ← isProp type
    if !isPropType then
      let valueSubs ← withLCtx emptyLCtx #[] do
        lambdaTelescope value fun fvars body => do
          let fullLCtx ← getLCtx
          let mut subs := #[]
          for j in [:fvars.size] do
            let fvar := fvars[j]!
            let ldecl ← fvar.fvarId!.getDecl
            let lctxForType := ← mkSafeLCtxForType fullLCtx fvars j
            for r in (← findNatSubtractions ldecl.type lctxForType) do
              subs := subs.push r
          for r in (← findNatSubtractions body fullLCtx) do
            subs := subs.push r
          return subs
      for r in valueSubs do
        allSubs := allSubs.push r

  -- Deduplicate findings
  allSubs := deduplicateSubtractions allSubs

  let unguarded := allSubs.filter (·.guardEvidence.isNone)

  return {
    declName := declName
    subtractions := allSubs
    unguardedCount := unguarded.size
  }

end AtpLinter.NatSubtraction
