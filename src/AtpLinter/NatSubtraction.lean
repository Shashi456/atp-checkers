/-
  Nat Subtraction Detector

  Detects potentially unsafe natural number subtractions where:
  - `a - b` is used on `Nat` without a guard like `h : b ≤ a` or `h : a ≥ b`

  In Lean 4, Nat subtraction is truncated: if a < b, then a - b = 0
  This is a common source of formalization errors.

  SOUNDNESS NOTES:
  - Uses full-scope traversal: when analyzing a binder type, ALL hypotheses
    from the declaration signature are available for guard proving, regardless
    of binder ordering. This matches the proof-state semantics where all
    hypotheses are simultaneously available.
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
  let result ← withSnapshot snap (proveNatSubGuard? lhs rhs (useGrind := true))
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
-/
partial def findNatSubtractions (e : Expr) (lctx : LocalContext) : MetaM (Array NatSubInfo) := do
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

  -- Recurse into sub-expressions, extending context for nested binders
  match e with
  | .app f a =>
      results := results ++ (← findNatSubtractions f lctx)
      results := results ++ (← findNatSubtractions a lctx)

  | .lam n ty body bi =>
      results := results ++ (← findNatSubtractions ty lctx)
      let bodyResults ← withLocalDecl n bi ty fun fvar => do
        let lctx' ← getLCtx
        findNatSubtractions (body.instantiate1 fvar) lctx'
      results := results ++ bodyResults

  | .forallE n ty body bi =>
      results := results ++ (← findNatSubtractions ty lctx)
      let bodyResults ← withLocalDecl n bi ty fun fvar => do
        let lctx' ← getLCtx
        findNatSubtractions (body.instantiate1 fvar) lctx'
      results := results ++ bodyResults

  | .letE name type value body _ =>
      results := results ++ (← findNatSubtractions type lctx)
      results := results ++ (← findNatSubtractions value lctx)
      let bodyResults ← withLetDecl name type value fun fvar => do
        let lctx' ← getLCtx
        findNatSubtractions (body.instantiate1 fvar) lctx'
      results := results ++ bodyResults

  | .mdata _ inner =>
      results := results ++ (← findNatSubtractions inner lctx)

  | .proj _ _ inner =>
      results := results ++ (← findNatSubtractions inner lctx)

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
  -- for guard checking, regardless of binder order (full proof-state semantics).
  let typeSubs ← withLCtx emptyLCtx #[] do
    forallTelescope type fun fvars body => do
      let fullLCtx ← getLCtx
      let mut subs := #[]
      for fvar in fvars do
        let ldecl ← fvar.fvarId!.getDecl
        subs := subs ++ (← findNatSubtractions ldecl.type fullLCtx)
      subs := subs ++ (← findNatSubtractions body fullLCtx)
      return subs
  allSubs := allSubs ++ typeSubs

  -- Analyze value: open all lambda binders first for full-scope guard checking.
  -- Only analyze value for non-Prop definitions (skip proof terms).
  if let some value := value? then
    let isPropType ← isProp type
    if !isPropType then
      let valueSubs ← withLCtx emptyLCtx #[] do
        lambdaTelescope value fun fvars body => do
          let fullLCtx ← getLCtx
          let mut subs := #[]
          for fvar in fvars do
            let ldecl ← fvar.fvarId!.getDecl
            subs := subs ++ (← findNatSubtractions ldecl.type fullLCtx)
          subs := subs ++ (← findNatSubtractions body fullLCtx)
          return subs
      allSubs := allSubs ++ valueSubs

  -- Deduplicate findings
  allSubs := deduplicateSubtractions allSubs

  let unguarded := allSubs.filter (·.guardEvidence.isNone)

  return {
    declName := declName
    subtractions := allSubs
    unguardedCount := unguarded.size
  }

/-- Generate a report for a single declaration -/
def generateReport (result : AnalysisResult) : MetaM String := do
  if result.subtractions.isEmpty then
    return s!"✓ {result.declName}: No Nat subtractions found"

  let mut report := s!"⚠ {result.declName}: Found {result.subtractions.size} Nat subtraction(s)\n"

  let mut i := 0
  for sub in result.subtractions do
    i := i + 1
    -- Use pre-computed strings captured at analysis time
    let status := match sub.guardEvidence with
      | some ev => s!"✓ guarded ({ev})"
      | none => "✗ UNGUARDED"
    report := report ++ s!"  [{i}] {sub.lhsStr} - {sub.rhsStr} [{status}]\n"

  if result.unguardedCount > 0 then
    report := report ++ s!"  WARNING: {result.unguardedCount} unguarded subtraction(s) may cause truncation issues\n"

  return report

end AtpLinter.NatSubtraction
