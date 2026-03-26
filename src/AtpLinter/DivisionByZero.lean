/-
  Division by Zero Detector

  Detects potentially unsafe divisions where:
  - `a / b` is used without a guard like `h : b ≠ 0` or `h : b > 0`

  In Lean 4 / Mathlib:
  - For Nat: n / 0 = 0
  - For Int: division by zero returns 0
  - For Rat/Real/Fields: x / 0 = 0 (defined this way for totality)

  This is mathematically unusual and can cause formalization errors.

  SOUNDNESS NOTES:
  - Uses full-scope traversal: when analyzing a binder type, ALL hypotheses
    from the declaration signature are available for guard proving, regardless
    of binder ordering. This matches the proof-state semantics where all
    hypotheses are simultaneously available.
  - Guard checking is proof-based: divisor must be provably ≠ 0, not just
    syntactically a non-zero literal (which can be unsound for Fin, ZMod, etc.)
-/

import Lean
import Lean.Elab.Command
import Lean.Meta.Basic
import AtpLinter.Basic
import AtpLinter.SemanticGuards

open Lean Elab Meta Term
open AtpLinter.SemanticGuards
open AtpLinter (isSyntacticZero ppExprSimple isSyntacticNonZeroLiteral isSafeTypeForNonZeroLiteral)

namespace AtpLinter.DivisionByZero

/-- Information about a detected division -/
structure DivInfo where
  expr : Expr
  dividend : Expr
  divisor : Expr
  divisorType : Expr
  guardEvidence : Option String := none
  isDefinitelyZero : Bool := false  -- m7 fix: true if divisor is definitionally 0
  unsafetyEvidence : Option String := none  -- Proof that divisor IS zero
  -- Pretty-printed strings captured at analysis time for correct binder names
  dividendStr : String := ""
  divisorStr : String := ""
  -- For deduplication
  exprHash : UInt64 := 0
  deriving Inhabited

/-- Check divisor guard using semantic prover -/
def checkDivisorGuard (divisor : Expr) (lctx : LocalContext) (localInsts : LocalInstances) : MetaM (Option String) := do
  let snap : LocalCtxSnapshot := { lctx := lctx, insts := localInsts }
  let result ← withSnapshot snap (proveDivisorSafe? divisor (useGrind := true))
  match result with
  | some provedBy => return some provedBy.toString
  | none => return none

/-- Try to prove the divisor is zero (unsafety proof for division by zero).
    Called when safety proof (d ≠ 0) fails. If this succeeds, the finding
    upgrades from "maybe" to "proven". -/
def checkDivisorUnsafe (divisor : Expr) (divisorType : Expr) (lctx : LocalContext) (localInsts : LocalInstances) : MetaM (Option String) := do
  let snap : LocalCtxSnapshot := { lctx := lctx, insts := localInsts }
  -- Build goal under snapshot (needs local context for typeclass resolution)
  let goal? ← withSnapshot snap do
    match ← mkZeroOf divisorType with
    | some zero =>
      try pure (some (← Lean.Meta.mkAppM ``Eq #[divisor, zero]))
      catch _ => pure none
    | none => pure none
  match goal? with
  | some goal =>
    match ← tryProveUnsafety? goal snap with
    | some pb => return some pb.toString
    | none => return none
  | none => return none

/--
Recursively find all divisions in an expression.

When called from `analyzeDecl`, the `lctx` parameter contains the FULL local
context (all hypotheses from the declaration signature), so guard checking sees
all available hypotheses regardless of binder order. For nested binders
encountered during recursion, the context is extended naturally.
-/
partial def findDivisions (e : Expr) (lctx : LocalContext) (positive : Bool := true) : MetaM (Array DivInfo) := do
  let mut results := #[]
  let localInsts ← getLocalInstances

  -- Check for HDiv.hDiv (the division operator)
  -- HDiv.hDiv : {α β γ : Type} → [HDiv α β γ] → α → β → γ
  if e.isAppOfArity ``HDiv.hDiv 6 then
    let args := e.getAppArgs
    let dividend := args[4]!
    let divisor := args[5]!

    -- m7 fix: Check if divisor is syntactically zero first
    let defZero := isSyntacticZero divisor
    -- Get the actual type of the divisor
    let divisorType ← inferType divisor

    -- OPTIMIZATION: For safe types (ℕ, ℤ, ℚ, ℝ, ℂ), non-zero literals like 2, 3
    -- are trivially non-zero. Skip semantic checking for these cases.
    let guardEvidence ←
      if isSyntacticNonZeroLiteral divisor && isSafeTypeForNonZeroLiteral divisorType then
        pure (some "literal")
      else
        -- Use semantic guard checking (proof-based, not syntactic)
        -- This is sound even for types like Fin where literals can equal zero
        checkDivisorGuard divisor lctx localInsts
    -- Try unsafety proof when guard failed and not already definitionally zero
    let unsafetyEvidence ←
      if guardEvidence.isNone && !defZero then
        checkDivisorUnsafe divisor divisorType lctx localInsts
      else pure none

    -- Capture pretty-printed strings NOW while in correct context
    let dividendStr ← ppExprSimple dividend
    let divisorStr ← ppExprSimple divisor
    results := results.push {
      expr := e
      dividend := dividend
      divisor := divisor
      divisorType := divisorType
      guardEvidence := guardEvidence
      isDefinitelyZero := defZero
      unsafetyEvidence := unsafetyEvidence
      dividendStr := dividendStr
      divisorStr := divisorStr
      exprHash := e.hash
    }

  -- Check for Nat.div specifically
  if e.isAppOfArity ``Nat.div 2 then
    let args := e.getAppArgs
    let dividend := args[0]!
    let divisor := args[1]!

    let defZero := isSyntacticZero divisor
    -- Nat is always a safe type for non-zero literal optimization
    let guardEvidence ←
      if isSyntacticNonZeroLiteral divisor then pure (some "literal")
      else checkDivisorGuard divisor lctx localInsts
    let unsafetyEvidence ←
      if guardEvidence.isNone && !defZero then
        checkDivisorUnsafe divisor (mkConst ``Nat) lctx localInsts
      else pure none
    let dividendStr ← ppExprSimple dividend
    let divisorStr ← ppExprSimple divisor
    results := results.push {
      expr := e
      dividend := dividend
      divisor := divisor
      divisorType := mkConst ``Nat
      guardEvidence := guardEvidence
      isDefinitelyZero := defZero
      unsafetyEvidence := unsafetyEvidence
      dividendStr := dividendStr
      divisorStr := divisorStr
      exprHash := e.hash
    }

  -- Check for Int.tdiv (truncated toward zero)
  if e.isAppOfArity ``Int.tdiv 2 then
    let args := e.getAppArgs
    let dividend := args[0]!
    let divisor := args[1]!

    let defZero := isSyntacticZero divisor
    -- Int is always a safe type for non-zero literal optimization
    let guardEvidence ←
      if isSyntacticNonZeroLiteral divisor then pure (some "literal")
      else checkDivisorGuard divisor lctx localInsts
    let unsafetyEvidence ←
      if guardEvidence.isNone && !defZero then
        checkDivisorUnsafe divisor (mkConst ``Int) lctx localInsts
      else pure none
    let dividendStr ← ppExprSimple dividend
    let divisorStr ← ppExprSimple divisor
    results := results.push {
      expr := e
      dividend := dividend
      divisor := divisor
      divisorType := mkConst ``Int
      guardEvidence := guardEvidence
      isDefinitelyZero := defZero
      unsafetyEvidence := unsafetyEvidence
      dividendStr := dividendStr
      divisorStr := divisorStr
      exprHash := e.hash
    }

  -- Check for Int.fdiv (floored toward negative infinity)
  if e.isAppOfArity ``Int.fdiv 2 then
    let args := e.getAppArgs
    let dividend := args[0]!
    let divisor := args[1]!

    let defZero := isSyntacticZero divisor
    -- Int is always a safe type for non-zero literal optimization
    let guardEvidence ←
      if isSyntacticNonZeroLiteral divisor then pure (some "literal")
      else checkDivisorGuard divisor lctx localInsts
    let unsafetyEvidence ←
      if guardEvidence.isNone && !defZero then
        checkDivisorUnsafe divisor (mkConst ``Int) lctx localInsts
      else pure none
    let dividendStr ← ppExprSimple dividend
    let divisorStr ← ppExprSimple divisor
    results := results.push {
      expr := e
      dividend := dividend
      divisor := divisor
      divisorType := mkConst ``Int
      guardEvidence := guardEvidence
      isDefinitelyZero := defZero
      unsafetyEvidence := unsafetyEvidence
      dividendStr := dividendStr
      divisorStr := divisorStr
      exprHash := e.hash
    }

  -- Check for Int.ediv (Euclidean division)
  if e.isAppOfArity ``Int.ediv 2 then
    let args := e.getAppArgs
    let dividend := args[0]!
    let divisor := args[1]!

    let defZero := isSyntacticZero divisor
    -- Int is always a safe type for non-zero literal optimization
    let guardEvidence ←
      if isSyntacticNonZeroLiteral divisor then pure (some "literal")
      else checkDivisorGuard divisor lctx localInsts
    let unsafetyEvidence ←
      if guardEvidence.isNone && !defZero then
        checkDivisorUnsafe divisor (mkConst ``Int) lctx localInsts
      else pure none
    let dividendStr ← ppExprSimple dividend
    let divisorStr ← ppExprSimple divisor
    results := results.push {
      expr := e
      dividend := dividend
      divisor := divisor
      divisorType := mkConst ``Int
      guardEvidence := guardEvidence
      isDefinitelyZero := defZero
      unsafetyEvidence := unsafetyEvidence
      dividendStr := dividendStr
      divisorStr := divisorStr
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
            findDivisions lhs lctx' positive
        for r in lhsResults do
          results := results.push r

        let rhsResults ← withLCtx lctx localInsts do
          withLocalDeclD `_atpAnd lhs fun _ => do
            let lctx' ← getLCtx
            findDivisions rhs lctx' positive
        for r in rhsResults do
          results := results.push r
      else if f.isConstOf ``Not then
        -- Negation: flip polarity for the argument
        for r in (← findDivisions a lctx (!positive)) do
          results := results.push r
      else
        for r in (← findDivisions f lctx positive) do
          results := results.push r
        for r in (← findDivisions a lctx positive) do
          results := results.push r

  | .lam n ty body bi =>
      for r in (← findDivisions ty lctx positive) do
        results := results.push r
      let bodyResults ← withLocalDecl n bi ty fun fvar => do
        let lctx' ← getLCtx
        findDivisions (body.instantiate1 fvar) lctx' positive
      for r in bodyResults do
        results := results.push r

  | .forallE n ty body bi =>
      -- Type (hypothesis) is in flipped polarity; body (conclusion) keeps same
      for r in (← findDivisions ty lctx (!positive)) do
        results := results.push r
      let bodyResults ← withLocalDecl n bi ty fun fvar => do
        let lctx' ← getLCtx
        findDivisions (body.instantiate1 fvar) lctx' positive
      for r in bodyResults do
        results := results.push r

  | .letE name type value body _ =>
      for r in (← findDivisions type lctx positive) do
        results := results.push r
      for r in (← findDivisions value lctx positive) do
        results := results.push r
      let bodyResults ← withLetDecl name type value fun fvar => do
        let lctx' ← getLCtx
        findDivisions (body.instantiate1 fvar) lctx' positive
      for r in bodyResults do
        results := results.push r

  | .mdata _ inner =>
      for r in (← findDivisions inner lctx positive) do
        results := results.push r

  | .proj _ _ inner =>
      for r in (← findDivisions inner lctx positive) do
        results := results.push r

  | _ => pure ()

  return results

/-- Result of analyzing a declaration -/
structure AnalysisResult where
  declName : Name
  divisions : Array DivInfo
  unguardedCount : Nat
  deriving Inhabited

/-- Deduplicate divisions by semantic key (pretty-printed operands + guard status).
    Drops exprHash so semantically identical detections from different syntactic
    forms (HDiv.hDiv vs Nat.div) merge correctly.
    When duplicates collide, the entry with stronger evidence wins.
    Uses insertion-order to guarantee deterministic output. -/
def deduplicateDivisions (divs : Array DivInfo) : Array DivInfo :=
  let hasStrongEvidence (d : DivInfo) : Bool :=
    d.isDefinitelyZero || d.unsafetyEvidence.isSome
  let init : Std.HashMap (String × String × Bool) Nat × Array DivInfo := ({}, #[])
  let (_, out) := divs.foldl (init := init) fun (seen, out) div =>
    let key := (div.dividendStr, div.divisorStr, div.guardEvidence.isSome)
    match seen[key]? with
    | some idx =>
      if !hasStrongEvidence (out[idx]!) && hasStrongEvidence div then
        (seen, out.set! idx div)
      else
        (seen, out)
    | none => (seen.insert key out.size, out.push div)
  out

/-- Analyze a declaration for division issues -/
def analyzeDecl (declName : Name) : MetaM AnalysisResult := do
  let env ← getEnv
  let some constInfo := env.find? declName
    | throwError "Declaration {declName} not found"

  let type := constInfo.type
  let value? := constInfo.value?

  let emptyLCtx : LocalContext := {}

  let mut allDivs := #[]

  -- Analyze the type: open ALL binders first so every hypothesis is available
  -- for guard checking, regardless of binder order (full proof-state semantics).
  let typeDivs ← withLCtx emptyLCtx #[] do
    forallTelescope type fun fvars body => do
      let fullLCtx ← getLCtx
      let mut divs := #[]
      for fvar in fvars do
        let ldecl ← fvar.fvarId!.getDecl
        for r in (← findDivisions ldecl.type fullLCtx) do
          divs := divs.push r
      for r in (← findDivisions body fullLCtx) do
        divs := divs.push r
      return divs
  for r in typeDivs do
    allDivs := allDivs.push r

  -- Analyze value: open all lambda binders first for full-scope guard checking.
  -- Only analyze value for non-Prop definitions (skip proof terms).
  if let some value := value? then
    let isPropType ← isProp type
    if !isPropType then
      let valueDivs ← withLCtx emptyLCtx #[] do
        lambdaTelescope value fun fvars body => do
          let fullLCtx ← getLCtx
          let mut divs := #[]
          for fvar in fvars do
            let ldecl ← fvar.fvarId!.getDecl
            for r in (← findDivisions ldecl.type fullLCtx) do
              divs := divs.push r
          for r in (← findDivisions body fullLCtx) do
            divs := divs.push r
          return divs
      for r in valueDivs do
        allDivs := allDivs.push r

  -- Deduplicate findings (can get duplicates from HDiv.hDiv and Nat.div paths)
  allDivs := deduplicateDivisions allDivs

  let unguarded := allDivs.filter (·.guardEvidence.isNone)

  return {
    declName := declName
    divisions := allDivs
    unguardedCount := unguarded.size
  }

/-- Generate a report for a single declaration -/
def generateReport (result : AnalysisResult) : MetaM String := do
  if result.divisions.isEmpty then
    return s!"✓ {result.declName}: No divisions found"

  let mut report := s!"⚠ {result.declName}: Found {result.divisions.size} division(s)\n"

  let mut i := 0
  for div in result.divisions do
    i := i + 1
    -- Use pre-computed strings captured at analysis time
    let typeStr ← ppExprSimple div.divisorType
    let status := match div.guardEvidence with
      | some ev => s!"✓ guarded ({ev})"
      | none => "✗ UNGUARDED"
    report := report ++ s!"  [{i}] {div.dividendStr} / {div.divisorStr} (type: {typeStr}) [{status}]\n"

  if result.unguardedCount > 0 then
    report := report ++ s!"  WARNING: {result.unguardedCount} unguarded division(s) - divisor could be zero\n"

  return report

end AtpLinter.DivisionByZero
