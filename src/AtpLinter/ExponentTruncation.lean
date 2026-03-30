/-
  Exponent Truncation Detector

  Detects cases where exponentiation with a non-positive exponent
  may produce unexpected results due to Lean's totalization semantics:
  - a^(-n) with Nat result has totalized semantics (0 or 1 depending on instance)
  - 2^0 = 1 (correct, but worth noting in some contexts)
  - a^b where b could be negative but result is Nat

  NOTE: The actual result of negative exponents depends on the HPow instance:
  - Some instances use Int.toNat which maps negative to 0, giving a^0 = 1
  - Others may produce different results

  SOUNDNESS NOTES:
  - Detects HPow.hPow and Nat.pow/Int.pow patterns
  - Uses omega to check if exponent is provably non-negative
  - Conservative: flags when non-negativity can't be proven

  LIMITATIONS:
  - Only checks Nat/Int exponents
  - Doesn't track exponent values through complex expressions
-/

import Lean
import Lean.Elab.Command
import Lean.Meta.Basic
import AtpLinter.Basic
import AtpLinter.SemanticGuards

open Lean Elab Meta Term
open AtpLinter (ppExprSimple mkSafeLCtxForType)
open AtpLinter.SemanticGuards

namespace AtpLinter.ExponentTruncation

/-- Type of exponentiation issue -/
-- R3 fix: Removed .zeroExponent (was dead code)
inductive ExponentIssue where
  | negativeExponent    -- Exponent is provably negative
  | possiblyNegative    -- Exponent might be negative (not guarded)
  deriving Inhabited, Repr, BEq, Hashable

/-- Information about a detected exponentiation issue -/
structure ExponentInfo where
  base : Expr
  exponent : Expr
  issue : ExponentIssue
  guardEvidence : Option ProvedBy
  negativeEvidence : Option ProvedBy := none  -- What proved the exponent is negative
  -- Pretty-printed strings
  baseStr : String := ""
  exponentStr : String := ""
  deriving Inhabited


/-- Check if an expression is an Int type -/
def isIntType (e : Expr) : MetaM Bool := do
  let ty ← inferType e
  let ty ← whnf ty
  return ty.isConstOf ``Int

/-- Check if an expression is a Nat type -/
def isNatType (e : Expr) : MetaM Bool := do
  let ty ← inferType e
  let ty ← whnf ty
  return ty.isConstOf ``Nat

/-- Try to prove an exponent is non-negative (0 ≤ exp) -/
def proveExponentNonNeg? (exp : Expr) : MetaM (Option ProvedBy) := do
  let saved ← Meta.saveState
  try
    -- Check if exponent is Nat (always non-negative)
    if ← isNatType exp then
      return some .simp  -- Nat is always ≥ 0 by definition

    -- For Int, try to prove 0 ≤ exp with enriched context
    if ← isIntType exp then
      withDerivedLocalFacts <| withExpandedAndHyps do
        let zero := Lean.mkIntLit 0
        let goal ← Lean.Meta.mkLe zero exp
        tryProve? goal (useOmega := true)
    else
      return none
  catch _ =>
    return none
  finally
    saved.restore

/-- Try to check if an exponent is definitely zero -/
def isDefinitelyZero (exp : Expr) : MetaM Bool := do
  let exp ← whnf exp
  -- Try normalized form first
  match exp.nat? with
  | some 0 => return true
  | some _ => return false
  | none =>
    -- Try raw literal form
    match exp with
    | .lit (.natVal 0) => return true
    | .app (.app (.const ``OfNat.ofNat _) _) nExpr =>
      match nExpr.nat? with
      | some 0 => return true
      | _ =>
        match nExpr with
        | .lit (.natVal 0) => return true
        | _ => return false
    | _ => return false

/-- Try to check if an exponent is definitely negative.
    Returns the ProvedBy method if successful. -/
def proveDefinitelyNegative? (exp : Expr) : MetaM (Option ProvedBy) := do
  let saved ← Meta.saveState
  try
    if ← isIntType exp then
      -- Try to prove exp < 0
      let zero := Lean.mkIntLit 0
      let goal ← Lean.Meta.mkLt exp zero
      tryProve? goal (useOmega := true) (useGrind := true)
    else
      return none
  catch _ =>
    return none
  finally
    saved.restore

/-- Extract exponentiation patterns from an expression -/
partial def findExponentPatterns (e : Expr) (lctx : LocalContext) (insts : LocalInstances)
    (positive : Bool := true) : MetaM (Array ExponentInfo) := do
  let mut results := #[]

  -- P2 fix: Use isAppOfArity instead of fragile nested pattern match
  -- HPow.hPow has 6 args: α β γ inst base exp
  if e.isAppOfArity ``HPow.hPow 6 then
    let args := e.getAppArgs
    let expType := args[1]!
    let resultType := args[2]!
    let baseExpr := args[4]!
    let expExpr := args[5]!

    -- Check if result type is Nat (where truncation matters)
    let resultType ← whnf resultType
    if resultType.isConstOf ``Nat then
      -- Check exponent type and value
      let expType ← whnf expType
      if expType.isConstOf ``Int then
        -- Int exponent to Nat result - potential issue
        let baseStr ← withLCtx lctx insts (ppExprSimple baseExpr)
        let expStr ← withLCtx lctx insts (ppExprSimple expExpr)

        -- Check if definitely negative
        let negProof ← withLCtx lctx insts (proveDefinitelyNegative? expExpr)
        if let some negPb := negProof then
          results := results.push {
            base := baseExpr
            exponent := expExpr
            issue := .negativeExponent
            guardEvidence := none
            negativeEvidence := some negPb
            baseStr := baseStr
            exponentStr := expStr
          }
        else
          -- Check if we can prove non-negative
          let guard ← withLCtx lctx insts (proveExponentNonNeg? expExpr)
          if guard.isNone then
            -- R3 fix: Removed dead .zeroExponent check - just report as possibly negative
            results := results.push {
              base := baseExpr
              exponent := expExpr
              issue := .possiblyNegative
              guardEvidence := none
              baseStr := baseStr
              exponentStr := expStr
            }

  -- R3 fix: Removed Nat.pow zero-exponent check (was dead code - zero exponent just gives 1)

  -- Recurse into subexpressions with polarity tracking
  match e with
  | .app f a =>
    if positive && e.isAppOfArity ``And 2 then
      let lhs := e.getAppArgs[0]!
      let rhs := e.getAppArgs[1]!
      let lhsResults ← withLCtx lctx insts do
        withLocalDeclD `_atpAnd rhs fun _ => do
          let lctx' ← getLCtx
          let insts' ← getLocalInstances
          findExponentPatterns lhs lctx' insts' positive
      for r in lhsResults do results := results.push r
      let rhsResults ← withLCtx lctx insts do
        withLocalDeclD `_atpAnd lhs fun _ => do
          let lctx' ← getLCtx
          let insts' ← getLocalInstances
          findExponentPatterns rhs lctx' insts' positive
      for r in rhsResults do results := results.push r
    else if f.isConstOf ``Not then
      for r in (← findExponentPatterns a lctx insts (!positive)) do results := results.push r
    else
      for r in (← findExponentPatterns f lctx insts positive) do results := results.push r
      for r in (← findExponentPatterns a lctx insts positive) do results := results.push r
  | .forallE n ty body bi =>
    for r in (← findExponentPatterns ty lctx insts (!positive)) do results := results.push r
    let bodyResults ← withLocalDecl n bi ty fun fvar => do
      let newLCtx ← getLCtx
      let newInsts ← getLocalInstances
      findExponentPatterns (body.instantiate1 fvar) newLCtx newInsts positive
    for r in bodyResults do results := results.push r
  | .lam n ty body bi =>
    for r in (← findExponentPatterns ty lctx insts positive) do results := results.push r
    let bodyResults ← withLocalDecl n bi ty fun fvar => do
      let newLCtx ← getLCtx
      let newInsts ← getLocalInstances
      findExponentPatterns (body.instantiate1 fvar) newLCtx newInsts positive
    for r in bodyResults do results := results.push r
  | .letE n ty val body _ =>
    for r in (← findExponentPatterns ty lctx insts positive) do results := results.push r
    for r in (← findExponentPatterns val lctx insts positive) do results := results.push r
    let bodyResults ← withLetDecl n ty val fun fvar => do
      let newLCtx ← getLCtx
      let newInsts ← getLocalInstances
      findExponentPatterns (body.instantiate1 fvar) newLCtx newInsts positive
    for r in bodyResults do results := results.push r
  | .mdata _ inner =>
    for r in (← findExponentPatterns inner lctx insts positive) do results := results.push r
  | .proj _ _ inner =>
    for r in (← findExponentPatterns inner lctx insts positive) do results := results.push r
  | _ => pure ()

  return results

/-- Result of analyzing a declaration -/
structure AnalysisResult where
  declName : Name
  exponents : Array ExponentInfo
  deriving Inhabited

/-- Deduplicate by expression strings and issue type -/
-- R1 fix: Include issue in key to avoid merging different severities
def deduplicateExponents (exps : Array ExponentInfo) : Array ExponentInfo :=
  let seen : Std.HashSet (String × String × ExponentIssue) := {}
  exps.foldl (init := (seen, #[])) (fun (seen, acc) exp =>
    let key := (exp.baseStr, exp.exponentStr, exp.issue)
    if seen.contains key then
      (seen, acc)
    else
      (seen.insert key, acc.push exp)
  ) |>.2

/-- Analyze a declaration for exponent truncation issues -/
def analyzeDecl (declName : Name) : MetaM AnalysisResult := do
  let env ← getEnv
  let some constInfo := env.find? declName
    | throwError "Declaration {declName} not found"

  let type := constInfo.type
  let value? := constInfo.value?

  let emptyLCtx : LocalContext := {}

  let mut allExps := #[]

  -- Analyze the type: open ALL binders first so every hypothesis is available
  -- for guard checking. Binder-type analysis uses prop-full, data-prefix
  let typeExps ← withLCtx emptyLCtx #[] do
    forallTelescope type fun fvars body => do
      let fullLCtx ← getLCtx
      let fullInsts ← getLocalInstances
      let mut exps := #[]
      for j in [:fvars.size] do
        let fvar := fvars[j]!
        let ldecl ← fvar.fvarId!.getDecl
        let lctxForType := ← mkSafeLCtxForType fullLCtx fvars j
        for r in (← findExponentPatterns ldecl.type lctxForType fullInsts) do
          exps := exps.push r
      for r in (← findExponentPatterns body fullLCtx fullInsts) do
        exps := exps.push r
      return exps
  for r in typeExps do
    allExps := allExps.push r

  -- Analyze value: open all lambda binders first for full-scope guard checking.
  -- Only analyze value for non-Prop definitions (skip proof terms).
  if let some value := value? then
    let isPropType ← isProp type
    if !isPropType then
      let valueExps ← withLCtx emptyLCtx #[] do
        lambdaTelescope value fun fvars body => do
          let fullLCtx ← getLCtx
          let fullInsts ← getLocalInstances
          let mut exps := #[]
          for j in [:fvars.size] do
            let fvar := fvars[j]!
            let ldecl ← fvar.fvarId!.getDecl
            let lctxForType := ← mkSafeLCtxForType fullLCtx fvars j
            for r in (← findExponentPatterns ldecl.type lctxForType fullInsts) do
              exps := exps.push r
          for r in (← findExponentPatterns body fullLCtx fullInsts) do
            exps := exps.push r
          return exps
      for r in valueExps do
        allExps := allExps.push r

  -- R3 fix: Simplified filter (no more zeroExponent case)
  let filteredExps := allExps.filter fun exp =>
    exp.guardEvidence.isNone

  let exponents := deduplicateExponents filteredExps

  return {
    declName := declName
    exponents := exponents
  }

/-- Human-readable issue type -/
def ExponentIssue.toString : ExponentIssue → String
  | .negativeExponent => "negative exponent with Nat result (totalized semantics - may produce 0 or 1 depending on instance)"
  | .possiblyNegative => "possibly negative exponent (totalized semantics if negative)"

/-- Generate a report for a single declaration -/
def generateReport (result : AnalysisResult) : String :=
  if result.exponents.isEmpty then
    s!"✓ {result.declName}: No exponent truncation issues detected"
  else
    let expLines := result.exponents.toList.map fun exp =>
      s!"  {exp.baseStr} ^ {exp.exponentStr}: {exp.issue.toString}\n"
    s!"⚠ {result.declName}: Found {result.exponents.size} exponent issue(s)\n" ++
      String.join expLines ++
      s!"  Suggestion: Ensure exponent is non-negative for Nat result, or use Int/Rat\n"

end AtpLinter.ExponentTruncation
