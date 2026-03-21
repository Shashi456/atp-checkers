/-
  Analytic Domain Totalization Detector

  Detects totalized analytic functions used without proper domain guards:
  - `Real.sqrt x` without `0 ≤ x` (sqrt of negative returns 0 in mathlib)
  - `Real.log x` without `0 < x` (log of non-positive returns 0)
  - `x⁻¹` / `Inv.inv x` without `x ≠ 0` (inverse of zero returns 0)

  These are mathematically unusual and common autoformalization errors where
  domain constraints are forgotten.

  SOUNDNESS NOTES:
  - Pattern matches on function names (works when analyzing mathlib-using code)
  - Uses semantic guard proving: checks if domain constraint is provable
  - Only reports when guard is NOT provable (conservative)
  - Suppresses for obviously-safe arguments (squares, abs, norms, Nat.cast)

  LIMITATIONS:
  - omega doesn't help for Real inequalities; relies on assumption/simp
  - Only checks common patterns; custom domain functions not detected
-/

import Lean
import Lean.Elab.Command
import Lean.Meta.Basic
import AtpLinter.Basic
import AtpLinter.SemanticGuards

open Lean Elab Meta Term
open AtpLinter
open AtpLinter.SemanticGuards

namespace AtpLinter.AnalyticDomain

/-- Kind of analytic operation with totalized semantics -/
inductive AnalyticOp where
  | sqrt      -- Real.sqrt: requires 0 ≤ x
  | log       -- Real.log: requires 0 < x
  | inv       -- Inv.inv / x⁻¹: requires x ≠ 0
  | exp       -- Real.exp: no domain restriction (included for completeness)
  deriving Inhabited, BEq, Hashable, Repr

/-- Information about a detected analytic domain issue -/
structure AnalyticInfo where
  op : AnalyticOp
  arg : Expr
  argStr : String
  guardEvidence : Option ProvedBy
  unsafetyEvidence : Option String := none  -- Proof that dangerous condition holds
  exprHash : UInt64
  deriving Inhabited


/-- Check if an expression is a syntactic non-negative literal (0, 1, 2, etc.) -/
def isSyntacticNonNegLiteral (e : Expr) : Bool :=
  match e with
  | .lit (.natVal _) => true  -- Any Nat literal is non-negative
  -- OfNat.ofNat α n inst - the literal n is in the second argument position
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal _))) _ => true
  | .app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal _)) => true
  | .app (.app (.const ``Zero.zero _) _) _ => true
  | .app (.const ``Zero.zero _) _ => true
  | .app (.app (.const ``One.one _) _) _ => true
  | .app (.const ``One.one _) _ => true
  | _ => false

/-- Known standard magnitude functions that return non-negative values. -/
def isStandardMagnitudeName (name : Name) : Bool :=
  name == ``abs ||
  name == ``Norm.norm ||
  name == ``NNNorm.nnnorm ||
  name == ``Complex.normSq

/-- `Complex.normSq z` often elaborates through coercions and unfolds under
    `whnf`, so recognize it before normalization. -/
def containsComplexNormSqConst (e : Expr) : Bool :=
  e.getAppFn.isConstOf ``Complex.normSq ||
  e.getAppArgs.any (fun arg => arg.isConstOf ``Complex.normSq)

/-- Check if an expression is obviously non-negative (suppression heuristic) -/
def isObviouslyNonNeg (e : Expr) : MetaM Bool := do
  -- First check syntactic literals (fast, no whnf needed)
  if isSyntacticNonNegLiteral e then return true
  if containsComplexNormSqConst e then return true

  let e ← whnf e
  if containsComplexNormSqConst e then return true

  -- Known positive constants are certainly non-negative.
  if let .const name _ := e then
    let nameStr := name.toString
    if nameStr == "Real.pi" || nameStr == "π" then return true

  -- x^2 pattern (even power)
  if e.isAppOfArity ``HPow.hPow 6 then
    let exp := e.getAppArgs[5]!
    match exp.nat? with
    | some n => return n % 2 == 0  -- Even powers are non-negative
    | none => pure ()

  -- x * x pattern
  if e.isAppOfArity ``HMul.hMul 6 then
    let a := e.getAppArgs[4]!
    let b := e.getAppArgs[5]!
    if ← isDefEq a b then return true

  -- Nat.cast n (Nat coerced to Real is always non-negative)
  if e.isAppOfArity ``Nat.cast 3 then return true

  -- Check for abs / norm patterns by name
  let fn := e.getAppFn
  if let .const name _ := fn then
    let nameStr := name.toString
    if nameStr == "Real.sqrt" || nameStr == "NNReal.sqrt" then return true
    if nameStr == "Real.exp" then return true
    if isStandardMagnitudeName name then return true
    if e.getAppArgs.any (fun arg => arg.isConstOf ``Complex.normSq) then return true

  return false


/-- Check if an expression is obviously positive (suppression heuristic) -/
def isObviouslyPos (e : Expr) : MetaM Bool := do
  -- First check syntactic positive literals (fast, no whnf needed)
  if isSyntacticNonZeroLiteral e then return true

  let e ← whnf e

  -- Positive literal after whnf
  match e.nat? with
  | some n => return n > 0
  | none => pure ()

  -- Check for known positive constants (π, e, etc.)
  if let .const name _ := e then
    let nameStr := name.toString
    if nameStr == "Real.pi" || nameStr == "π" then return true
    if nameStr == "Real.exp" then return true  -- exp 1 = e

  -- exp x is always positive
  let fn := e.getAppFn
  if let .const name _ := fn then
    if name.toString == "Real.exp" then return true

  return false

/-- Prove 0 ≤ x. Enriches local context with derived facts and expanded
    conjunctions before proving, matching proveDivisorSafe?. -/
def proveNonNeg? (x : Expr) (lctx : LocalContext) (insts : LocalInstances) : MetaM (Option ProvedBy) := do
  -- First check obvious cases
  if ← isObviouslyNonNeg x then
    return some .simp

  let snap : LocalCtxSnapshot := { lctx := lctx, insts := insts }
  withSnapshot snap <| withGuardFacts do
    let ty ← inferType x
    match ← mkZeroOf ty with
    | none => return none
    | some zero =>
      let goal ← mkLE zero x
      -- omega won't help for Real; grind handles ordered-field reasoning
      tryProve? goal (useOmega := false)

/-- Prove 0 < x. Enriches local context with derived facts and expanded
    conjunctions before proving, matching proveDivisorSafe?. -/
def provePos? (x : Expr) (lctx : LocalContext) (insts : LocalInstances) : MetaM (Option ProvedBy) := do
  -- First check obvious cases
  if ← isObviouslyPos x then
    return some .simp

  let snap : LocalCtxSnapshot := { lctx := lctx, insts := insts }
  withSnapshot snap <| withGuardFacts do
    let ty ← inferType x
    match ← mkZeroOf ty with
    | none => return none
    | some zero =>
      let goal ← mkLT zero x
      -- omega won't help for Real; grind handles ordered-field reasoning
      tryProve? goal (useOmega := false)

/-- Prove x ≠ 0. Enriches local context with derived facts and expanded
    conjunctions, and tries structural nonzero closure (mul_ne_zero,
    pow_ne_zero) before falling back to general provers. -/
def proveNeZero? (x : Expr) (lctx : LocalContext) (insts : LocalInstances) : MetaM (Option ProvedBy) := do
  -- Shortcut: syntactic positive literals on safe types are obviously non-zero
  if isSyntacticNonZeroLiteral x then
    let ty ← inferType x
    if ← isSafeTypeForNonZeroLiteral ty then
      return some .simp

  let snap : LocalCtxSnapshot := { lctx := lctx, insts := insts }
  withSnapshot snap <| withGuardFacts do
    let ty ← inferType x
    match ← mkZeroOf ty with
    | none => return none
    | some zero =>
      -- Try direct proof first
      let goal ← mkAppM ``Ne #[x, zero]
      if let some how ← tryProve? goal (useOmega := true) (useGrind := true) then
        return some how
      -- Try structural nonzero closure (mul_ne_zero, pow_ne_zero)
      if let some (_, how) ← proveStructuralNonzero? x (useGrind := true) then
        return some how
      -- Cast transport: unwrap Nat.cast/Int.cast/Rat.cast, prove nonzero on source
      if let some (_, how) ← proveCastTransport? x (useGrind := true) then
        return some how
      -- Try positivity: 0 < x → x ≠ 0
      try
        let gPos ← Lean.Meta.mkLt zero x
        if let some _ ← tryProve? gPos (useOmega := false) (useGrind := true) then
          return some .positivity
      catch _ => pure ()
      return none

/-- Check whether `x ≠ 0` is a sound inverse guard for this type.
    For scalar-like types (fields, division rings, GroupWithZero), `x ≠ 0`
    correctly guards `x⁻¹`. For types where `Inv` has different semantics
    (e.g. matrix inverse needs `IsUnit`, group inverse is total), we skip
    the nonzero check to avoid false positives.
    We test: does the type have a `GroupWithZero` instance? If so, `x ≠ 0`
    is the right guard. If not, the inverse may have non-scalar semantics. -/
def supportsNeZeroInvGuard (ty : Expr) : MetaM Bool := do
  -- If the type has GroupWithZero, then x ≠ 0 ↔ IsUnit x, so nonzero is correct.
  -- This covers fields, division rings, and ℝ/ℂ/ℚ.
  try
    let _ ← synthInstance (← mkAppM ``GroupWithZero #[ty])
    return true
  catch _ =>
    -- No GroupWithZero — inv has different semantics (matrix, group, etc.)
    return false

/-- Try to prove an unsafety condition for an analytic argument.
    Builds the appropriate goal based on the operation type:
    - sqrt: x < 0 (negative input)
    - log: x ≤ 0 (non-positive input)
    - inv: x = 0 (zero input)
    Uses grind (not omega) since these are typically Real-valued. -/
def proveAnalyticUnsafe? (op : AnalyticOp) (x : Expr) (lctx : LocalContext) (insts : LocalInstances)
    : MetaM (Option String) := do
  let snap : LocalCtxSnapshot := { lctx := lctx, insts := insts }
  -- Build goal under snapshot (needs local context for typeclass resolution)
  let goal? ← withSnapshot snap do
    let ty ← inferType x
    match ← mkZeroOf ty with
    | some zero =>
      try
        let goal ← match op with
          | .sqrt => mkLT x zero              -- x < 0
          | .log  => mkLE x zero              -- x ≤ 0
          | .inv  => mkAppM ``Eq #[x, zero]   -- x = 0
          | .exp  => pure (Lean.mkConst ``True)  -- never called for exp
        pure (some goal)
      catch _ => pure none
    | none => pure none
  match goal? with
  | some goal =>
    -- Route through tryProveUnsafety? for single policy point
    -- Analytic types use grind only (omega doesn't help for Real)
    match ← tryProveUnsafety? goal snap (useOmega := false) with
    | some pb => return some pb.toString
    | none => return none
  | none => return none

/-- Check if a constant name matches known sqrt functions.
    Uses exact Name matching (not substring) for precision. -/
def isSqrtName (name : Name) : Bool :=
  match name with
  | .str (.str .anonymous "Real") "sqrt" => true
  | .str (.str .anonymous "NNReal") "sqrt" => true
  | _ => false

/-- Check if a constant name matches known log functions.
    Uses exact Name matching (not substring) for precision. -/
def isLogName (name : Name) : Bool :=
  match name with
  | .str (.str .anonymous "Real") "log" => true
  | _ => false

/-- Find analytic domain issues in an expression -/
partial def findAnalyticPatterns (e : Expr) (lctx : LocalContext) (insts : LocalInstances)
    (positive : Bool := true) : MetaM (Array AnalyticInfo) := do
  let mut results := #[]

  -- Performance: Skip non-application expressions quickly
  if !e.isApp && !e.isForall && !e.isLambda && !e.isLet then
    return #[]

  -- Check for sqrt patterns
  -- Real.sqrt has arity 1 (just the argument)
  let fn := e.getAppFn
  if let .const name _ := fn then
    if isSqrtName name then
      let args := e.getAppArgs
      if args.size >= 1 then
        let arg := args.back!
        let guard ← proveNonNeg? arg lctx insts
        if guard.isNone then
          let argStr ← ppExprSimple arg
          let unsafetyEvidence ← proveAnalyticUnsafe? .sqrt arg lctx insts
          results := results.push {
            op := .sqrt
            arg := arg
            argStr := argStr
            guardEvidence := none
            unsafetyEvidence := unsafetyEvidence
            exprHash := e.hash
          }

    -- Check for log patterns
    if isLogName name then
      let args := e.getAppArgs
      if args.size >= 1 then
        let arg := args.back!
        let guard ← provePos? arg lctx insts
        if guard.isNone then
          let argStr ← ppExprSimple arg
          let unsafetyEvidence ← proveAnalyticUnsafe? .log arg lctx insts
          results := results.push {
            op := .log
            arg := arg
            argStr := argStr
            guardEvidence := none
            unsafetyEvidence := unsafetyEvidence
            exprHash := e.hash
          }

  -- Check for Inv.inv patterns (x⁻¹)
  -- Inv.inv : {α : Type*} → [Inv α] → α → α
  -- Only check types where Zero instance exists (otherwise proveNeZero? will fail)
  if e.isAppOf `Inv.inv && e.getAppNumArgs == 3 then
    let arg := e.getAppArgs[2]!
    let argTy ← inferType arg
    -- Gate: only check types where nonzero really is the correct inverse guard.
    if ← supportsNeZeroInvGuard argTy then
      let guard ← proveNeZero? arg lctx insts
      if guard.isNone then
        let argStr ← ppExprSimple arg
        let unsafetyEvidence ← proveAnalyticUnsafe? .inv arg lctx insts
        results := results.push {
          op := .inv
          arg := arg
          argStr := argStr
          guardEvidence := none
          unsafetyEvidence := unsafetyEvidence
          exprHash := e.hash
        }
    else
      pure ()

  -- Recurse into subexpressions with proper context handling.
  -- `positive` tracks logical polarity: true = asserted, false = negated/hypothesis.
  -- The conjunction rule only fires in positive position.
  match e with
  | .forallE n ty body bi =>
    -- Type (hypothesis) is in flipped polarity; body (conclusion) keeps same
    for r in (← findAnalyticPatterns ty lctx insts (!positive)) do
      results := results.push r
    let bodyResults ← withLocalDecl n bi ty fun fvar => do
      let lctx' ← getLCtx
      let insts' ← getLocalInstances
      findAnalyticPatterns (body.instantiate1 fvar) lctx' insts' positive
    for r in bodyResults do
      results := results.push r

  | .lam n ty body bi =>
    for r in (← findAnalyticPatterns ty lctx insts positive) do
      results := results.push r
    let bodyResults ← withLocalDecl n bi ty fun fvar => do
      let lctx' ← getLCtx
      let insts' ← getLocalInstances
      findAnalyticPatterns (body.instantiate1 fvar) lctx' insts' positive
    for r in bodyResults do
      results := results.push r

  | .letE n ty val body _ =>
    for r in (← findAnalyticPatterns ty lctx insts positive) do
      results := results.push r
    for r in (← findAnalyticPatterns val lctx insts positive) do
      results := results.push r
    let bodyResults ← withLetDecl n ty val fun fvar => do
      let lctx' ← getLCtx
      let insts' ← getLocalInstances
      findAnalyticPatterns (body.instantiate1 fvar) lctx' insts' positive
    for r in bodyResults do
      results := results.push r

  | .app f a =>
    if positive && e.isAppOfArity ``And 2 then
      -- Conjunction in positive position: share sibling conjuncts as hypotheses
      let lhs := e.getAppArgs[0]!
      let rhs := e.getAppArgs[1]!

      let lhsResults ← withLCtx lctx insts do
        withLocalDeclD `_atpAnd rhs fun _ => do
          let lctx' ← getLCtx
          let insts' ← getLocalInstances
          findAnalyticPatterns lhs lctx' insts' positive
      for r in lhsResults do
        results := results.push r

      let rhsResults ← withLCtx lctx insts do
        withLocalDeclD `_atpAnd lhs fun _ => do
          let lctx' ← getLCtx
          let insts' ← getLocalInstances
          findAnalyticPatterns rhs lctx' insts' positive
      for r in rhsResults do
        results := results.push r
    else if f.isConstOf ``Not then
      -- Negation: flip polarity for the argument
      for r in (← findAnalyticPatterns a lctx insts (!positive)) do
        results := results.push r
    else
      for r in (← findAnalyticPatterns f lctx insts positive) do
        results := results.push r
      for r in (← findAnalyticPatterns a lctx insts positive) do
        results := results.push r

  | .mdata _ inner =>
    for r in (← findAnalyticPatterns inner lctx insts positive) do
      results := results.push r

  | .proj _ _ inner =>
    for r in (← findAnalyticPatterns inner lctx insts positive) do
      results := results.push r

  | _ => pure ()

  return results

/-- Result of analyzing a declaration -/
structure AnalysisResult where
  declName : Name
  issues : Array AnalyticInfo
  deriving Inhabited

/-- Deduplicate by argument string and operation type.
    When duplicates collide, the entry with stronger evidence wins.
    Uses insertion-order to guarantee deterministic output. -/
def deduplicateIssues (issues : Array AnalyticInfo) : Array AnalyticInfo :=
  let init : Std.HashMap (String × AnalyticOp) Nat × Array AnalyticInfo := ({}, #[])
  let (_, out) := issues.foldl (init := init) fun (seen, out) issue =>
    let key := (issue.argStr, issue.op)
    match seen[key]? with
    | some idx =>
      if (out[idx]!).unsafetyEvidence.isNone && issue.unsafetyEvidence.isSome then
        (seen, out.set! idx issue)
      else
        (seen, out)
    | none => (seen.insert key out.size, out.push issue)
  out

/-- Analyze a declaration for analytic domain issues -/
def analyzeDecl (declName : Name) : MetaM AnalysisResult := do
  let env ← getEnv
  let some constInfo := env.find? declName
    | throwError "Declaration {declName} not found"

  let type := constInfo.type
  let value? := constInfo.value?

  let emptyLCtx : LocalContext := {}

  let mut allIssues := #[]

  -- Analyze the type: open ALL binders first so every hypothesis is available
  -- for guard checking. Binder-type analysis uses prop-full, data-prefix
  let typeIssues ← withLCtx emptyLCtx #[] do
    forallTelescope type fun fvars body => do
      let fullLCtx ← getLCtx
      let fullInsts ← getLocalInstances
      let mut issues := #[]
      for j in [:fvars.size] do
        let fvar := fvars[j]!
        let ldecl ← fvar.fvarId!.getDecl
        let lctxForType := ← mkSafeLCtxForType fullLCtx fvars j
        for r in (← findAnalyticPatterns ldecl.type lctxForType fullInsts) do
          issues := issues.push r
      for r in (← findAnalyticPatterns body fullLCtx fullInsts) do
        issues := issues.push r
      return issues
  for r in typeIssues do
    allIssues := allIssues.push r

  -- Analyze value: open all lambda binders first for full-scope guard checking.
  -- Only analyze value for non-Prop definitions (skip proof terms).
  if let some value := value? then
    let isPropType ← isProp type
    if !isPropType then
      let valueIssues ← withLCtx emptyLCtx #[] do
        lambdaTelescope value fun fvars body => do
          let fullLCtx ← getLCtx
          let fullInsts ← getLocalInstances
          let mut issues := #[]
          for j in [:fvars.size] do
            let fvar := fvars[j]!
            let ldecl ← fvar.fvarId!.getDecl
            let lctxForType := ← mkSafeLCtxForType fullLCtx fvars j
            for r in (← findAnalyticPatterns ldecl.type lctxForType fullInsts) do
              issues := issues.push r
          for r in (← findAnalyticPatterns body fullLCtx fullInsts) do
            issues := issues.push r
          return issues
      for r in valueIssues do
        allIssues := allIssues.push r

  let dedupIssues := deduplicateIssues allIssues

  return { declName, issues := dedupIssues }

/-- Human-readable operation description used in structured finding messages. -/
def AnalyticOp.description : AnalyticOp → String
  | .sqrt => "Real.sqrt requires 0 ≤ x (returns 0 for negative input)"
  | .log => "Real.log requires 0 < x (returns 0 for non-positive input)"
  | .inv => "x⁻¹ requires x ≠ 0 (returns 0 for zero input)"
  | .exp => "Real.exp has no domain restriction"

end AtpLinter.AnalyticDomain
