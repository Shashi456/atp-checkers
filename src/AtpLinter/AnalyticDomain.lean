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

/-- Pretty print an expression for reporting -/
def ppExprSimple (e : Expr) : MetaM String := do
  try
    let fmt ← ppExpr e
    return toString fmt
  catch _ =>
    return "<expr>"

/-- Known mathlib names for analytic functions (as strings for pattern matching) -/
def sqrtPatterns : List String := ["Real.sqrt", "sqrt", "Sqrt"]
def logPatterns : List String := ["Real.log", ".log"]

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

/-- Check if an expression is obviously non-negative (suppression heuristic) -/
def isObviouslyNonNeg (e : Expr) : MetaM Bool := do
  -- First check syntactic literals (fast, no whnf needed)
  if isSyntacticNonNegLiteral e then return true

  let e ← whnf e

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
    if containsSubstr nameStr "abs" then return true
    if containsSubstr nameStr "norm" then return true
    if containsSubstr nameStr "nnnorm" then return true

  return false

/-- Check if an expression is a syntactic positive literal (1, 2, 3, π, e, etc.)
    Works for both Nat literals and OfNat.ofNat patterns (2 : ℝ). -/
def isSyntacticPositiveLiteral (e : Expr) : Bool :=
  match e with
  -- Direct Nat literal > 0
  | .lit (.natVal n) => n > 0
  -- OfNat.ofNat α n inst - the literal n is in the second argument position
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ => n > 0
  | .app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n)) => n > 0
  -- One.one pattern
  | .app (.app (.const ``One.one _) _) _ => true
  | .app (.const ``One.one _) _ => true
  | _ => false

/-- Check if an expression is obviously positive (suppression heuristic) -/
def isObviouslyPos (e : Expr) : MetaM Bool := do
  -- First check syntactic positive literals (fast, no whnf needed)
  if isSyntacticPositiveLiteral e then return true

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
    if containsSubstr name.toString "exp" then return true

  return false

/-- Prove 0 ≤ x -/
def proveNonNeg? (x : Expr) (lctx : LocalContext) (insts : LocalInstances) : MetaM (Option ProvedBy) := do
  -- First check obvious cases
  if ← isObviouslyNonNeg x then
    return some .simp

  let snap : LocalCtxSnapshot := { lctx := lctx, insts := insts }
  withSnapshot snap do
    let ty ← inferType x
    match ← mkZeroOf ty with
    | none => return none
    | some zero =>
      let goal ← mkLE zero x
      -- omega won't help for Real; grind handles ordered-field reasoning
      tryProve? goal (useOmega := false) (useGrind := true)

/-- Prove 0 < x -/
def provePos? (x : Expr) (lctx : LocalContext) (insts : LocalInstances) : MetaM (Option ProvedBy) := do
  -- First check obvious cases
  if ← isObviouslyPos x then
    return some .simp

  let snap : LocalCtxSnapshot := { lctx := lctx, insts := insts }
  withSnapshot snap do
    let ty ← inferType x
    match ← mkZeroOf ty with
    | none => return none
    | some zero =>
      let goal ← mkLT zero x
      -- omega won't help for Real; grind handles ordered-field reasoning
      tryProve? goal (useOmega := false) (useGrind := true)

/-- Prove x ≠ 0 -/
def proveNeZero? (x : Expr) (lctx : LocalContext) (insts : LocalInstances) : MetaM (Option ProvedBy) := do
  let snap : LocalCtxSnapshot := { lctx := lctx, insts := insts }
  withSnapshot snap do
    let ty ← inferType x
    match ← mkZeroOf ty with
    | none => return none
    | some zero =>
      let goal ← mkAppM ``Ne #[x, zero]
      tryProve? goal (useOmega := true) (useGrind := true)

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
  | .str (.str .anonymous "Complex") "log" => true
  | _ => false

/-- Find analytic domain issues in an expression -/
partial def findAnalyticPatterns (e : Expr) (lctx : LocalContext) (insts : LocalInstances)
    : MetaM (Array AnalyticInfo) := do
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
  if e.isAppOfArity ``Inv.inv 3 then
    let arg := e.getAppArgs[2]!
    let argTy ← inferType arg
    -- Gate: only check if the type has a Zero instance (mkZeroOf succeeds)
    match ← mkZeroOf argTy with
    | some _ =>
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
    | none => pure ()  -- Type has no Zero, Inv.inv may have different semantics

  -- Recurse into subexpressions with proper context handling
  match e with
  | .forallE n ty body bi =>
    results := results ++ (← findAnalyticPatterns ty lctx insts)
    let bodyResults ← withLocalDecl n bi ty fun fvar => do
      let lctx' ← getLCtx
      let insts' ← getLocalInstances
      findAnalyticPatterns (body.instantiate1 fvar) lctx' insts'
    results := results ++ bodyResults

  | .lam n ty body bi =>
    results := results ++ (← findAnalyticPatterns ty lctx insts)
    let bodyResults ← withLocalDecl n bi ty fun fvar => do
      let lctx' ← getLCtx
      let insts' ← getLocalInstances
      findAnalyticPatterns (body.instantiate1 fvar) lctx' insts'
    results := results ++ bodyResults

  | .letE n ty val body _ =>
    results := results ++ (← findAnalyticPatterns ty lctx insts)
    results := results ++ (← findAnalyticPatterns val lctx insts)
    let bodyResults ← withLetDecl n ty val fun fvar => do
      let lctx' ← getLCtx
      let insts' ← getLocalInstances
      findAnalyticPatterns (body.instantiate1 fvar) lctx' insts'
    results := results ++ bodyResults

  | .app f a =>
    results := results ++ (← findAnalyticPatterns f lctx insts)
    results := results ++ (← findAnalyticPatterns a lctx insts)

  | .mdata _ inner =>
    results := results ++ (← findAnalyticPatterns inner lctx insts)

  | .proj _ _ inner =>
    results := results ++ (← findAnalyticPatterns inner lctx insts)

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

  -- Analyze type (statement/specification)
  let typeIssues ← withLCtx emptyLCtx #[] do
    findAnalyticPatterns type emptyLCtx #[]

  -- Only analyze value for non-Prop definitions (skip proof terms)
  let valueIssues ← match value? with
    | some v =>
      let isPropType ← isProp type
      if !isPropType then
        withLCtx emptyLCtx #[] do
          findAnalyticPatterns v emptyLCtx #[]
      else
        pure #[]
    | none => pure #[]

  let allIssues := deduplicateIssues (typeIssues ++ valueIssues)

  return { declName, issues := allIssues }

/-- Human-readable operation description -/
def AnalyticOp.description : AnalyticOp → String
  | .sqrt => "Real.sqrt requires 0 ≤ x (returns 0 for negative input)"
  | .log => "Real.log requires 0 < x (returns 0 for non-positive input)"
  | .inv => "x⁻¹ requires x ≠ 0 (returns 0 for zero input)"
  | .exp => "Real.exp has no domain restriction"

/-- Human-readable guard description -/
def AnalyticOp.guardNeeded : AnalyticOp → String
  | .sqrt => "0 ≤"
  | .log => "0 <"
  | .inv => "≠ 0:"
  | .exp => "(none)"

/-- Generate a report for a single declaration -/
def generateReport (result : AnalysisResult) : String :=
  if result.issues.isEmpty then
    s!"✓ {result.declName}: No analytic domain issues detected"
  else
    let issueLines := result.issues.toList.map fun issue =>
      let opName := match issue.op with
        | .sqrt => "sqrt"
        | .log => "log"
        | .inv => "⁻¹"
        | .exp => "exp"
      s!"  {opName}({issue.argStr}): {issue.op.description}\n"
    s!"⚠ {result.declName}: Found {result.issues.size} analytic domain issue(s)\n" ++
      String.join issueLines ++
      s!"  Suggestion: Add domain guard hypotheses or verify intended behavior\n"

end AtpLinter.AnalyticDomain
