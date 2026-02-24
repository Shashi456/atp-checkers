/-
  Counterexample Search

  Attempts to find concrete counterexamples for suspicious declarations.
  Only runs when triggered by:
  - Declaration contains sorry
  - Other linters flagged the declaration
  - Declaration is in an autoformalization namespace

  Two-phase search:
  1. Exhaustive enumeration over small domains (Bool, Nat 0–4, Int ±2, Fin ≤8)
  2. Plausible random testing fallback (when exhaustive finds nothing)

  SOUNDNESS NOTES:
  - Exhaustive: uses `decide` to evaluate fully-instantiated propositions
  - Plausible: `TestResult.failure` carries a proof of `¬ p`
  - Both backends fail closed: skip if any step is uncertain

  LIMITATIONS (exhaustive):
  - Only enumerates Bool, small Nat/Int, small Fin n
  - Requires Decidable instance for the proposition
  - Skips Type/Prop/function-typed binders
  - Maximum 4 binders, 2000 total assignments
-/

import Lean
import Lean.Elab.Command
import Lean.Meta.Basic
import Plausible

open Lean Elab Meta Term

namespace AtpLinter.Counterexample

/-- Configuration for counterexample search -/
structure Config where
  maxBinders : Nat := 4
  maxAssignments : Nat := 2000
  natValues : List Nat := [0, 1, 2, 3, 4]
  intValues : List Int := [0, 1, -1, 2, -2]
  maxFinSize : Nat := 8
  deriving Inhabited

/-- How the counterexample was found -/
inductive SearchMethod where
  | exhaustive   -- Found by decide over enumerated values
  | plausible    -- Found by Plausible random sampling
  deriving Inhabited, BEq

/-- A single variable assignment -/
structure Assignment where
  name : Name
  value : Expr
  valueStr : String
  deriving Inhabited

/-- Result of finding a counterexample -/
structure CounterexampleResult where
  assignments : List Assignment
  instantiatedProp : String
  method : SearchMethod := .exhaustive
  deriving Inhabited

/-- Result of analyzing a declaration -/
structure AnalysisResult where
  declName : Name
  counterexample : Option CounterexampleResult
  wasSkipped : Bool  -- true if we didn't run (gate not triggered)
  deriving Inhabited

/-- Pretty print an expression -/
def ppExprSimple (e : Expr) : MetaM String := do
  try
    let fmt ← ppExpr e
    return toString fmt
  catch _ =>
    return "<expr>"

/-- Make an Int literal expression -/
def mkIntLitExpr (i : Int) : MetaM Expr := do
  if i >= 0 then
    -- For non-negative, use mkNumeral with Nat value
    Lean.Meta.mkNumeral (mkConst ``Int) i.toNat
  else
    -- For negative, construct -n
    let posExpr ← Lean.Meta.mkNumeral (mkConst ``Int) i.natAbs
    mkAppM ``Neg.neg #[posExpr]

/-- Make a Fin literal expression: (n : Fin k) -/
def mkFinLitExpr (n : Nat) (k : Nat) : MetaM Expr := do
  -- Fin.mk n h where h : n < k
  -- For small values, we use OfNat instance
  let finType := mkApp (mkConst ``Fin) (mkNatLit k)
  Lean.Meta.mkNumeral finType n

/-- Get enumerable values for a type, if it's enumerable -/
def getEnumerable (ty : Expr) (cfg : Config) : MetaM (Option (List Expr)) := do
  let ty ← whnf ty
  match ty with
  | .const ``Bool _ =>
    return some [mkConst ``Bool.false, mkConst ``Bool.true]
  | .const ``Nat _ =>
    let vals := cfg.natValues.map fun n => mkNatLit n
    return some vals
  | .const ``Int _ =>
    let vals ← cfg.intValues.mapM mkIntLitExpr
    return some vals
  | .app (.const ``Fin _) nExpr =>
    match nExpr.nat? with
    | some k =>
      if k ≤ cfg.maxFinSize && k > 0 then
        let vals ← (List.range k).mapM fun n => mkFinLitExpr n k
        return some vals
      else
        return none
    | none =>
      -- Also try raw literal form
      match nExpr with
      | .lit (.natVal k) =>
        if k ≤ cfg.maxFinSize && k > 0 then
          let vals ← (List.range k).mapM fun n => mkFinLitExpr n k
          return some vals
        else
          return none
      | _ => return none
  | _ => return none

/-- Check if a binder should be skipped (Type, Prop, function, typeclass) -/
def shouldSkipBinder (ty : Expr) (bi : BinderInfo) : MetaM Bool := do
  -- Skip typeclass instances
  if bi == .instImplicit then return true

  let ty ← whnf ty
  -- Skip Type/Sort
  if ty.isSort then return true
  -- Skip Prop-typed binders (proof hypotheses like h : n = 0)
  -- Use Meta.isProp to check if ty has type Prop, not if ty IS Prop
  if ← isProp ty then return true
  -- Skip function types
  if ty.isForall then return true

  return false

/-- Try to evaluate a Prop using decide -/
def tryDecide (prop : Expr) : MetaM (Option Bool) := do
  let saved ← Meta.saveState
  try
    -- Try to synthesize Decidable instance
    let decType ← mkAppM ``Decidable #[prop]
    let decInst? ← trySynthInstance decType
    match decInst? with
    | .none | .undef => return none
    | .some decInst =>
      -- Build: @decide prop decInst (explicitly apply the instance)
      let decideExpr := mkApp2 (mkConst ``decide) prop decInst
      -- Try to reduce it to a Bool literal
      let reduced ← whnf decideExpr
      match reduced with
      | .const ``Bool.true _ => return some true
      | .const ``Bool.false _ => return some false
      | _ =>
        -- Try harder with full reduction
        let fullyReduced ← reduce decideExpr
        match fullyReduced with
        | .const ``Bool.true _ => return some true
        | .const ``Bool.false _ => return some false
        | _ => return none
  catch _ =>
    return none
  finally
    saved.restore

/-- Main counterexample search using single-binder peeling.
    Uses StateT to properly track total assignments across all branches. -/
partial def searchCounterexampleM (e : Expr) (assignments : List Assignment)
    (cfg : Config) : StateT Nat MetaM (Option CounterexampleResult) := do
  let count ← get
  if count >= cfg.maxAssignments then return none
  -- Use > not >= to allow exactly maxBinders assignments
  if assignments.length > cfg.maxBinders then return none

  -- First, check if this is already a decidable proposition (before whnf)
  -- whnf can unfold GT.gt to Nat.le which loses Decidable instance
  let isPropTy ← isProp e
  if isPropTy then
    match ← tryDecide e with
    | some false =>
      -- Found counterexample!
      let propStr ← ppExprSimple e
      return some {
        assignments := assignments.reverse
        instantiatedProp := propStr
      }
    | some true => return none  -- Proposition is true, not a counterexample
    | none => pure ()  -- Continue to check for more binders

  -- Normalize to check for forall binders
  let eWhnf ← whnf e

  match eWhnf with
  | .forallE n ty body bi =>
    -- Check if we should skip this binder
    let skip ← shouldSkipBinder ty bi
    if skip then
      -- For Prop binders (hypotheses like h : n > 0), we need to check
      -- if the hypothesis is satisfiable to avoid false counterexamples.
      -- If h : n > 0 is false (e.g., n=0), the implication is vacuously true.
      let isPropTy ← isProp ty
      if isPropTy then
        -- Try to decide if the hypothesis is true
        match ← tryDecide ty with
        | some true =>
          -- Hypothesis is true, continue checking conclusion
          withLocalDecl n bi ty fun fvar => do
            searchCounterexampleM (body.instantiate1 fvar) assignments cfg
        | some false =>
          -- Hypothesis is false → implication is vacuously true, not a counterexample
          return none
        | none =>
          -- Can't decide hypothesis → can't determine if valid counterexample
          return none
      else
        -- Other non-enumerable types (Type, Sort, functions): abort
        return none
    else
      -- Try to enumerate values for this type
      match ← getEnumerable ty cfg with
      | none => return none  -- Can't enumerate, skip entire search
      | some vals =>
        for v in vals do
          let currentCount ← get
          if currentCount >= cfg.maxAssignments then break
          -- Increment counter for this assignment
          set (currentCount + 1)
          let body' := body.instantiate1 v
          let valueStr ← ppExprSimple v
          let assignment : Assignment := { name := n, value := v, valueStr := valueStr }
          let result ← searchCounterexampleM body' (assignment :: assignments) cfg
          if result.isSome then return result
        return none

  | _ =>
    -- No more binders and couldn't decide - give up
    return none

/-- Entry point that runs the StateT computation -/
def searchCounterexample (e : Expr) (cfg : Config) : MetaM (Option CounterexampleResult) := do
  let (result, _) ← searchCounterexampleM e [] cfg |>.run 0
  return result

-- ============================================================
-- Plausible Fallback
-- ============================================================

/-- Helper that runs Plausible and extracts a machine-readable result.
    Returns `none` if no counterexample found, `some (assignmentStrs, shrinkCount)` if found.
    This function is called via `evalExpr` from `tryPlausibleImpl`. -/
def runPlausibleHelper (p : Prop) [Plausible.Testable p]
    (cfg : Plausible.Configuration) : IO (Option (List String × Nat)) := do
  match ← Plausible.Testable.checkIO p cfg with
  | .success _ => return none
  | .gaveUp _ => return none
  | .failure _ xs n => return some (xs, n)

/-- Parse Plausible output lines into assignments and an optional issue description.
    Plausible emits three line formats:
    - `"var := {repr x}"` (from `addVarInfo`)
    - `"guard: {printProp p}"` (from guard checks)
    - `"issue: {s} does not hold"` (from decidable base case) -/
def parsePlausibleOutput (lines : List String) : List Assignment × Option String := Id.run do
  let mut assignments : List Assignment := []
  let mut issueProp : Option String := none
  for line in lines do
    if line.startsWith "issue: " then
      issueProp := some (line.drop 7 |>.replace " does not hold" "")
    else if line.startsWith "guard: " then
      pure ()  -- skip guard lines
    else
      match line.splitOn " := " with
      | [nameStr, valueStr] =>
        assignments := assignments ++ [{
          name := .mkSimple nameStr.trim
          value := mkStrLit valueStr  -- dummy Expr (not used downstream)
          valueStr := valueStr
        }]
      | _ => pure ()  -- skip unparseable
  (assignments, issueProp)

/-- Unsafe implementation of Plausible fallback.
    Bridges MetaM → IO using `evalExpr`, following the same pattern as
    the `plausible` tactic (Plausible/Tactic.lean:196). -/
private unsafe def tryPlausibleImpl (prop : Expr)
    : MetaM (Option (List Assignment × Option String)) := do
  -- Step 1: Decorate the proposition with NamedBinder for variable name reporting
  let decorated ← Plausible.Decorations.addDecorations prop

  -- Step 2: Try to synthesize a Testable instance
  let testableType ← mkAppM ``Plausible.Testable #[decorated]
  let inst? ← trySynthInstance testableType
  match inst? with
  | .none | .undef => return none  -- No Testable instance; gracefully skip
  | .some inst =>
    try
      -- Step 3: Build the Plausible Configuration expression
      let plausibleCfg : Plausible.Configuration := {
        numInst := 200
        maxSize := 100
        randomSeed := some 42
        quiet := true
      }
      let cfgExpr := toExpr plausibleCfg

      -- Step 4: Build the expression `runPlausibleHelper decorated plausibleCfg`
      let e ← mkAppOptM ``runPlausibleHelper #[decorated, inst, cfgExpr]

      -- Step 5: Execute via evalExpr to get an IO action
      let retType := mkApp (mkConst ``IO)
        (mkApp (mkConst ``Option [0])
          (mkApp2 (mkConst ``Prod [0, 0])
            (mkApp (mkConst ``List [0]) (mkConst ``String))
            (mkConst ``Nat)))

      let ioAction ← evalExpr (IO (Option (List String × Nat))) retType e

      -- Step 6: Run the IO action
      let result ← ioAction

      match result with
      | none => return none
      | some (strs, _) =>
        let (assignments, issueProp) := parsePlausibleOutput strs
        return some (assignments, issueProp)
    catch _ =>
      -- Any failure (timeout, missing instance, etc.) → skip
      return none

/-- Safe wrapper for the Plausible fallback.
    Uses `@[implemented_by]` to contain the `unsafe evalExpr` boundary. -/
@[implemented_by tryPlausibleImpl]
opaque tryPlausibleSafe (prop : Expr) : MetaM (Option (List Assignment × Option String)) :=
  return none

/-- Check if a declaration contains sorry -/
def containsSorry (constInfo : ConstantInfo) : Bool :=
  match constInfo.value? with
  | some v => go v
  | none => false
where
  go (e : Expr) : Bool :=
    match e with
    | .const name _ => name == ``sorryAx
    | .app f a => go f || go a
    | .lam _ ty body _ => go ty || go body
    | .forallE _ ty body _ => go ty || go body
    | .letE _ ty val body _ => go ty || go val || go body
    | .mdata _ inner => go inner
    | .proj _ _ inner => go inner
    | _ => false

/-- Check if declaration is in an autoformalization namespace -/
def isAutoformalizationDecl (name : Name) : Bool :=
  let str := name.toString
  str.startsWith "AutoFormalized." ||
  str.startsWith "AF." ||
  str.startsWith "Autoformalized."

/-- Check if counterexample search should run based on gates -/
def shouldRun (declName : Name) (constInfo : ConstantInfo) (hasOtherFindings : Bool) : Bool :=
  -- Gate 1: Contains sorry
  containsSorry constInfo ||
  -- Gate 2: Other linters flagged this declaration
  hasOtherFindings ||
  -- Gate 3: Autoformalization namespace
  isAutoformalizationDecl declName

/-- Analyze a declaration for counterexamples -/
def analyzeDecl (declName : Name) (hasOtherFindings : Bool := false)
    (cfg : Config := {}) : MetaM AnalysisResult := do
  let env ← getEnv
  let some constInfo := env.find? declName
    | throwError "Declaration {declName} not found"

  -- Check gates
  if !shouldRun declName constInfo hasOtherFindings then
    return { declName, counterexample := none, wasSkipped := true }

  let type := constInfo.type

  -- Only check Prop-valued declarations
  let isPropType ← isProp type
  if !isPropType then
    return { declName, counterexample := none, wasSkipped := true }

  -- Phase 1: Exhaustive enumeration
  let emptyLCtx : LocalContext := {}
  let exhaustiveResult ← withLCtx emptyLCtx #[] do
    searchCounterexample type cfg

  -- If exhaustive search found something, return immediately
  if exhaustiveResult.isSome then
    return {
      declName := declName
      counterexample := exhaustiveResult
      wasSkipped := false
    }

  -- Phase 2: Plausible fallback (only when exhaustive found nothing)
  let plausibleResult ← withLCtx emptyLCtx #[] do
    tryPlausibleSafe type

  match plausibleResult with
  | some (assignments, issueProp) =>
    let propStr := issueProp.getD (← withLCtx emptyLCtx #[] do ppExprSimple type)
    return {
      declName := declName
      counterexample := some {
        assignments := assignments
        instantiatedProp := propStr
        method := .plausible
      }
      wasSkipped := false
    }
  | none =>
    return {
      declName := declName
      counterexample := none
      wasSkipped := false
    }

/-- Generate a report for a single declaration -/
def generateReport (result : AnalysisResult) : String :=
  if result.wasSkipped then
    s!"○ {result.declName}: Counterexample search skipped (gate not triggered)"
  else
    match result.counterexample with
    | none =>
      s!"✓ {result.declName}: No counterexample found in search space"
    | some cex =>
      let assignmentLines := cex.assignments.map fun a =>
        s!"    {a.name} := {a.valueStr}"
      let assignmentStr := String.intercalate "\n" assignmentLines
      s!"✗ {result.declName}: COUNTEREXAMPLE FOUND\n" ++
        s!"  Assignments:\n{assignmentStr}\n" ++
        s!"  Instantiated proposition: {cex.instantiatedProp}\n" ++
        s!"  This proposition evaluates to false!\n"

end AtpLinter.Counterexample
