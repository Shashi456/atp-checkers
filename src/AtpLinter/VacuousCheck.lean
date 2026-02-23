/-
  Vacuous Theorem Detector

  Detects theorems that are vacuously true due to:
  1. Contradictory hypotheses:
     - `n < 0` for `n : Nat`
     - Inconsistent bounds: `a < b` and `b ≤ a`
  2. Empty domain quantification:
     - `∀ x : Fin 0, P x` (Fin 0 is empty)
     - `∀ x : Empty, P x`
     - `∀ x : { n : Nat // n < 0 }, P x` (impossible subtype)

  SOUNDNESS NOTES:
  - Uses forallTelescope to collect ALL hypotheses (correct for vacuity check)
  - Attempts to prove False using omega/simp
  - Checks binder types for emptiness (Fin 0, Empty, impossible subtypes)
  - Only reports when contradiction/emptiness is provable (no false positives)

  LIMITATIONS:
  - omega only works on Nat/Int linear arithmetic
  - Non-linear contradictions may be missed
  - Complex subtype predicates may not be detected as empty
-/

import Lean
import Lean.Elab.Command
import Lean.Meta.Basic
import AtpLinter.SemanticGuards

open Lean Elab Meta Term
open AtpLinter.SemanticGuards

namespace AtpLinter.VacuousCheck

/-- Kind of vacuity detected -/
inductive VacuityKind where
  | contradictoryHyps                                      -- Hypotheses prove False
  | emptyDomain (binderName : Name) (typeDesc : String)    -- Binder type is empty
  deriving Inhabited

/-- Information about detected vacuity -/
structure VacuityInfo where
  kind : VacuityKind
  provedBy : ProvedBy
  relevantHyps : Array String  -- Names/descriptions of hypotheses that might be relevant
  deriving Inhabited

/-- Result of analyzing a declaration -/
structure AnalysisResult where
  declName : Name
  isVacuous : Bool
  vacuityInfo : Option VacuityInfo
  deriving Inhabited

/-- Extract hypothesis descriptions for reporting -/
def getRelevantHypDescriptions (fvars : Array Expr) : MetaM (Array String) := do
  let mut result := #[]
  for fvar in fvars do
    let ldecl ← fvar.fvarId!.getDecl
    let ty := ldecl.type
    -- Check if this is a comparison/equality type (likely relevant to contradiction)
    let isProp ← isProp ty
    if isProp then
      let tyStr ← ppExpr ty
      let name := ldecl.userName.toString
      result := result.push s!"{name} : {tyStr}"
  -- Limit to first 6 hypotheses
  return result.toSubarray 0 (min result.size 6) |>.toArray

/-- Check if an expression is definitionally equal to zero -/
def isDefEqZero (e : Expr) : MetaM Bool := do
  let e ← whnf e
  -- Check for Nat literal 0
  match e.nat? with
  | some 0 => return true
  | some _ => return false
  | none =>
    -- Check for OfNat.ofNat pattern with 0
    match e with
    | .lit (.natVal 0) => return true
    | .app (.app (.const ``OfNat.ofNat _) _) nExpr =>
      match nExpr.nat? with
      | some 0 => return true
      | _ => return false
    | _ => return false

/-- Check if a type is provably empty. Returns reason string if empty. -/
def checkDomainEmpty? (ty : Expr) : MetaM (Option String) := do
  let ty ← whnf ty

  -- Empty / PEmpty types
  if ty.isConstOf ``Empty then
    return some "Empty type"
  if ty.isConstOf ``PEmpty then
    return some "PEmpty type"

  -- Fin n where n = 0
  if ty.isAppOfArity ``Fin 1 then
    let n := ty.getAppArgs[0]!
    if ← isDefEqZero n then
      return some "Fin 0 has no elements"

  -- Subtype { x // p x } - check if predicate is never satisfiable
  -- We check for common patterns like { n : Nat // n < 0 }
  if ty.isAppOfArity ``Subtype 2 then
    let baseTy := ty.getAppArgs[0]!
    let pred := ty.getAppArgs[1]!

    -- pred is typically a lambda: fun x => condition
    match pred with
    | .lam _ _ body _ =>
      -- For Nat base type, try to prove the condition is always false using omega
      let baseTy ← whnf baseTy
      if baseTy.isConstOf ``Nat || baseTy.isConstOf ``Int then
        -- Create goal: ∀ x, ¬ body
        -- We test with a fresh variable and try to prove ¬body
        let result ← withLocalDeclD `_x baseTy fun x => do
          let instantiated := body.instantiate1 x
          let negGoal ← mkAppM ``Not #[instantiated]
          tryProve? negGoal (useOmega := true) (useGrind := true)
        if result.isSome then
          return some "subtype predicate is never satisfied"
    | _ => pure ()

  return none

/-- Check if hypotheses are contradictory OR any binder domain is empty -/
def checkVacuous (declType : Expr) : MetaM (Option VacuityInfo) := do
  let saved ← Meta.saveState
  try
    -- Open all binders to get hypotheses in local context
    forallTelescope declType fun fvars _ => do
      -- First: Check each binder type for emptiness
      for fvar in fvars do
        let ldecl ← fvar.fvarId!.getDecl
        let ty := ldecl.type
        match ← checkDomainEmpty? ty with
        | some reason =>
          let typeStr ← ppExpr ty
          return some {
            kind := .emptyDomain ldecl.userName s!"{typeStr} ({reason})"
            provedBy := .simp  -- Empty domain is a type-level fact
            relevantHyps := #[]
          }
        | none => pure ()

      -- Second: Try to prove False from the hypotheses (omega then grind)
      let falseExpr := Lean.mkConst ``False
      let result ← tryProveVacuity? falseExpr
      match result with
      | some provedBy =>
        -- Extract relevant hypothesis descriptions
        let relevantHyps ← getRelevantHypDescriptions fvars
        return some { kind := .contradictoryHyps, provedBy, relevantHyps }
      | none =>
        return none
  catch _ =>
    return none
  finally
    saved.restore

/-- Analyze a declaration for vacuous hypotheses -/
def analyzeDecl (declName : Name) : MetaM AnalysisResult := do
  let env ← getEnv
  let some constInfo := env.find? declName
    | throwError "Declaration {declName} not found"

  let type := constInfo.type

  -- Only check Prop-valued declarations (theorems)
  let isPropType ← isProp type
  if !isPropType then
    return { declName, isVacuous := false, vacuityInfo := none }

  -- Check if hypotheses are contradictory
  let vacuityInfo ← checkVacuous type

  return {
    declName := declName
    isVacuous := vacuityInfo.isSome
    vacuityInfo := vacuityInfo
  }

/-- Generate a report for a single declaration -/
def generateReport (result : AnalysisResult) : String :=
  if !result.isVacuous then
    s!"✓ {result.declName}: Not vacuous"
  else
    match result.vacuityInfo with
    | none => s!"✓ {result.declName}: Not vacuous"
    | some info =>
      match info.kind with
      | .contradictoryHyps =>
        let proofMethod := info.provedBy.toString
        let hypSection := if info.relevantHyps.isEmpty then ""
          else "  Potentially relevant hypotheses:\n" ++
            String.join (info.relevantHyps.toList.map (fun h => s!"    {h}\n"))
        s!"✗ {result.declName}: VACUOUS THEOREM\n" ++
          s!"  Hypotheses are contradictory (proved by {proofMethod})\n" ++
          hypSection ++
          s!"  The theorem is trivially true for the wrong reason\n"
      | .emptyDomain binderName typeDesc =>
        s!"✗ {result.declName}: VACUOUS THEOREM (empty domain)\n" ++
          s!"  Quantified variable '{binderName}' has empty type: {typeDesc}\n" ++
          s!"  The theorem is trivially true because no such value exists\n" ++
          s!"  Suggestion: Check bounds - domain should likely be non-empty\n"

end AtpLinter.VacuousCheck
