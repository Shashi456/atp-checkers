/-
  Axiom Checker

  Detects user-defined axioms that assert theorem statements without proof.
  In autoformalization, using `axiom` to "state" a theorem means nothing
  was actually proven.

  Standard axioms (propext, funext, Quot.sound, Classical.*) are excluded.
-/

import Lean
import Lean.Util.CollectAxioms

open Lean

namespace AtpLinter.AxiomChecker

/-- Standard axioms that are part of Lean's foundations -/
def standardAxioms : List Name := [
  `propext,
  `funext,
  `Quot.sound,
  `Classical.choice,
  `Classical.em,
  `Classical.propDecidable
]

/-- Check if a name is in the Lean namespace (internal axioms) -/
def isLeanNamespace (name : Name) : Bool :=
  match name.getRoot with
  | `Lean => true
  | `Init => true
  | _ => false

/-- True for declarations coming from an imported module. -/
def isImportedDecl (env : Environment) (name : Name) : Bool :=
  (env.getModuleIdxFor? name).isSome

/-- Check if a name is a standard/allowed axiom -/
def isStandardAxiom (env : Environment) (name : Name) : Bool :=
  standardAxioms.contains name ||
  (isLeanNamespace name && isImportedDecl env name) ||
  -- Also allow specific Classical axioms
  match name with
  | .str p "choice" => p == `Classical
  | .str p "em" => p == `Classical
  | .str p "propDecidable" => p == `Classical
  | _ => false

/-- True when `name` is a non-whitelisted user axiom whose type is a Prop. -/
def isUserPropAxiom (env : Environment) (name : Name) : MetaM Bool := do
  match env.find? name with
  | some (.axiomInfo info) =>
      let isPropType ← Meta.isProp info.type
      return isPropType && !isStandardAxiom env name
  | _ => return false

/-- User Prop axioms transitively used by a declaration. -/
def userPropAxiomDependencies (env : Environment) (declName : Name) : MetaM (Array Name) := do
  let mut deps := #[]
  for name in ← Lean.collectAxioms declName do
    if ← isUserPropAxiom env name then
      if !deps.contains name then
        deps := deps.push name
  return deps

/-- Result of analyzing a declaration for axiom usage -/
structure AnalysisResult where
  declName : Name
  isAxiom : Bool
  isUserAxiom : Bool  -- axiom AND not standard
  isProp : Bool       -- type is Prop (asserting a proposition)
  depAxioms : Array Name := #[] -- user Prop axioms this declaration depends on
  deriving Inhabited

/-- Analyze a declaration for axiom usage -/
def analyzeDecl (declName : Name) : MetaM AnalysisResult := do
  let env ← getEnv
  let some constInfo := env.find? declName
    | throwError "Declaration {declName} not found"

  match constInfo with
  | .axiomInfo info =>
    -- Check if the axiom's type is a Prop
    let isPropType ← Meta.isProp info.type
    return {
      declName := declName
      isAxiom := true
      isUserAxiom := !isStandardAxiom env declName
      isProp := isPropType
      depAxioms := #[]
    }
  | _ =>
    let depAxioms ←
      match constInfo.value? with
      | some _ => userPropAxiomDependencies env declName
      | none => pure #[]
    return {
      declName := declName
      isAxiom := false
      isUserAxiom := false
      isProp := false
      depAxioms := depAxioms
    }

/-- Generate a report for a single declaration -/
def generateReport (result : AnalysisResult) : String :=
  if !result.isUserAxiom then
    s!"✓ {result.declName}: Not a user axiom"
  else if result.isProp then
    s!"✗ {result.declName}: User axiom asserting a Prop - this is unproven!"
  else
    s!"⚠ {result.declName}: User axiom (non-Prop type)"

end AtpLinter.AxiomChecker
