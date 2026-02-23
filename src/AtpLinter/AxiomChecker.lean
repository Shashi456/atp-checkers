/-
  Axiom Checker

  Detects user-defined axioms that assert theorem statements without proof.
  In autoformalization, using `axiom` to "state" a theorem means nothing
  was actually proven.

  Standard axioms (propext, funext, Quot.sound, Classical.*) are excluded.
-/

import Lean

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

/-- Check if a name is a standard/allowed axiom -/
def isStandardAxiom (name : Name) : Bool :=
  standardAxioms.contains name ||
  isLeanNamespace name ||
  -- Also allow specific Classical axioms
  match name with
  | .str p "choice" => p == `Classical
  | .str p "em" => p == `Classical
  | .str p "propDecidable" => p == `Classical
  | _ => false

/-- Result of analyzing a declaration for axiom usage -/
structure AnalysisResult where
  declName : Name
  isAxiom : Bool
  isUserAxiom : Bool  -- axiom AND not standard
  isProp : Bool       -- type is Prop (asserting a proposition)
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
      isUserAxiom := !isStandardAxiom declName
      isProp := isPropType
    }
  | _ =>
    return {
      declName := declName
      isAxiom := false
      isUserAxiom := false
      isProp := false
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
