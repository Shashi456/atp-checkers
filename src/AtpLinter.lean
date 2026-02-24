/-
  ATP Linter - Main module

  Unified interface for detecting common Lean formalization errors:
  - Truncated Nat subtraction
  - Division by zero
  - Integer division truncation (e.g., 1/4 = 0)
  - Int.toNat truncation
  - 0-indexed List.range
  - Modulo by zero
  - User axioms (unproven statements)
  - Sorry placeholders
  - Vacuous theorems (contradictory hypotheses)
  - Unused quantified variables
  - Counterexample search (Phase 2)
  - Cast-after-truncation (Phase 2)
  - Exponent truncation (Phase 2)
  - Analytic domain totalization (Phase 5)

  Usage:
    #check_atp myTheorem  -- Run all linters on a declaration
-/

import AtpLinter.Basic
import AtpLinter.NatSubtraction
import AtpLinter.DivisionByZero
import AtpLinter.IntDivTruncation
import AtpLinter.IntToNat
import AtpLinter.ListRange
import AtpLinter.ModuloByZero
import AtpLinter.AxiomChecker
import AtpLinter.VacuousCheck
import AtpLinter.UnusedBinder
-- Phase 2 checkers
import AtpLinter.Counterexample
import AtpLinter.CastAfterTruncation
import AtpLinter.ExponentTruncation
-- Phase 5 checkers
import AtpLinter.AnalyticDomain

open Lean Elab Meta Command Term

namespace AtpLinter

/-- Combined analysis result -/
structure FullAnalysis where
  declName : Name
  natSubResult : NatSubtraction.AnalysisResult
  divResult : DivisionByZero.AnalysisResult
  intDivResult : IntDivTruncation.AnalysisResult
  intToNatResult : IntToNat.AnalysisResult
  listRangeResult : ListRange.AnalysisResult
  moduloResult : ModuloByZero.AnalysisResult
  axiomResult : AxiomChecker.AnalysisResult
  vacuousResult : VacuousCheck.AnalysisResult
  unusedBinderResult : UnusedBinder.AnalysisResult
  -- Phase 2 checkers
  counterexampleResult : Counterexample.AnalysisResult
  castTruncResult : CastAfterTruncation.AnalysisResult
  exponentResult : ExponentTruncation.AnalysisResult
  -- Phase 5 checkers
  analyticDomainResult : AnalyticDomain.AnalysisResult
  deriving Inhabited

/-- Run all linters on a declaration -/
def analyzeDecl (declName : Name) : MetaM FullAnalysis := do
  -- Phase 1 checkers
  let natSubResult ← NatSubtraction.analyzeDecl declName
  let divResult ← DivisionByZero.analyzeDecl declName
  let intDivResult ← IntDivTruncation.analyzeDecl declName
  let intToNatResult ← IntToNat.analyzeDecl declName
  let listRangeResult ← ListRange.analyzeDecl declName
  let moduloResult ← ModuloByZero.analyzeDecl declName
  let axiomResult ← AxiomChecker.analyzeDecl declName
  let vacuousResult ← VacuousCheck.analyzeDecl declName
  let unusedBinderResult ← UnusedBinder.analyzeDecl declName

  -- Phase 2 checkers (non-gated)
  let castTruncResult ← CastAfterTruncation.analyzeDecl declName
  let exponentResult ← ExponentTruncation.analyzeDecl declName

  -- Phase 5 checkers
  let analyticDomainResult ← AnalyticDomain.analyzeDecl declName

  -- Counterexample search is gated: only run if other checkers found issues
  -- or if declaration contains sorry
  let hasOtherFindings :=
    natSubResult.subtractions.any (·.guardEvidence.isNone) ||
    divResult.divisions.any (·.guardEvidence.isNone) ||
    !intDivResult.truncations.isEmpty ||
    intToNatResult.conversions.any (fun c => c.kind == .toNat && c.guardEvidence.isNone) ||
    moduloResult.modulos.any (·.guardEvidence.isNone) ||
    (axiomResult.isUserAxiom && axiomResult.isProp) ||
    vacuousResult.isVacuous ||
    !unusedBinderResult.unusedBinders.isEmpty ||
    !castTruncResult.patterns.isEmpty ||
    !exponentResult.exponents.isEmpty ||
    !analyticDomainResult.issues.isEmpty

  let counterexampleResult ← Counterexample.analyzeDecl declName hasOtherFindings

  return {
    declName := declName
    natSubResult := natSubResult
    divResult := divResult
    intDivResult := intDivResult
    intToNatResult := intToNatResult
    listRangeResult := listRangeResult
    moduloResult := moduloResult
    axiomResult := axiomResult
    vacuousResult := vacuousResult
    unusedBinderResult := unusedBinderResult
    counterexampleResult := counterexampleResult
    castTruncResult := castTruncResult
    exponentResult := exponentResult
    analyticDomainResult := analyticDomainResult
  }

/-- Convert analysis results to LintFindings -/
def toFindings (analysis : FullAnalysis) : MetaM (Array LintFinding) := do
  let mut findings := #[]

  -- Nat subtraction findings
  for sub in analysis.natSubResult.subtractions do
    if sub.guardEvidence.isNone then
      -- Use pre-computed strings captured at analysis time
      findings := findings.push {
        category := .truncatedSubtraction
        severity := .warning
        declName := analysis.declName
        message := s!"{sub.lhsStr} - {sub.rhsStr} has no guard ensuring {sub.rhsStr} ≤ {sub.lhsStr}"
        suggestion := s!"Add hypothesis `h : {sub.rhsStr} ≤ {sub.lhsStr}` or use Int instead of Nat"
        confidence := if sub.unsafetyEvidence.isSome then .proven else .maybe
        provedBy := sub.unsafetyEvidence
      }

  -- Division findings
  for div in analysis.divResult.divisions do
    -- m7 fix: Check for definitionally zero divisor first (more severe)
    if div.isDefinitelyZero then
      findings := findings.push {
        category := .divisionByZero
        severity := .error  -- Definite division by zero is an error
        declName := analysis.declName
        message := s!"{div.dividendStr} / {div.divisorStr} divides by literal zero!"
        suggestion := "This is definitely division by zero - the divisor is 0"
        confidence := .proven
        provedBy := some "definitional"
      }
    else if div.guardEvidence.isNone then
      -- Use pre-computed strings captured at analysis time
      findings := findings.push {
        category := .divisionByZero
        severity := .warning
        declName := analysis.declName
        message := s!"{div.dividendStr} / {div.divisorStr} has no guard ensuring {div.divisorStr} ≠ 0"
        suggestion := s!"Add hypothesis `h : {div.divisorStr} ≠ 0` or `h : {div.divisorStr} > 0`"
        confidence := if div.unsafetyEvidence.isSome then .proven else .maybe
        provedBy := div.unsafetyEvidence
      }

  -- Integer division truncation findings
  for trunc in analysis.intDivResult.truncations do
    -- Use pre-computed pretty-printed strings (captured at analysis time with correct binder context)
    let dividendStr := trunc.dividendStr
    let divisorStr := trunc.divisorStr
    -- M2 fix: Use correct semantics description based on division kind
    let semanticsNote := match trunc.kind with
      | .nat => "truncates toward zero"
      | .intHDiv => "truncates (Int default /)"
      | .intTdiv => "truncates toward zero (Int.tdiv)"
      | .intFdiv => "floors toward -∞ (Int.fdiv)"
      | .intEdiv => "Euclidean division (Int.ediv)"
    match trunc.status with
    | .willTruncate =>
      let detail := match trunc.dividendVal, trunc.divisorVal with
        | some a, some b =>
          let floatResult := (Float.ofInt a) / (Float.ofInt b)
          -- Dispatch on DivKind to compute the correct truncated result
          let truncResult := match trunc.kind with
            | .nat => a / b  -- Nat semantics (truncate toward zero, non-negative)
            | .intHDiv => a / b  -- Lean default Int division
            | .intTdiv => Int.tdiv a b  -- truncated toward zero
            | .intFdiv => Int.fdiv a b  -- floored toward -∞
            | .intEdiv => Int.ediv a b  -- Euclidean
          s!" ({a} / {b} = {truncResult} in integer division, but {floatResult} mathematically)"
        | _, _ => ""
      findings := findings.push {
        category := .intDivTruncation
        severity := .error
        declName := analysis.declName
        message := s!"{dividendStr} / {divisorStr} definitely truncates to wrong value{detail}"
        suggestion := "Use Real/Rat division, or restructure to avoid fractional division"
        confidence := .proven
        provedBy := some "definitional"
      }
    | .mayTruncate =>
      findings := findings.push {
        category := .intDivTruncation
        severity := .warning
        declName := analysis.declName
        message := s!"{dividendStr} / {divisorStr} may truncate ({semanticsNote})"
        suggestion := "Ensure truncation is intended, or use Real/Rat if precise division is needed"
      }
    | .noTruncate => pure () -- Should not appear, but safe to ignore

  -- Int.toNat findings (only for .toNat kind, not .natAbs which is always safe)
  for conv in analysis.intToNatResult.conversions do
    if conv.kind == .toNat && conv.guardEvidence.isNone then
      -- Use pre-computed string captured at analysis time
      findings := findings.push {
        category := .intToNat
        severity := .warning
        declName := analysis.declName
        message := s!"Int.toNat ({conv.argumentStr}) has no guard ensuring ({conv.argumentStr}) ≥ 0"
        suggestion := s!"Add hypothesis `h : {conv.argumentStr} ≥ 0` or use Int.natAbs for absolute value"
        confidence := if conv.unsafetyEvidence.isSome then .proven else .maybe
        provedBy := conv.unsafetyEvidence
      }

  -- List.range findings (informational)
  for rng in analysis.listRangeResult.ranges do
    if rng.rangeType == "List.range" || rng.rangeType == "Finset.range" then
      -- Use pre-computed string captured at analysis time
      findings := findings.push {
        category := .listRange
        severity := .info
        declName := analysis.declName
        message := s!"{rng.rangeType} {rng.argumentStr} is 0-indexed: [0, 1, ..., {rng.argumentStr}-1]"
        suggestion := "If you need [1, 2, ..., n], use List.range' 1 n or Finset.Icc 1 n"
      }

  -- Modulo findings
  for mod in analysis.moduloResult.modulos do
    if mod.guardEvidence.isNone then
      findings := findings.push {
        category := .modulo
        severity := .warning
        declName := analysis.declName
        message := s!"{mod.dividendStr} % {mod.divisorStr} has no guard ensuring {mod.divisorStr} ≠ 0"
        suggestion := s!"Add hypothesis `h : {mod.divisorStr} ≠ 0`. Note: in Lean, n % 0 = n"
        confidence := if mod.unsafetyEvidence.isSome then .proven else .maybe
        provedBy := mod.unsafetyEvidence
      }

  -- Axiom findings (only for user axioms asserting Props)
  if analysis.axiomResult.isUserAxiom && analysis.axiomResult.isProp then
    findings := findings.push {
      category := .unsoundAxiom
      severity := .error
      declName := analysis.declName
      message := "Declaration uses `axiom` instead of `theorem` - this asserts without proof"
      suggestion := "Replace with `theorem ... := by sorry` if unproven, or provide an actual proof"
      confidence := .proven
      provedBy := some "structural"
    }

  -- Vacuous theorem findings
  if analysis.vacuousResult.isVacuous then
    match analysis.vacuousResult.vacuityInfo with
    | some info =>
      match info.kind with
      | .contradictoryHyps =>
        let proofMethod := info.provedBy.toString
        let hypList := if info.relevantHyps.isEmpty then ""
          else "\n  Potentially relevant: " ++ String.intercalate ", " info.relevantHyps.toList
        findings := findings.push {
          category := .vacuousTheorem
          severity := .error
          declName := analysis.declName
          message := s!"Hypotheses are contradictory (proved by {proofMethod}){hypList}"
          suggestion := "Check inequality directions and type constraints"
          confidence := .proven
          provedBy := some info.provedBy.toString
        }
      | .emptyDomain binderName typeDesc =>
        findings := findings.push {
          category := .vacuousTheorem
          severity := .error
          declName := analysis.declName
          message := s!"Quantified over empty domain: '{binderName}' has type {typeDesc}"
          suggestion := "Check bounds - domain should likely be non-empty (e.g., Fin n with n > 0)"
          confidence := .proven
          provedBy := some info.provedBy.toString
        }
    | none => pure ()

  -- Unused binder findings
  for binder in analysis.unusedBinderResult.unusedBinders do
    -- m2 fix: Use new kind field for correct symbol
    let kindStr := match binder.kind with
      | .forall_ => "∀"
      | .lambda => "λ"
      | .exists_ => "∃"
    findings := findings.push {
      category := .unusedBinder
      severity := .warning
      declName := analysis.declName
      message := s!"{kindStr} {binder.nameStr} : {binder.typeStr} is bound but never used in body"
      suggestion := "Remove unused variable or use it in the statement"
    }

  -- Phase 2: Counterexample findings
  match analysis.counterexampleResult.counterexample with
  | some cex =>
    let assignmentStrs := cex.assignments.map fun a => s!"{a.name} := {a.valueStr}"
    let assignmentList := String.intercalate ", " assignmentStrs
    findings := findings.push {
      category := .counterexample
      severity := .error
      declName := analysis.declName
      message := s!"Counterexample found: [{assignmentList}] makes proposition false"
      suggestion := s!"The instantiated proposition `{cex.instantiatedProp}` evaluates to false"
      confidence := .proven
      provedBy := some "decide"
    }
  | none => pure ()

  -- Phase 2: Cast-after-truncation findings
  for pat in analysis.castTruncResult.patterns do
    let truncDesc := pat.truncationType.toString
    let castDesc := pat.castType.toString
    findings := findings.push {
      category := .castAfterTruncation
      severity := .warning
      declName := analysis.declName
      message := s!"{castDesc} applied after {truncDesc}: {pat.innerExprStr}"
      suggestion := "The inner operation may have already lost precision before the cast"
    }

  -- Phase 2: Exponent truncation findings
  for exp in analysis.exponentResult.exponents do
    if exp.guardEvidence.isNone then
      let issueDesc := exp.issue.toString
      findings := findings.push {
        category := .exponentTruncation
        severity := if exp.issue == .negativeExponent then .error else .warning
        declName := analysis.declName
        message := s!"{exp.baseStr} ^ {exp.exponentStr}: {issueDesc}"
        suggestion := "Ensure exponent is non-negative for Nat result, or use Int/Rat"
        confidence := if exp.issue == .negativeExponent then .proven else .maybe
        provedBy := exp.negativeEvidence.map SemanticGuards.ProvedBy.toString
      }

  -- Phase 5: Analytic domain findings
  for issue in analysis.analyticDomainResult.issues do
    let opName := match issue.op with
      | .sqrt => "sqrt"
      | .log => "log"
      | .inv => "⁻¹"
      | .exp => "exp"
    let guardDesc := match issue.op with
      | .sqrt => s!"0 ≤ {issue.argStr}"
      | .log => s!"0 < {issue.argStr}"
      | .inv => s!"{issue.argStr} ≠ 0"
      | .exp => "(no guard needed)"
    findings := findings.push {
      category := .analyticDomain
      severity := .warning
      declName := analysis.declName
      message := s!"{opName}({issue.argStr}): {issue.op.description}"
      suggestion := s!"Add guard hypothesis: {guardDesc}"
      confidence := if issue.unsafetyEvidence.isSome then .proven else .maybe
      provedBy := issue.unsafetyEvidence
    }

  return findings

/-- Generate a full report for a declaration -/
def generateFullReport (declName : Name) : MetaM String := do
  let analysis ← analyzeDecl declName
  let findings ← toFindings analysis

  if findings.isEmpty then
    return s!"✓ {declName}: No issues detected"

  let separator := "──────────────────────────────────────────────────"
  let mut report := s!"Analysis of {declName}:\n"
  report := report ++ separator ++ "\n"

  for finding in findings do
    report := report ++ finding.format ++ "\n\n"

  -- Summary
  let errors := findings.filter (·.severity == .error) |>.size
  let warnings := findings.filter (·.severity == .warning) |>.size
  let infos := findings.filter (·.severity == .info) |>.size

  report := report ++ separator ++ "\n"
  report := report ++ s!"Summary: {errors} error(s), {warnings} warning(s), {infos} info(s)\n"

  return report

/-- JSON output for programmatic use -/
structure FindingJson where
  category : String
  severity : String
  declaration : String
  message : String
  suggestion : Option String
  taxonomyCategory : String
  confidence : String
  provedBy : Option String
  deriving Repr

def LintFinding.toJson (f : LintFinding) : FindingJson := {
  category := toString f.category
  severity := toString f.severity
  declaration := f.declName.toString
  message := f.message
  suggestion := f.suggestion
  taxonomyCategory := f.category.taxonomyCategory
  confidence := toString f.confidence
  provedBy := f.provedBy
}

/-- Convert FindingJson to JSON string -/
-- m4 fix: Include taxonomyCategory in JSON output
def FindingJson.toJsonString (f : FindingJson) : String :=
  let escape (s : String) : String :=
    s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n" |>.replace "\r" "\\r" |>.replace "\t" "\\t"
  let suggestion := match f.suggestion with
    | some s => s!"\"{escape s}\""
    | none => "null"
  let provedBy := match f.provedBy with
    | some s => s!"\"{escape s}\""
    | none => "null"
  s!"\{\"category\":\"{escape f.category}\",\"severity\":\"{escape f.severity}\",\"declaration\":\"{escape f.declaration}\",\"message\":\"{escape f.message}\",\"suggestion\":{suggestion},\"taxonomyCategory\":\"{escape f.taxonomyCategory}\",\"confidence\":\"{escape f.confidence}\",\"provedBy\":{provedBy}}"

/-- Emit a finding with sentinel prefix for machine parsing -/
def emitFinding (f : LintFinding) : IO Unit := do
  let json := f.toJson.toJsonString
  IO.println s!"ATP_LINT:{json}"

/-- Emit completion sentinel -/
def emitDone (declCount : Nat) (findingCount : Nat) : IO Unit := do
  IO.println s!"ATP_DONE:\{\"declarations\":{declCount},\"findings\":{findingCount}}"

/-- Command to run the linter -/
syntax (name := checkAtp) "#check_atp " ident : command

@[command_elab checkAtp]
def elabCheckAtp : CommandElab := fun stx => do
  let id := stx[1]
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  try
    let report ← liftTermElabM <| generateFullReport name
    logInfo report
  catch e =>
    logWarning m!"Linter error on {name}: {e.toMessageData}"

/-- Check if a declaration was defined in the current module (not imported).
    A declaration is local if:
    1. It has no module index (added during current elaboration), OR
    2. Its module index corresponds to the current module name

    The second check is needed because `lake env lean` assigns module indices
    even to declarations in the current file. -/
def isLocalDecl (env : Environment) (currModuleName : Name) (declName : Name) : Bool :=
  match env.getModuleIdxFor? declName with
  | none => true  -- No module index = definitely local
  | some idx =>
    -- Check if the module at this index matches the current module
    match env.header.moduleNames[idx.toNat]? with
    | some modName => modName == currModuleName
    | none => false

/-- Check if a name is an auxiliary definition we should skip.
    Uses Lean's built-in `Name.isInternal` plus component checks for common
    auto-generated definition suffixes. -/
def isAuxiliaryDecl (name : Name) : Bool :=
  -- Name.isInternal catches names with `_` prefix in any component
  -- (e.g., `._proof_1`, `._uniq.123`, `._match_1`)
  name.isInternal ||
  -- Check specific suffixes using Name component matching
  match name with
  | .str _ s =>
    s == "rec" || s == "recOn" || s == "casesOn" ||
    s == "below" || s == "brecOn" || s == "noConfusion" ||
    s.startsWith "sizeOf" || s == "inj"
  | _ => false

/-- Get all declarations defined in the current module -/
def getLocalDecls (env : Environment) (currModuleName : Name) : Array Name :=
  -- PERFORMANCE FIX: Use foldl instead of toList to avoid intermediate allocation
  -- Only check map₂ (newly added during elaboration) - map₁ contains imported decls
  env.constants.map₂.foldl (init := #[]) fun result name _ =>
    if !isAuxiliaryDecl name && isLocalDecl env currModuleName name then
      result.push name
    else
      result

/-- Command to run the linter on ALL declarations in the current file -/
syntax (name := checkAtpAll) "#check_atp_all" : command

@[command_elab checkAtpAll]
def elabCheckAtpAll : CommandElab := fun _ => do
  let env ← getEnv
  -- Get current module name from the environment's main module
  let currModuleName := env.header.mainModule
  let decls := getLocalDecls env currModuleName

  let mut totalFindings : Nat := 0
  let mut processedDecls : Nat := 0

  for declName in decls do
    try
      let findings ← liftTermElabM do
        let analysis ← analyzeDecl declName
        toFindings analysis

      processedDecls := processedDecls + 1

      for finding in findings do
        liftCoreM <| emitFinding finding
        totalFindings := totalFindings + 1

    catch e =>
      -- Emit an infra_error finding for declarations where a checker crashes
      let errMsg ← e.toMessageData.toString
      let finding : LintFinding := {
        category := .infraError
        severity := .info
        declName := declName
        message := s!"Linter internal error: {errMsg}"
        suggestion := none
      }
      liftCoreM <| do
        -- Emit as a structured finding so the runner can count it
        let json := finding.toJson.toJsonString
        IO.println s!"ATP_LINT:{json}"
      totalFindings := totalFindings + 1

  -- Emit completion sentinel
  liftCoreM <| emitDone processedDecls totalFindings

/-- Tactic to check current goal context -/
syntax (name := checkAtpTac) "check_atp" : tactic

-- Note: Full tactic implementation would go here

end AtpLinter
