/-
  TestAssertions — Shared test assertion macros for the ATP linter test suite.

  Provides `#cov_assert_*` commands that programmatically assert properties
  of linter findings for a given declaration.
-/

import AtpLinter

open Lean Elab Command Meta

namespace TestAssertions

/-- Get findings for a declaration. -/
def getFindingsFor (name : Name) : CommandElabM (Array AtpLinter.LintFinding) := do
  liftTermElabM do
    let analysis ← AtpLinter.analyzeDecl name
    AtpLinter.toFindings analysis

def findingsSummary (findings : Array AtpLinter.LintFinding) : String :=
  if findings.isEmpty then
    "(none)"
  else
    findings.toList.map (fun f =>
      let pb := match f.provedBy with
        | some v => v
        | none => "null"
      s!"{toString f.category} [{toString f.confidence}] provedBy={pb}"
    ) |> String.intercalate "; "

syntax (name := covAssertCount) "#cov_assert_count " ident num : command
syntax (name := covAssertHasCategory) "#cov_assert_has " ident str : command
syntax (name := covAssertNotCategory) "#cov_assert_not " ident str : command
syntax (name := covAssertConfidence) "#cov_assert_confidence " ident str ident : command
syntax (name := covAssertProvedBy) "#cov_assert_proved_by " ident str str : command
syntax (name := covAssertNoProvedBy) "#cov_assert_no_proved_by " ident str : command

@[command_elab covAssertCount]
def elabCovAssertCount : CommandElab := fun stx => do
  let id := stx[1]
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some expected := stx[2].isNatLit?
    | throwError "Expected number literal"
  let findings ← getFindingsFor name
  if findings.size != expected then
    throwError "Expected {expected} finding(s) for {name}, got {findings.size}. Findings: {findingsSummary findings}"

@[command_elab covAssertHasCategory]
def elabCovAssertHasCategory : CommandElab := fun stx => do
  let id := stx[1]
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some category := stx[2].isStrLit?
    | throwError "Expected string literal category"
  let findings ← getFindingsFor name
  let has := findings.any (fun f => toString f.category == category)
  if !has then
    throwError "Expected category '{category}' for {name}. Findings: {findingsSummary findings}"

@[command_elab covAssertNotCategory]
def elabCovAssertNotCategory : CommandElab := fun stx => do
  let id := stx[1]
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some category := stx[2].isStrLit?
    | throwError "Expected string literal category"
  let findings ← getFindingsFor name
  let has := findings.any (fun f => toString f.category == category)
  if has then
    throwError "Expected no '{category}' finding for {name}. Findings: {findingsSummary findings}"

private def resolveConfidence (stx : Syntax) : CommandElabM AtpLinter.Confidence := do
  let id := stx.getId
  match id with
  | .str .anonymous "proven" => return .proven
  | .str .anonymous "maybe"  => return .maybe
  | _ => throwError "Unknown confidence level '{id}'. Expected: proven, maybe"

@[command_elab covAssertConfidence]
def elabCovAssertConfidence : CommandElab := fun stx => do
  let id := stx[1]
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some category := stx[2].isStrLit?
    | throwError "Expected string literal category"
  let expected ← resolveConfidence stx[3]
  let findings ← getFindingsFor name
  let catFindings := findings.filter (fun f => toString f.category == category)
  if catFindings.isEmpty then
    throwError "No findings in category '{category}' for {name}. Findings: {findingsSummary findings}"
  let ok := catFindings.any (fun f => f.confidence == expected)
  if !ok then
    throwError "Expected confidence '{expected}' for '{category}' in {name}. Findings: {findingsSummary findings}"

@[command_elab covAssertProvedBy]
def elabCovAssertProvedBy : CommandElab := fun stx => do
  let id := stx[1]
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some category := stx[2].isStrLit?
    | throwError "Expected string literal category"
  let some expectedMethod := stx[3].isStrLit?
    | throwError "Expected string literal provedBy method"
  let findings ← getFindingsFor name
  let catFindings := findings.filter (fun f => toString f.category == category)
  if catFindings.isEmpty then
    throwError "No findings in category '{category}' for {name}. Findings: {findingsSummary findings}"
  let ok := catFindings.any (fun f => f.provedBy == some expectedMethod)
  if !ok then
    throwError "Expected provedBy '{expectedMethod}' for '{category}' in {name}. Findings: {findingsSummary findings}"

@[command_elab covAssertNoProvedBy]
def elabCovAssertNoProvedBy : CommandElab := fun stx => do
  let id := stx[1]
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some category := stx[2].isStrLit?
    | throwError "Expected string literal category"
  let findings ← getFindingsFor name
  let catFindings := findings.filter (fun f => toString f.category == category)
  if catFindings.isEmpty then
    throwError "No findings in category '{category}' for {name}. Findings: {findingsSummary findings}"
  let hasProvedBy := catFindings.any (fun f => f.provedBy.isSome)
  if hasProvedBy then
    throwError "Expected provedBy = null for '{category}' in {name}. Findings: {findingsSummary findings}"

end TestAssertions
