/-
  List.range Detector

  Detects usage of List.range which is 0-indexed.

  `List.range n` returns `[0, 1, 2, ..., n-1]` (n elements, starting at 0)

  This is a common source of off-by-one errors when formalizing problems
  that use 1-indexed sequences like "the first n positive integers" or
  "sum from 1 to n".

  Alternatives:
  - `List.range' 1 n` for [1, 2, ..., n]
  - `List.Icc 1 n` from Mathlib for [1, 2, ..., n] as a Finset
  - `Finset.range n` is also 0-indexed: {0, 1, ..., n-1}
  - `Finset.Icc 1 n` for {1, 2, ..., n}
-/

import Lean
import Lean.Elab.Command
import Lean.Meta.Basic

open Lean Elab Meta Term

namespace AtpLinter.ListRange

/-- Information about a detected List.range usage -/
structure RangeInfo where
  expr : Expr
  argument : Expr
  rangeType : String  -- "List.range", "Finset.range", etc.
  -- Pretty-printed string captured at analysis time for correct binder names
  argumentStr : String := ""
  -- For List.range', store additional args if available
  extraArgs : Array String := #[]
  deriving Inhabited

/-- Pretty print an expression for reporting, with fallback for bound variables -/
def ppExprSimple (e : Expr) : MetaM String := do
  try
    let fmt ← ppExpr e
    return toString fmt
  catch _ =>
    match e with
    | .bvar n => return s!"var{n}"
    | .fvar id =>
      try
        let ldecl ← id.getDecl
        return ldecl.userName.toString
      catch _ =>
        return "x"
    | _ => return s!"<expr>"

/-- Check if a name matches a target, handling qualified names robustly.
    Matches if the name equals the target, or ends with the target after a dot.
    For example, `Mathlib.Data.Finset.range` would match target `Finset.range`. -/
def nameMatches (name : Name) (target : String) : Bool :=
  let nameStr := name.toString
  nameStr == target || nameStr.endsWith ("." ++ target)

/-- Recursively find all range usages in an expression using telescope-based traversal -/
partial def findRanges (e : Expr) : MetaM (Array RangeInfo) := do
  let mut results := #[]

  -- Check for List.range
  if e.isAppOfArity ``List.range 1 then
    let args := e.getAppArgs
    let argument := args[0]!
    let argumentStr ← ppExprSimple argument
    results := results.push {
      expr := e
      argument := argument
      rangeType := "List.range"
      argumentStr := argumentStr
    }

  -- Check for List.range' (this is the "safer" 1-indexed version when used correctly)
  -- List.range' start len step (step defaults to 1)
  -- We flag it too for review
  if e.isAppOf ``List.range' then
    let args := e.getAppArgs
    if args.size >= 1 then
      let start := args[0]!
      let startStr ← ppExprSimple start
      -- Collect all args for more informative reporting
      let mut extraArgs := #[]
      if args.size >= 2 then
        extraArgs := extraArgs.push (← ppExprSimple args[1]!)  -- len
      if args.size >= 3 then
        extraArgs := extraArgs.push (← ppExprSimple args[2]!)  -- step
      results := results.push {
        expr := e
        argument := start
        rangeType := "List.range'"
        argumentStr := startStr
        extraArgs := extraArgs
      }

  -- Check for Finset.range (0-indexed like List.range)
  -- Use nameMatches for robustness with qualified names from Mathlib
  if let some name := e.getAppFn.constName? then
    if nameMatches name "Finset.range" then
      let args := e.getAppArgs
      if args.size >= 1 then
        let argumentStr ← ppExprSimple args[0]!
        results := results.push {
          expr := e
          argument := args[0]!
          rangeType := "Finset.range"
          argumentStr := argumentStr
        }

    -- Check for common Mathlib interval functions by name
    -- Use nameMatches for robustness with different Mathlib namespace structures
    let intervalType :=
      if nameMatches name "Finset.Icc" then some "Finset.Icc"
      else if nameMatches name "Finset.Ico" then some "Finset.Ico"
      else if nameMatches name "Finset.Ioc" then some "Finset.Ioc"
      else if nameMatches name "Finset.Ioo" then some "Finset.Ioo"
      else none
    if let some intervalName := intervalType then
      let args := e.getAppArgs
      if args.size >= 2 then
        let lowerStr ← ppExprSimple args[0]!
        let upperStr ← ppExprSimple args[1]!
        results := results.push {
          expr := e
          argument := args[0]!  -- lower bound
          rangeType := intervalName
          argumentStr := lowerStr
          extraArgs := #[upperStr]
        }

  -- Recurse with proper binder handling
  match e with
  | .app f a =>
      results := results ++ (← findRanges f)
      results := results ++ (← findRanges a)

  | .lam .. =>
      -- Use lambdaTelescope to open ALL consecutive binders at once
      let bodyResults ← lambdaTelescope e fun xs innerBody => do
        let mut allResults := #[]
        -- Visit types of ALL introduced binders (not just the first!)
        for x in xs do
          let ldecl ← x.fvarId!.getDecl
          allResults := allResults ++ (← findRanges ldecl.type)
        -- Visit the body
        allResults := allResults ++ (← findRanges innerBody)
        pure allResults
      results := results ++ bodyResults

  | .forallE .. =>
      -- Use forallTelescope to open ALL consecutive binders at once
      let bodyResults ← forallTelescope e fun xs innerBody => do
        let mut allResults := #[]
        -- Visit types of ALL introduced binders (not just the first!)
        for x in xs do
          let ldecl ← x.fvarId!.getDecl
          allResults := allResults ++ (← findRanges ldecl.type)
        -- Visit the body
        allResults := allResults ++ (← findRanges innerBody)
        pure allResults
      results := results ++ bodyResults

  | .letE name type value body _ =>
      results := results ++ (← findRanges type)
      results := results ++ (← findRanges value)
      let bodyResults ← withLetDecl name type value fun fvar => do
        findRanges (body.instantiate1 fvar)
      results := results ++ bodyResults

  | .mdata _ inner =>
      results := results ++ (← findRanges inner)

  | .proj _ _ inner =>
      results := results ++ (← findRanges inner)

  | _ => pure ()

  return results

/-- Result of analyzing a declaration -/
structure AnalysisResult where
  declName : Name
  ranges : Array RangeInfo
  zeroIndexedCount : Nat  -- List.range and Finset.range
  deriving Inhabited

/-- Analyze a declaration for range usage -/
def analyzeDecl (declName : Name) : MetaM AnalysisResult := do
  let env ← getEnv
  let some constInfo := env.find? declName
    | throwError "Declaration {declName} not found"

  let type := constInfo.type
  let value? := constInfo.value?

  let mut allRanges := #[]

  -- Always analyze the type (statement/specification)
  let typeRanges ← findRanges type
  allRanges := allRanges ++ typeRanges

  -- Only analyze value for non-Prop definitions (skip proof terms)
  -- Proof terms can be enormous and contain incidental operations
  if let some value := value? then
    let isPropType ← isProp type
    if !isPropType then
      let valueRanges ← findRanges value
      allRanges := allRanges ++ valueRanges

  -- Count 0-indexed ranges
  let zeroIndexed := allRanges.filter fun r =>
    r.rangeType == "List.range" || r.rangeType == "Finset.range"

  return {
    declName := declName
    ranges := allRanges
    zeroIndexedCount := zeroIndexed.size
  }

/-- Generate a report for a single declaration -/
def generateReport (result : AnalysisResult) : MetaM String := do
  if result.ranges.isEmpty then
    return s!"✓ {result.declName}: No range functions found"

  let mut report := s!"ℹ {result.declName}: Found {result.ranges.size} range function(s)\n"

  let mut i := 0
  for rng in result.ranges do
    i := i + 1
    -- Use pre-computed string captured at analysis time
    let warning := if rng.rangeType == "List.range" || rng.rangeType == "Finset.range"
      then " ← 0-indexed!"
      else ""
    -- Format args: show all args for range'/interval functions
    let argsStr := if rng.extraArgs.isEmpty then
      rng.argumentStr
    else
      rng.argumentStr ++ ", " ++ ", ".intercalate rng.extraArgs.toList
    report := report ++ s!"  [{i}] {rng.rangeType} ({argsStr}){warning}\n"

  if result.zeroIndexedCount > 0 then
    report := report ++ s!"  NOTE: {result.zeroIndexedCount} use(s) of 0-indexed range.\n"
    report := report ++ s!"         Verify this matches the problem (e.g., 'first n positive integers' needs 1..n, not 0..n-1)\n"

  return report

end AtpLinter.ListRange
