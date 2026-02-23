/-
  Cast-after-Truncation Detector

  Detects patterns where a truncating operation is performed and then
  the result is cast, which compounds the data loss:
  - (a / b).toNat - division already truncated, then coerced
  - (a - b).toNat - subtraction may have clamped to 0
  - Int.toNat (a / b) - same pattern, different syntax

  SOUNDNESS NOTES:
  - Pattern-based detection (may miss aliased operations)
  - Only flags clear truncation-then-cast patterns
  - Semantic analysis would require dataflow tracking

  LIMITATIONS:
  - Doesn't track values through let bindings
  - Doesn't detect truncation hidden behind function calls
-/

import Lean
import Lean.Elab.Command
import Lean.Meta.Basic

open Lean Elab Meta Term

namespace AtpLinter.CastAfterTruncation

/-- Type of truncation that occurred -/
inductive TruncationType where
  | intDiv        -- Integer division (a / b)
  | natSub        -- Natural subtraction (a - b)
  | intMod        -- Integer modulo
  deriving Inhabited, Repr, BEq, Hashable

/-- Type of cast that occurred -/
inductive CastType where
  | intToNat      -- Int.toNat or ↑ to Nat
  | natToFin      -- Nat to Fin n
  deriving Inhabited, Repr, BEq, Hashable

/-- Information about a detected cast-after-truncation -/
structure CastTruncInfo where
  truncationType : TruncationType
  castType : CastType
  innerExpr : Expr
  -- Pretty-printed strings
  innerExprStr : String := ""
  deriving Inhabited

/-- Pretty print an expression for reporting -/
def ppExprSimple (e : Expr) : MetaM String := do
  try
    let fmt ← ppExpr e
    return toString fmt
  catch _ =>
    return "<expr>"

/-- Check if an expression is integer or natural division (not Rat/Real/etc.) -/
-- HDiv.hDiv has 6 args: α β γ inst dividend divisor
-- P1 fix: Check type to avoid matching Rat/Real division
def isIntOrNatDiv (e : Expr) : MetaM Bool := do
  if e.isAppOfArity ``HDiv.hDiv 6 then
    let args := e.getAppArgs
    let ty ← whnf args[0]!
    return ty.isConstOf ``Int || ty.isConstOf ``Nat
  else
    return e.isAppOfArity ``Int.ediv 2 ||
           e.isAppOfArity ``Int.fdiv 2 ||
           e.isAppOfArity ``Int.tdiv 2

/-- Check if an expression is natural subtraction -/
-- HSub.hSub has 6 args: α β γ inst a b
def isNatSub (e : Expr) : MetaM Bool := do
  if e.isAppOfArity ``HSub.hSub 6 then
    let args := e.getAppArgs
    let tyExpr := args[0]!
    let ty ← whnf tyExpr
    return ty.isConstOf ``Nat
  else if e.isAppOfArity ``Nat.sub 2 then
    return true
  else
    return false

/-- Check if an expression is integer modulo -/
-- HMod.hMod has 6 args: α β γ inst a b
def isIntMod (e : Expr) : Bool :=
  e.isAppOfArity ``HMod.hMod 6 ||
  e.isAppOfArity ``Int.emod 2 ||
  e.isAppOfArity ``Int.fmod 2 ||
  e.isAppOfArity ``Int.tmod 2

/-- Detect truncation type in an expression -/
def detectTruncation (e : Expr) : MetaM (Option TruncationType) := do
  if ← isIntOrNatDiv e then return some .intDiv
  if ← isNatSub e then return some .natSub
  if isIntMod e then return some .intMod
  return none

/-- Check if expression is Int.toNat application -/
def isIntToNat (e : Expr) : Option Expr :=
  match e with
  | .app (.const ``Int.toNat _) arg => some arg
  | _ => none

/-- Check if expression is a Nat-to-Fin coercion -/
def isNatToFin (e : Expr) : MetaM (Option Expr) := do
  -- Pattern: Fin.ofNat n, or OfNat.ofNat with Fin type
  match e with
  | .app (.app (.const ``Fin.ofNat _) _) arg => return some arg
  | .app (.app (.app (.const ``OfNat.ofNat _) tyExpr) arg) _ =>
    let ty ← whnf tyExpr
    match ty with
    | .app (.const ``Fin _) _ => return some arg
    | _ => return none
  | _ => return none

/-- Recursively find cast-after-truncation patterns -/
partial def findCastTruncPatterns (e : Expr) : MetaM (Array CastTruncInfo) := do
  let mut results := #[]

  -- Check for Int.toNat pattern
  -- Note: Do NOT call whnf on arg - it unfolds HDiv.hDiv to implementation details
  match isIntToNat e with
  | some arg =>
    match ← detectTruncation arg with
    | some truncType =>
      let innerStr ← ppExprSimple arg
      results := results.push {
        truncationType := truncType
        castType := .intToNat
        innerExpr := arg
        innerExprStr := innerStr
      }
    | none => pure ()
  | none => pure ()

  -- Check for Nat-to-Fin pattern
  -- Note: Do NOT call whnf on arg - it unfolds HSub.hSub to implementation details
  match ← isNatToFin e with
  | some arg =>
    -- Check if arg involves Nat subtraction
    if ← isNatSub arg then
      let innerStr ← ppExprSimple arg
      results := results.push {
        truncationType := .natSub
        castType := .natToFin
        innerExpr := arg
        innerExprStr := innerStr
      }
  | none => pure ()

  -- Recurse into subexpressions with proper binder handling
  match e with
  | .app f a =>
    results := results ++ (← findCastTruncPatterns f)
    results := results ++ (← findCastTruncPatterns a)
  | .lam n ty body bi =>
    results := results ++ (← findCastTruncPatterns ty)
    -- Properly introduce binder before recursing into body
    let bodyResults ← withLocalDecl n bi ty fun fvar => do
      findCastTruncPatterns (body.instantiate1 fvar)
    results := results ++ bodyResults
  | .forallE n ty body bi =>
    results := results ++ (← findCastTruncPatterns ty)
    let bodyResults ← withLocalDecl n bi ty fun fvar => do
      findCastTruncPatterns (body.instantiate1 fvar)
    results := results ++ bodyResults
  | .letE n ty val body _ =>
    results := results ++ (← findCastTruncPatterns ty)
    results := results ++ (← findCastTruncPatterns val)
    let bodyResults ← withLetDecl n ty val fun fvar => do
      findCastTruncPatterns (body.instantiate1 fvar)
    results := results ++ bodyResults
  | .mdata _ inner =>
    results := results ++ (← findCastTruncPatterns inner)
  | .proj _ _ inner =>
    results := results ++ (← findCastTruncPatterns inner)
  | _ => pure ()

  return results

/-- Result of analyzing a declaration -/
structure AnalysisResult where
  declName : Name
  patterns : Array CastTruncInfo
  deriving Inhabited

/-- Deduplicate by inner expression string and types -/
-- R1 fix: Include truncation and cast types in key
def deduplicatePatterns (patterns : Array CastTruncInfo) : Array CastTruncInfo :=
  let seen : Std.HashSet (String × TruncationType × CastType) := {}
  patterns.foldl (init := (seen, #[])) (fun (seen, acc) pat =>
    let key := (pat.innerExprStr, pat.truncationType, pat.castType)
    if seen.contains key then
      (seen, acc)
    else
      (seen.insert key, acc.push pat)
  ) |>.2

/-- Analyze a declaration for cast-after-truncation patterns -/
def analyzeDecl (declName : Name) : MetaM AnalysisResult := do
  let env ← getEnv
  let some constInfo := env.find? declName
    | throwError "Declaration {declName} not found"

  let type := constInfo.type
  let value? := constInfo.value?

  -- Analyze type (statement/specification)
  let emptyLCtx : LocalContext := {}
  let typePatterns ← withLCtx emptyLCtx #[] (findCastTruncPatterns type)

  -- Only analyze value for non-Prop definitions (skip proof terms)
  -- Proof terms can be enormous and contain incidental operations
  let valuePatterns ← match value? with
    | some v =>
      let isPropType ← isProp type
      if !isPropType then
        withLCtx emptyLCtx #[] (findCastTruncPatterns v)
      else
        pure #[]
    | none => pure #[]

  let allPatterns := deduplicatePatterns (typePatterns ++ valuePatterns)

  return {
    declName := declName
    patterns := allPatterns
  }

/-- Human-readable truncation type -/
def TruncationType.toString : TruncationType → String
  | .intDiv => "integer division"
  | .natSub => "natural subtraction"
  | .intMod => "integer modulo"

/-- Human-readable cast type -/
def CastType.toString : CastType → String
  | .intToNat => "Int.toNat"
  | .natToFin => "Nat to Fin"

/-- Generate a report for a single declaration -/
def generateReport (result : AnalysisResult) : String :=
  if result.patterns.isEmpty then
    s!"✓ {result.declName}: No cast-after-truncation patterns detected"
  else
    let patternLines := result.patterns.toList.map fun pat =>
      s!"  {pat.castType.toString} applied to {pat.truncationType.toString}: {pat.innerExprStr}\n"
    s!"⚠ {result.declName}: Found {result.patterns.size} cast-after-truncation pattern(s)\n" ++
      String.join patternLines ++
      s!"  Suggestion: The inner operation may have already lost precision\n"

end AtpLinter.CastAfterTruncation
