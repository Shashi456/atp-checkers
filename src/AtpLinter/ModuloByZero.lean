/-
  Modulo by Zero Detector

  Detects potentially unsafe modulo operations where:
  - `a % b` is used without a guard like `h : b ≠ 0` or `h : b > 0`

  In Lean 4:
  - For Nat: n % 0 = n (unusual - remainder equals the dividend)
  - For Int: similar behavior with different division variants

  This is mathematically unusual and can cause formalization errors.

  SOUNDNESS NOTES:
  - Uses full-scope traversal: when analyzing a binder type, ALL hypotheses
    from the declaration signature are available for guard proving, regardless
    of binder ordering. This matches the proof-state semantics where all
    hypotheses are simultaneously available.
  - Guard checking is proof-based via SemanticGuards
-/

import Lean
import Lean.Elab.Command
import Lean.Meta.Basic
import AtpLinter.Basic
import AtpLinter.SemanticGuards

open Lean Elab Meta Term
open AtpLinter.SemanticGuards
open AtpLinter (ppExprSimple)

namespace AtpLinter.ModuloByZero

/-- Check if an expression is a syntactic non-zero literal (1, 2, 3, etc.)
    Used to skip false positive warnings for modulo with literal divisors. -/
def isSyntacticNonZeroLiteral (e : Expr) : Bool :=
  match e with
  | .lit (.natVal n) => n > 0
  -- OfNat.ofNat α n inst - the literal n is in the second argument position
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ => n > 0
  | .app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n)) => n > 0
  | .app (.app (.const ``One.one _) _) _ => true
  | .app (.const ``One.one _) _ => true
  | _ => false

/-- Simple substring check -/
private def strContains (haystack : String) (needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- Check if a type is "safe" for syntactic non-zero optimization (ℕ, ℤ, ℚ, ℝ, ℂ). -/
def isSafeTypeForNonZeroLiteral (ty : Expr) : Bool :=
  match ty with
  | .const ``Nat _ => true
  | .const ``Int _ => true
  | .const ``Rat _ => true
  | .const name _ =>
    let s := name.toString
    s == "Real" || s == "Complex" || strContains s "Real" || strContains s "Rat"
  | _ => false

/-- Information about a detected modulo operation -/
structure ModInfo where
  expr : Expr
  dividend : Expr
  divisor : Expr
  divisorType : Expr
  guardEvidence : Option String := none
  unsafetyEvidence : Option String := none  -- Proof that divisor IS zero
  -- Pretty-printed strings captured at analysis time
  dividendStr : String := ""
  divisorStr : String := ""
  -- For deduplication
  exprHash : UInt64 := 0
  deriving Inhabited

/-- Check divisor guard using semantic prover -/
def checkDivisorGuard (divisor : Expr) (lctx : LocalContext) (localInsts : LocalInstances) : MetaM (Option String) := do
  let snap : LocalCtxSnapshot := { lctx := lctx, insts := localInsts }
  let result ← withSnapshot snap (proveDivisorSafe? divisor)
  match result with
  | some provedBy => return some provedBy.toString
  | none => return none

/-- Try to prove the divisor is zero (unsafety proof for modulo by zero).
    Called when safety proof (d ≠ 0) fails. If this succeeds, the finding
    upgrades from "maybe" to "proven". -/
def checkDivisorUnsafe (divisor : Expr) (divisorType : Expr) (lctx : LocalContext) (localInsts : LocalInstances) : MetaM (Option String) := do
  let snap : LocalCtxSnapshot := { lctx := lctx, insts := localInsts }
  let goal? ← withSnapshot snap do
    match ← mkZeroOf divisorType with
    | some zero =>
      try pure (some (← Lean.Meta.mkAppM ``Eq #[divisor, zero]))
      catch _ => pure none
    | none => pure none
  match goal? with
  | some goal =>
    match ← tryProveUnsafety? goal snap with
    | some pb => return some pb.toString
    | none => return none
  | none => return none

/--
Recursively find all modulo operations in an expression.

When called from `analyzeDecl`, the `lctx` parameter contains the FULL local
context (all hypotheses from the declaration signature), so guard checking sees
all available hypotheses regardless of binder order. For nested binders
encountered during recursion, the context is extended naturally.
-/
partial def findModulos (e : Expr) (lctx : LocalContext) : MetaM (Array ModInfo) := do
  let mut results := #[]
  let localInsts ← getLocalInstances

  -- Check for HMod.hMod (the modulo operator)
  -- HMod.hMod : {α β γ : Type} → [HMod α β γ] → α → β → γ
  if e.isAppOfArity ``HMod.hMod 6 then
    let args := e.getAppArgs
    let dividend := args[4]!
    let divisor := args[5]!

    let divisorType ← inferType divisor
    -- OPTIMIZATION: Skip warning for non-zero literals on safe types
    let guardEvidence ←
      if isSyntacticNonZeroLiteral divisor && isSafeTypeForNonZeroLiteral divisorType then
        pure (some "literal")
      else
        checkDivisorGuard divisor lctx localInsts
    let unsafetyEvidence ←
      if guardEvidence.isNone then
        checkDivisorUnsafe divisor divisorType lctx localInsts
      else pure none
    let dividendStr ← ppExprSimple dividend
    let divisorStr ← ppExprSimple divisor
    results := results.push {
      expr := e
      dividend := dividend
      divisor := divisor
      divisorType := divisorType
      guardEvidence := guardEvidence
      unsafetyEvidence := unsafetyEvidence
      dividendStr := dividendStr
      divisorStr := divisorStr
      exprHash := e.hash
    }

  -- Check for Nat.mod directly
  if e.isAppOfArity ``Nat.mod 2 then
    let args := e.getAppArgs
    let dividend := args[0]!
    let divisor := args[1]!

    let guardEvidence ←
      if isSyntacticNonZeroLiteral divisor then pure (some "literal")
      else checkDivisorGuard divisor lctx localInsts
    let unsafetyEvidence ←
      if guardEvidence.isNone then
        checkDivisorUnsafe divisor (mkConst ``Nat) lctx localInsts
      else pure none
    let dividendStr ← ppExprSimple dividend
    let divisorStr ← ppExprSimple divisor
    results := results.push {
      expr := e
      dividend := dividend
      divisor := divisor
      divisorType := mkConst ``Nat
      guardEvidence := guardEvidence
      unsafetyEvidence := unsafetyEvidence
      dividendStr := dividendStr
      divisorStr := divisorStr
      exprHash := e.hash
    }

  -- Check for Int.tmod (truncated toward zero)
  if e.isAppOfArity ``Int.tmod 2 then
    let args := e.getAppArgs
    let dividend := args[0]!
    let divisor := args[1]!

    let guardEvidence ←
      if isSyntacticNonZeroLiteral divisor then pure (some "literal")
      else checkDivisorGuard divisor lctx localInsts
    let unsafetyEvidence ←
      if guardEvidence.isNone then
        checkDivisorUnsafe divisor (mkConst ``Int) lctx localInsts
      else pure none
    let dividendStr ← ppExprSimple dividend
    let divisorStr ← ppExprSimple divisor
    results := results.push {
      expr := e
      dividend := dividend
      divisor := divisor
      divisorType := mkConst ``Int
      guardEvidence := guardEvidence
      unsafetyEvidence := unsafetyEvidence
      dividendStr := dividendStr
      divisorStr := divisorStr
      exprHash := e.hash
    }

  -- Check for Int.fmod (floored toward negative infinity)
  if e.isAppOfArity ``Int.fmod 2 then
    let args := e.getAppArgs
    let dividend := args[0]!
    let divisor := args[1]!

    let guardEvidence ←
      if isSyntacticNonZeroLiteral divisor then pure (some "literal")
      else checkDivisorGuard divisor lctx localInsts
    let unsafetyEvidence ←
      if guardEvidence.isNone then
        checkDivisorUnsafe divisor (mkConst ``Int) lctx localInsts
      else pure none
    let dividendStr ← ppExprSimple dividend
    let divisorStr ← ppExprSimple divisor
    results := results.push {
      expr := e
      dividend := dividend
      divisor := divisor
      divisorType := mkConst ``Int
      guardEvidence := guardEvidence
      unsafetyEvidence := unsafetyEvidence
      dividendStr := dividendStr
      divisorStr := divisorStr
      exprHash := e.hash
    }

  -- Check for Int.emod (Euclidean modulo)
  if e.isAppOfArity ``Int.emod 2 then
    let args := e.getAppArgs
    let dividend := args[0]!
    let divisor := args[1]!

    let guardEvidence ←
      if isSyntacticNonZeroLiteral divisor then pure (some "literal")
      else checkDivisorGuard divisor lctx localInsts
    let unsafetyEvidence ←
      if guardEvidence.isNone then
        checkDivisorUnsafe divisor (mkConst ``Int) lctx localInsts
      else pure none
    let dividendStr ← ppExprSimple dividend
    let divisorStr ← ppExprSimple divisor
    results := results.push {
      expr := e
      dividend := dividend
      divisor := divisor
      divisorType := mkConst ``Int
      guardEvidence := guardEvidence
      unsafetyEvidence := unsafetyEvidence
      dividendStr := dividendStr
      divisorStr := divisorStr
      exprHash := e.hash
    }

  -- Recurse into sub-expressions, extending context for nested binders
  match e with
  | .app f a =>
      results := results ++ (← findModulos f lctx)
      results := results ++ (← findModulos a lctx)

  | .lam n ty body bi =>
      results := results ++ (← findModulos ty lctx)
      let bodyResults ← withLocalDecl n bi ty fun fvar => do
        let lctx' ← getLCtx
        findModulos (body.instantiate1 fvar) lctx'
      results := results ++ bodyResults

  | .forallE n ty body bi =>
      results := results ++ (← findModulos ty lctx)
      let bodyResults ← withLocalDecl n bi ty fun fvar => do
        let lctx' ← getLCtx
        findModulos (body.instantiate1 fvar) lctx'
      results := results ++ bodyResults

  | .letE name type value body _ =>
      results := results ++ (← findModulos type lctx)
      results := results ++ (← findModulos value lctx)
      let bodyResults ← withLetDecl name type value fun fvar => do
        let lctx' ← getLCtx
        findModulos (body.instantiate1 fvar) lctx'
      results := results ++ bodyResults

  | .mdata _ inner =>
      results := results ++ (← findModulos inner lctx)

  | .proj _ _ inner =>
      results := results ++ (← findModulos inner lctx)

  | _ => pure ()

  return results

/-- Result of analyzing a declaration -/
structure AnalysisResult where
  declName : Name
  modulos : Array ModInfo
  unguardedCount : Nat
  deriving Inhabited

/-- Deduplicate modulos by semantic key (pretty-printed operands + guard status).
    Drops exprHash so semantically identical detections from different syntactic
    forms (HMod.hMod vs Nat.mod) merge correctly.
    When duplicates collide, the entry with stronger evidence wins.
    Uses insertion-order to guarantee deterministic output. -/
def deduplicateModulos (mods : Array ModInfo) : Array ModInfo :=
  let init : Std.HashMap (String × String × Bool) Nat × Array ModInfo := ({}, #[])
  let (_, out) := mods.foldl (init := init) fun (seen, out) mod =>
    let key := (mod.dividendStr, mod.divisorStr, mod.guardEvidence.isSome)
    match seen[key]? with
    | some idx =>
      if (out[idx]!).unsafetyEvidence.isNone && mod.unsafetyEvidence.isSome then
        (seen, out.set! idx mod)
      else
        (seen, out)
    | none => (seen.insert key out.size, out.push mod)
  out

/-- Analyze a declaration for modulo issues -/
def analyzeDecl (declName : Name) : MetaM AnalysisResult := do
  let env ← getEnv
  let some constInfo := env.find? declName
    | throwError "Declaration {declName} not found"

  let type := constInfo.type
  let value? := constInfo.value?

  let emptyLCtx : LocalContext := {}

  let mut allMods := #[]

  -- Analyze the type: open ALL binders first so every hypothesis is available
  -- for guard checking, regardless of binder order (full proof-state semantics).
  let typeMods ← withLCtx emptyLCtx #[] do
    forallTelescope type fun fvars body => do
      let fullLCtx ← getLCtx
      let mut mods := #[]
      for fvar in fvars do
        let ldecl ← fvar.fvarId!.getDecl
        mods := mods ++ (← findModulos ldecl.type fullLCtx)
      mods := mods ++ (← findModulos body fullLCtx)
      return mods
  allMods := allMods ++ typeMods

  -- Analyze value: open all lambda binders first for full-scope guard checking.
  -- Only analyze value for non-Prop definitions.
  if let some value := value? then
    let isPropType ← isProp type
    if !isPropType then
      let valueMods ← withLCtx emptyLCtx #[] do
        lambdaTelescope value fun fvars body => do
          let fullLCtx ← getLCtx
          let mut mods := #[]
          for fvar in fvars do
            let ldecl ← fvar.fvarId!.getDecl
            mods := mods ++ (← findModulos ldecl.type fullLCtx)
          mods := mods ++ (← findModulos body fullLCtx)
          return mods
      allMods := allMods ++ valueMods

  -- Deduplicate findings
  allMods := deduplicateModulos allMods

  let unguarded := allMods.filter (·.guardEvidence.isNone)

  return {
    declName := declName
    modulos := allMods
    unguardedCount := unguarded.size
  }

/-- Generate a report for a single declaration -/
def generateReport (result : AnalysisResult) : MetaM String := do
  if result.modulos.isEmpty then
    return s!"✓ {result.declName}: No modulo operations found"

  let mut report := s!"⚠ {result.declName}: Found {result.modulos.size} modulo operation(s)\n"

  let mut i := 0
  for mod in result.modulos do
    i := i + 1
    let typeStr ← ppExprSimple mod.divisorType
    let status := match mod.guardEvidence with
      | some ev => s!"✓ guarded ({ev})"
      | none => "✗ UNGUARDED"
    report := report ++ s!"  [{i}] {mod.dividendStr} % {mod.divisorStr} (type: {typeStr}) [{status}]\n"

  if result.unguardedCount > 0 then
    report := report ++ s!"  WARNING: {result.unguardedCount} unguarded modulo(s) - divisor could be zero (n % 0 = n)\n"

  return report

end AtpLinter.ModuloByZero
