/-
  Modulo by Zero Detector

  Detects potentially unsafe modulo operations where:
  - `a % b` is used without a guard like `h : b ≠ 0` or `h : b > 0`

  In Lean 4:
  - For Nat: n % 0 = n (unusual - remainder equals the dividend)
  - For Int: similar behavior with different division variants

  This is mathematically unusual and can cause formalization errors.

  SOUNDNESS NOTES:
  - Uses prop-full, data-prefix binder-type analysis: when analyzing a
    binder type, all propositional hypotheses are available regardless of
    binder ordering, but later data binders are excluded to prevent
    circular derived-fact justification (see mkSafeLCtxForType).
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
open AtpLinter (ppExprSimple isSyntacticNonZeroLiteral isSafeTypeForNonZeroLiteral mkSafeLCtxForType)

namespace AtpLinter.ModuloByZero

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
  let result ← withSnapshot snap (proveDivisorSafe? divisor (useGrind := true))
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

Positive-position conjunctions share sibling facts as local hypotheses. This is
polarity-aware: conjunctions under negation or in implication antecedents do not
share guards.
-/
partial def findModulos (e : Expr) (lctx : LocalContext) (positive : Bool := true) : MetaM (Array ModInfo) := do
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
      if isSyntacticNonZeroLiteral divisor && (← isSafeTypeForNonZeroLiteral divisorType) then
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

  -- Recurse into sub-expressions, extending context for nested binders.
  -- `positive` tracks logical polarity: true = asserted, false = negated/hypothesis.
  -- The conjunction rule only fires in positive position.
  match e with
  | .app f a =>
      if positive && e.isAppOfArity ``And 2 then
        let lhs := e.getAppArgs[0]!
        let rhs := e.getAppArgs[1]!
        let lhsResults ← withLCtx lctx localInsts do
          withLocalDeclD `_atpAnd rhs fun _ => do
            let lctx' ← getLCtx
            findModulos lhs lctx' positive
        for r in lhsResults do
          results := results.push r
        let rhsResults ← withLCtx lctx localInsts do
          withLocalDeclD `_atpAnd lhs fun _ => do
            let lctx' ← getLCtx
            findModulos rhs lctx' positive
        for r in rhsResults do
          results := results.push r
      else if f.isConstOf ``Not then
        for r in (← findModulos a lctx (!positive)) do
          results := results.push r
      else
        for r in (← findModulos f lctx positive) do
          results := results.push r
        for r in (← findModulos a lctx positive) do
          results := results.push r

  | .lam n ty body bi =>
      for r in (← findModulos ty lctx positive) do
        results := results.push r
      let bodyResults ← withLocalDecl n bi ty fun fvar => do
        let lctx' ← getLCtx
        findModulos (body.instantiate1 fvar) lctx' positive
      for r in bodyResults do
        results := results.push r

  | .forallE n ty body bi =>
      for r in (← findModulos ty lctx (!positive)) do
        results := results.push r
      let bodyResults ← withLocalDecl n bi ty fun fvar => do
        let lctx' ← getLCtx
        findModulos (body.instantiate1 fvar) lctx' positive
      for r in bodyResults do
        results := results.push r

  | .letE name type value body _ =>
      for r in (← findModulos type lctx positive) do
        results := results.push r
      for r in (← findModulos value lctx positive) do
        results := results.push r
      let bodyResults ← withLetDecl name type value fun fvar => do
        let lctx' ← getLCtx
        findModulos (body.instantiate1 fvar) lctx' positive
      for r in bodyResults do
        results := results.push r

  | .mdata _ inner =>
      for r in (← findModulos inner lctx positive) do
        results := results.push r

  | .proj _ _ inner =>
      for r in (← findModulos inner lctx positive) do
        results := results.push r

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
  -- for guard checking. Binder-type analysis uses prop-full, data-prefix
  let typeMods ← withLCtx emptyLCtx #[] do
    forallTelescope type fun fvars body => do
      let fullLCtx ← getLCtx
      let mut mods := #[]
      for j in [:fvars.size] do
        let fvar := fvars[j]!
        let ldecl ← fvar.fvarId!.getDecl
        let lctxForType := ← mkSafeLCtxForType fullLCtx fvars j
        for r in (← findModulos ldecl.type lctxForType) do
          mods := mods.push r
      for r in (← findModulos body fullLCtx) do
        mods := mods.push r
      return mods
  for r in typeMods do
    allMods := allMods.push r

  -- Analyze value: open all lambda binders first for full-scope guard checking.
  -- Only analyze value for non-Prop definitions.
  if let some value := value? then
    let isPropType ← isProp type
    if !isPropType then
      let valueMods ← withLCtx emptyLCtx #[] do
        lambdaTelescope value fun fvars body => do
          let fullLCtx ← getLCtx
          let mut mods := #[]
          for j in [:fvars.size] do
            let fvar := fvars[j]!
            let ldecl ← fvar.fvarId!.getDecl
            let lctxForType := ← mkSafeLCtxForType fullLCtx fvars j
            for r in (← findModulos ldecl.type lctxForType) do
              mods := mods.push r
          for r in (← findModulos body fullLCtx) do
            mods := mods.push r
          return mods
      for r in valueMods do
        allMods := allMods.push r

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
