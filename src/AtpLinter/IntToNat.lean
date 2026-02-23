/-
  Int.toNat Detector

  Detects usage of Int.toNat which truncates negative integers to 0.

  `Int.toNat : Int → Nat` returns:
  - n if the input is non-negative (Int.ofNat n)
  - 0 if the input is negative

  This can silently corrupt values when converting from Int to Nat
  without checking that the Int is non-negative.

  SOUNDNESS NOTES:
  - Uses prefix-context traversal: when analyzing a binder type, only
    hypotheses that are actually in scope at that point are available
  - Int.natAbs is reported separately (not as "guarded") since it has
    different semantics (absolute value, not truncation)
-/

import Lean
import Lean.Elab.Command
import Lean.Meta.Basic
import AtpLinter.SemanticGuards

open Lean Elab Meta Term
open AtpLinter.SemanticGuards

namespace AtpLinter.IntToNat

/-- Kind of Int-to-Nat conversion -/
inductive ConversionKind where
  | toNat   -- Int.toNat: truncates negatives to 0
  | natAbs  -- Int.natAbs: takes absolute value
  deriving Inhabited, Repr, BEq

/-- Information about a detected Int-to-Nat conversion -/
structure ToNatInfo where
  expr : Expr
  argument : Expr
  kind : ConversionKind
  guardEvidence : Option String := none
  unsafetyEvidence : Option String := none  -- Proof that argument < 0 (truncation occurs)
  -- Pretty-printed string captured at analysis time for correct binder names
  argumentStr : String := ""
  -- For deduplication
  exprHash : UInt64 := 0
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

/-- Check Int.toNat guard using semantic prover -/
def checkIntToNatGuard (intExpr : Expr) (lctx : LocalContext) (localInsts : LocalInstances) : MetaM (Option String) := do
  let snap : LocalCtxSnapshot := { lctx := lctx, insts := localInsts }
  let result ← withSnapshot snap (proveIntNonneg? intExpr)
  match result with
  | some provedBy => return some provedBy.toString
  | none => return none

/-- Try to prove argument < 0 (unsafety proof for Int.toNat).
    Called when safety proof (0 ≤ x) fails. If this succeeds, the finding
    upgrades from "maybe" to "proven". -/
def checkIntToNatUnsafe (intExpr : Expr) (lctx : LocalContext) (localInsts : LocalInstances) : MetaM (Option String) := do
  let snap : LocalCtxSnapshot := { lctx := lctx, insts := localInsts }
  let goal? ← withSnapshot snap do
    try
      let zero := Lean.mkIntLit 0
      pure (some (← Lean.Meta.mkLt intExpr zero))
    catch _ => pure none
  match goal? with
  | some goal =>
    match ← tryProveUnsafety? goal snap with
    | some pb => return some pb.toString
    | none => return none
  | none => return none

/--
Recursively find all Int.toNat usages in an expression using PREFIX-CONTEXT traversal.

CRITICAL: For soundness, when analyzing a binder type, we must only have
hypotheses in scope that actually precede that binder. This means we use
single-binder recursion, NOT telescope-based traversal.
-/
partial def findIntToNat (e : Expr) (lctx : LocalContext) : MetaM (Array ToNatInfo) := do
  let mut results := #[]
  let localInsts ← getLocalInstances

  -- Check for Int.toNat
  if e.isAppOfArity ``Int.toNat 1 then
    let args := e.getAppArgs
    let argument := args[0]!
    -- Use semantic guard checking
    let guardEvidence ← checkIntToNatGuard argument lctx localInsts
    let unsafetyEvidence ←
      if guardEvidence.isNone then
        checkIntToNatUnsafe argument lctx localInsts
      else pure none
    -- Capture pretty-printed string NOW while in correct context
    let argumentStr ← ppExprSimple argument
    results := results.push {
      expr := e
      argument := argument
      kind := .toNat
      guardEvidence := guardEvidence
      unsafetyEvidence := unsafetyEvidence
      argumentStr := argumentStr
      exprHash := e.hash
    }

  -- Also check for natAbs which has similar issues
  -- (though natAbs returns |n| rather than max(n,0))
  -- NOTE: We report natAbs separately, NOT as "guarded", because it has
  -- different semantics. Users should review if absolute value is intended.
  if e.isAppOfArity ``Int.natAbs 1 then
    let args := e.getAppArgs
    let argument := args[0]!
    let argumentStr ← ppExprSimple argument
    results := results.push {
      expr := e
      argument := argument
      kind := .natAbs
      guardEvidence := none  -- Not "guarded" - flagged for review
      argumentStr := argumentStr
      exprHash := e.hash
    }

  -- Recurse with PREFIX-CONTEXT correct binder handling
  -- Key: visit binder type BEFORE introducing later binders
  match e with
  | .app f a =>
      results := results ++ (← findIntToNat f lctx)
      results := results ++ (← findIntToNat a lctx)

  | .lam n ty body bi =>
      -- Visit binder type in CURRENT context (before introducing this binder)
      results := results ++ (← findIntToNat ty lctx)
      -- Then introduce the binder and recurse into body
      let bodyResults ← withLocalDecl n bi ty fun fvar => do
        let lctx' ← getLCtx
        findIntToNat (body.instantiate1 fvar) lctx'
      results := results ++ bodyResults

  | .forallE n ty body bi =>
      -- Visit binder type in CURRENT context (before introducing this binder)
      results := results ++ (← findIntToNat ty lctx)
      -- Then introduce the binder and recurse into body
      let bodyResults ← withLocalDecl n bi ty fun fvar => do
        let lctx' ← getLCtx
        findIntToNat (body.instantiate1 fvar) lctx'
      results := results ++ bodyResults

  | .letE name type value body _ =>
      results := results ++ (← findIntToNat type lctx)
      results := results ++ (← findIntToNat value lctx)
      let bodyResults ← withLetDecl name type value fun fvar => do
        let lctx' ← getLCtx
        findIntToNat (body.instantiate1 fvar) lctx'
      results := results ++ bodyResults

  | .mdata _ inner =>
      results := results ++ (← findIntToNat inner lctx)

  | .proj _ _ inner =>
      results := results ++ (← findIntToNat inner lctx)

  | _ => pure ()

  return results

/-- Result of analyzing a declaration -/
structure AnalysisResult where
  declName : Name
  conversions : Array ToNatInfo
  unguardedCount : Nat
  deriving Inhabited

/-- Deduplicate conversions by semantic key (pretty-printed argument + guard status).
    Uses insertion-order to guarantee deterministic output. -/
def deduplicateConversions (convs : Array ToNatInfo) : Array ToNatInfo :=
  let init : Std.HashMap (String × Bool) Nat × Array ToNatInfo := ({}, #[])
  let (_, out) := convs.foldl (init := init) fun (seen, out) conv =>
    let key := (conv.argumentStr, conv.guardEvidence.isSome)
    match seen[key]? with
    | some idx =>
      if (out[idx]!).unsafetyEvidence.isNone && conv.unsafetyEvidence.isSome then
        (seen, out.set! idx conv)
      else
        (seen, out)
    | none => (seen.insert key out.size, out.push conv)
  out

/-- Analyze a declaration for Int.toNat issues -/
def analyzeDecl (declName : Name) : MetaM AnalysisResult := do
  let env ← getEnv
  let some constInfo := env.find? declName
    | throwError "Declaration {declName} not found"

  let type := constInfo.type
  let value? := constInfo.value?

  -- CRITICAL: Start with empty local context to avoid ambient hypotheses
  -- affecting guard proofs. The declaration's type/value are closed terms.
  let emptyLCtx : LocalContext := {}

  let mut allConvs := #[]

  -- Always analyze the type (statement/specification) under empty context
  let typeConvs ← withLCtx emptyLCtx #[] (findIntToNat type emptyLCtx)
  allConvs := allConvs ++ typeConvs

  -- Only analyze value for non-Prop definitions (skip proof terms)
  -- Proof terms can be enormous and contain incidental operations
  if let some value := value? then
    let isPropType ← isProp type
    if !isPropType then
      let valueConvs ← withLCtx emptyLCtx #[] (findIntToNat value emptyLCtx)
      allConvs := allConvs ++ valueConvs

  -- Deduplicate findings
  allConvs := deduplicateConversions allConvs

  -- Count unguarded Int.toNat (not natAbs, which is a different category)
  let unguarded := allConvs.filter (fun c => c.guardEvidence.isNone && c.kind == .toNat)

  return {
    declName := declName
    conversions := allConvs
    unguardedCount := unguarded.size
  }

/-- Generate a report for a single declaration -/
def generateReport (result : AnalysisResult) : MetaM String := do
  if result.conversions.isEmpty then
    return s!"✓ {result.declName}: No Int.toNat conversions found"

  let mut report := s!"⚠ {result.declName}: Found {result.conversions.size} Int→Nat conversion(s)\n"

  let mut i := 0
  for conv in result.conversions do
    i := i + 1
    -- Use pre-computed string captured at analysis time
    let funcName := match conv.kind with
      | .toNat => "Int.toNat"
      | .natAbs => "Int.natAbs"
    let status := match conv.kind with
      | .toNat =>
        match conv.guardEvidence with
        | some ev => s!"✓ guarded ({ev})"
        | none => "✗ UNGUARDED"
      | .natAbs => "⚠ review (absolute value)"
    report := report ++ s!"  [{i}] {funcName} ({conv.argumentStr}) [{status}]\n"

  if result.unguardedCount > 0 then
    report := report ++ s!"  WARNING: {result.unguardedCount} unguarded Int.toNat - negative values will become 0\n"

  return report

end AtpLinter.IntToNat
