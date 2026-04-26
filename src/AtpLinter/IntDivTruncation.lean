/-
  Integer Division Truncation Detector

  Detects cases where integer division truncates to zero or loses precision:
  - `1 / 4` on Nat = 0 (not 0.25)
  - `a / b` where a < b gives 0
  - Small literal divisions that truncate

  This is especially problematic in expressions like:
  - `x ^ (1 / 4)` where 1/4 becomes 0, making x^0 = 1
  - `(a + b) / 2` for averaging (loses the fractional part)

  Uses telescope-based traversal for correct binder handling.
-/

import Lean
import Lean.Elab.Command
import Lean.Meta.Basic
import AtpLinter.Basic

open Lean Elab Meta Term
open AtpLinter (ppExprSimple)

namespace AtpLinter.IntDivTruncation

/-! ## Phase 2: Data Model -/

/-- Classification of the truncation risk -/
inductive TruncationStatus where
  | willTruncate  -- Both literals, a % b ≠ 0 (e.g., 1/4, 3/2)
  | mayTruncate   -- At least one non-literal (e.g., n/4, a/b)
  | noTruncate    -- Both literals, a % b = 0 (e.g., 4/2)
  deriving Repr, BEq, Inhabited, Hashable

/-- Kind of integer division being detected -/
inductive DivKind where
  | nat      -- Nat division (Nat.div or HDiv on Nat)
  | intHDiv  -- HDiv on Int (default / operator)
  | intTdiv  -- Int.tdiv (truncated toward zero)
  | intFdiv  -- Int.fdiv (floored toward negative infinity)
  | intEdiv  -- Int.ediv (Euclidean division)
  deriving Repr, BEq, Inhabited, Hashable

/-- Information about a detected integer division that truncates -/
structure TruncDivInfo where
  expr : Expr
  dividend : Expr
  divisor : Expr
  dividendVal : Option Int := none
  divisorVal : Option Int := none
  status : TruncationStatus
  kind : DivKind := .nat
  -- Pretty-printed strings captured at analysis time for correct binder names
  dividendStr : String
  divisorStr : String
  deriving Inhabited

/-- Result of analyzing a declaration -/
structure AnalysisResult where
  declName : Name
  truncations : Array TruncDivInfo
  willTruncateCount : Nat
  mayTruncateCount : Nat
  deriving Inhabited

/-! ## Phase 3: Core Utilities -/

/-- Extract Nat literal value if present.
    Uses Expr.nat? for normalized OfNat.ofNat form,
    with fallback for raw .lit (.natVal n). -/
def getNatLit? (e : Expr) : Option Nat :=
  -- Try normalized form first (OfNat.ofNat)
  match e.nat? with
  | some n => some n
  | none =>
    -- Fallback for raw literals
    match e with
    | .lit (.natVal n) => some n
    | _ => none

/-- Extract Int literal value if present.
    Handles:
    - Positive: OfNat.ofNat or raw natVal cast to Int
    - Negative: Neg.neg (Int.negOfNat n) or Int.negSucc patterns -/
def getIntLit? (e : Expr) : Option Int :=
  -- Try as a Nat first (positive Int literals often come through OfNat)
  match getNatLit? e with
  | some n => some (Int.ofNat n)
  | none =>
    -- Check for negation: Neg.neg _ _ x where x is a positive literal
    if e.isAppOfArity ``Neg.neg 3 then
      let inner := e.getAppArgs[2]!
      match getNatLit? inner with
      | some n => some (-(Int.ofNat n))
      | none => none
    -- Check for Int.negOfNat n (another representation of negative integers)
    else if e.isAppOfArity ``Int.negOfNat 1 then
      let arg := e.getAppArgs[0]!
      match getNatLit? arg with
      | some n => some (-(Int.ofNat n))
      | none => none
    -- P3 fix: Handle Int.negSucc n (represents -(n+1))
    else if e.isAppOfArity ``Int.negSucc 1 then
      let arg := e.getAppArgs[0]!
      match getNatLit? arg with
      | some n => some (-(Int.ofNat (n + 1)))
      | none => none
    else
      none

/-- Get literal value for truncation classification.
    For Nat division, returns as Int. For Int division, extracts Int literal. -/
def getLitVal? (e : Expr) (kind : DivKind) : Option Int :=
  match kind with
  | .nat => getNatLit? e |>.map Int.ofNat
  | _ => getIntLit? e

/-- Match division patterns on Nat or Int.
    Returns (dividend, divisor, kind) if this is an integer division. -/
def matchIntegerDiv? (e : Expr) : Option (Expr × Expr × DivKind) :=
  -- Match HDiv.hDiv α β γ inst dividend divisor
  if e.isAppOfArity ``HDiv.hDiv 6 then
    let args := e.getAppArgs
    let α := args[0]!
    let dividend := args[4]!
    let divisor := args[5]!
    if α.isConstOf ``Nat then
      some (dividend, divisor, .nat)
    else if α.isConstOf ``Int then
      some (dividend, divisor, .intHDiv)
    else
      none
  -- Match Nat.div dividend divisor
  else if e.isAppOfArity ``Nat.div 2 then
    let args := e.getAppArgs
    some (args[0]!, args[1]!, .nat)
  -- Match Int.tdiv dividend divisor (truncated toward zero)
  else if e.isAppOfArity ``Int.tdiv 2 then
    let args := e.getAppArgs
    some (args[0]!, args[1]!, .intTdiv)
  -- Match Int.fdiv dividend divisor (floored toward negative infinity)
  else if e.isAppOfArity ``Int.fdiv 2 then
    let args := e.getAppArgs
    some (args[0]!, args[1]!, .intFdiv)
  -- Match Int.ediv dividend divisor (Euclidean division)
  else if e.isAppOfArity ``Int.ediv 2 then
    let args := e.getAppArgs
    some (args[0]!, args[1]!, .intEdiv)
  else
    none

/-- Classify truncation risk based on literal values.
    Works for both Nat and Int divisions.
    For Int, uses Int.emod for remainder check (exact division means a % b == 0). -/
def classifyTruncation (dividendVal divisorVal : Option Int) : TruncationStatus :=
  match dividendVal, divisorVal with
  | some 0, some b =>
      -- 0 / x is always 0, no truncation
      if b == 0 then .noTruncate  -- Defer to DivisionByZero linter
      else .noTruncate  -- 0 / b = 0, exact
  | some a, some b =>
      if b == 0 then
        .noTruncate  -- Defer to DivisionByZero linter
      else if a % b == 0 then
        .noTruncate  -- Exact division (works for both positive and negative)
      else
        .willTruncate  -- Definite truncation
  | some 0, none =>
      .noTruncate  -- 0 / x = 0 for any x, no truncation
  | _, some b =>
      if b == 0 then .noTruncate  -- Defer to DivisionByZero
      else if b == 1 || b == -1 then .noTruncate  -- x / ±1 = ±x (identity up to sign)
      else .mayTruncate  -- x / 2 -> precision loss
  | _, _ => .mayTruncate  -- At least one unknown


/-! ## Phase 4: Prefix-Context Traversal -/

/-- Core visitor that uses PREFIX-CONTEXT traversal for correct binder handling.
    Pretty-prints expressions at discovery time when binders are in scope.

    Note: IntDivTruncation doesn't do guard proving, so the context scoping
    is less critical than for DivisionByZero/NatSubtraction. However, we use
    the same pattern for consistency. -/
partial def findDivisionsCore (e : Expr) : MetaM (Array TruncDivInfo) := do
  let mut results := #[]

  -- Check if this expression is a division
  if let some (dividend, divisor, kind) := matchIntegerDiv? e then
    -- Use kind-appropriate literal extraction (Int for Int divisions, Nat→Int for Nat)
    let dividendVal := getLitVal? dividend kind
    let divisorVal := getLitVal? divisor kind
    let status := classifyTruncation dividendVal divisorVal

    if status != .noTruncate then
      -- Pretty-print NOW while we have the correct context
      let dividendStr ← ppExprSimple dividend
      let divisorStr ← ppExprSimple divisor
      results := results.push {
        expr := e
        dividend := dividend
        divisor := divisor
        dividendVal := dividendVal
        divisorVal := divisorVal
        status := status
        kind := kind
        dividendStr := dividendStr
        divisorStr := divisorStr
      }

  -- Recurse with PREFIX-CONTEXT correct binder handling
  -- Key: visit binder type BEFORE introducing later binders
  match e with
  | .app f a =>
      for r in (← findDivisionsCore f) do
        results := results.push r
      for r in (← findDivisionsCore a) do
        results := results.push r

  | .lam n ty body bi =>
      -- Visit binder type in CURRENT context
      for r in (← findDivisionsCore ty) do
        results := results.push r
      -- Then introduce the binder and recurse into body
      let bodyResults ← withLocalDecl n bi ty fun fvar => do
        findDivisionsCore (body.instantiate1 fvar)
      for r in bodyResults do
        results := results.push r

  | .forallE n ty body bi =>
      -- Visit binder type in CURRENT context
      for r in (← findDivisionsCore ty) do
        results := results.push r
      -- Then introduce the binder and recurse into body
      let bodyResults ← withLocalDecl n bi ty fun fvar => do
        findDivisionsCore (body.instantiate1 fvar)
      for r in bodyResults do
        results := results.push r

  | .letE name type value body _ =>
      for r in (← findDivisionsCore type) do
        results := results.push r
      for r in (← findDivisionsCore value) do
        results := results.push r
      let bodyResults ← withLetDecl name type value fun fvar => do
        findDivisionsCore (body.instantiate1 fvar)
      for r in bodyResults do
        results := results.push r

  | .mdata _ inner =>
      for r in (← findDivisionsCore inner) do
        results := results.push r

  | .proj _ _ inner =>
      for r in (← findDivisionsCore inner) do
        results := results.push r

  | _ => pure ()

  return results

/-- Deduplicate truncation findings by semantic key (pretty-printed operands, kind, status).
    Drops exprHash so semantically identical detections from different syntactic
    forms (HDiv.hDiv vs Int.tdiv) merge correctly.
    Uses insertion-order to guarantee deterministic output. -/
def deduplicateTruncations (truncs : Array TruncDivInfo) : Array TruncDivInfo :=
  let init : Std.HashMap (String × String × DivKind × TruncationStatus) Nat × Array TruncDivInfo := ({}, #[])
  let (_, out) := truncs.foldl (init := init) fun (seen, out) trunc =>
    let key := (trunc.dividendStr, trunc.divisorStr, trunc.kind, trunc.status)
    match seen[key]? with
    | some _ => (seen, out)  -- first wins (no evidence hierarchy for truncation)
    | none => (seen.insert key out.size, out.push trunc)
  out

/-- Analyze a declaration for truncating divisions -/
def analyzeDecl (declName : Name) : MetaM AnalysisResult := do
  let env ← getEnv
  let some constInfo := env.find? declName
    | throwError "Declaration {declName} not found"

  let mut allTruncs := #[]

  -- Always analyze the type (statement/specification)
  let typeTruncs ← findDivisionsCore constInfo.type
  for r in typeTruncs do
    allTruncs := allTruncs.push r

  -- Only analyze value for non-Prop definitions (skip proof terms)
  -- Proof terms can be enormous and contain incidental operations
  if let some value := constInfo.value? then
    let isPropType ← isProp constInfo.type
    if !isPropType then
      let valueTruncs ← findDivisionsCore value
      for r in valueTruncs do
        allTruncs := allTruncs.push r

  -- Deduplicate findings
  allTruncs := deduplicateTruncations allTruncs

  let willCount := allTruncs.filter (·.status == .willTruncate) |>.size
  let mayCount := allTruncs.filter (·.status == .mayTruncate) |>.size

  return {
    declName := declName
    truncations := allTruncs
    willTruncateCount := willCount
    mayTruncateCount := mayCount
  }

end AtpLinter.IntDivTruncation
