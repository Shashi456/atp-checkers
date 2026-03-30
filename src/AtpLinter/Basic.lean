/-
  ATP Linter - Basic definitions and types

  This module provides common types and utilities used across
  all the specific linters.
-/

import Lean
import Mathlib.Algebra.CharZero.Defs

open Lean Meta

namespace AtpLinter

/-- Categories of errors we detect -/
inductive ErrorCategory where
  | truncatedSubtraction   -- Nat subtraction without guard
  | divisionByZero         -- Division without non-zero guard
  | intDivTruncation       -- Integer division truncates (e.g., 1/4 = 0)
  | intToNat               -- Int.toNat without non-negative guard
  | listRange              -- 0-indexed range (informational)
  | modulo                 -- n % 0 = n edge case
  -- Phase 1 categories
  | unsoundAxiom           -- User axiom asserting theorem without proof
  | vacuousTheorem         -- Contradictory hypotheses make theorem trivially true
  | unusedBinder           -- Quantified variable not used in body
  -- Phase 2 categories
  | counterexample         -- Found concrete counterexample to proposition
  | castAfterTruncation    -- Cast applied after truncating operation
  | exponentTruncation     -- Negative/zero exponent with Nat result
  -- Phase 5 categories
  | analyticDomain         -- sqrt/log/inv without domain guard
  -- Infrastructure
  | infraError             -- Linter internal error on a declaration
  deriving Repr, BEq, Hashable

/-- Severity levels -/
inductive Severity where
  | error      -- Almost certainly wrong
  | warning    -- Likely wrong, needs review
  | info       -- May be intentional, flagged for awareness
  deriving Repr, BEq

/-- Confidence level for a lint finding -/
inductive Confidence where
  | proven    -- Constructive proof/witness that the risky behavior occurs
  | maybe     -- Suspicious pattern or failed safety proof, but no proof of actual failure
  deriving Repr, BEq, Inhabited

instance : ToString Confidence where
  toString
    | .proven => "proven"
    | .maybe => "maybe"

/-- A single lint finding -/
structure LintFinding where
  category : ErrorCategory
  severity : Severity
  declName : Name
  message : String
  suggestion : Option String := none
  confidence : Confidence := .maybe
  provedBy : Option String := none     -- tactic/method name (e.g. "omega", "decide", "definitional")
  deriving Repr

/-- Get a human-readable name for an error category -/
def ErrorCategory.toString : ErrorCategory → String
  | .truncatedSubtraction => "Truncated Nat Subtraction"
  | .divisionByZero => "Potential Division by Zero"
  | .intDivTruncation => "Integer Division Truncation"
  | .intToNat => "Unguarded Int.toNat"
  | .listRange => "0-Indexed Range"
  | .modulo => "Modulo Edge Case"
  | .unsoundAxiom => "Unsound Axiom"
  | .vacuousTheorem => "Vacuous Theorem"
  | .unusedBinder => "Unused Quantified Variable"
  | .counterexample => "Counterexample Found"
  | .castAfterTruncation => "Cast After Truncation"
  | .exponentTruncation => "Exponent Truncation"
  | .analyticDomain => "Analytic Domain Totalization"
  | .infraError => "Linter Internal Error"

/-- Get the taxonomy category for an error -/
def ErrorCategory.taxonomyCategory : ErrorCategory → String
  | .truncatedSubtraction => "I.d - Lean Semantic Traps"
  | .divisionByZero => "I.d - Lean Semantic Traps"
  | .intDivTruncation => "I.d - Lean Semantic Traps"
  | .intToNat => "I.d - Lean Semantic Traps"
  | .listRange => "I.b - Goal Misalignment (potential)"
  | .modulo => "I.d - Lean Semantic Traps"
  | .unsoundAxiom => "I.c - Unproven Statement"
  | .vacuousTheorem => "I.a - Specification Error"
  | .unusedBinder => "I.a - Specification Error"
  | .counterexample => "I.a - Specification Error"
  | .castAfterTruncation => "I.d - Lean Semantic Traps"
  | .exponentTruncation => "I.d - Lean Semantic Traps"
  | .analyticDomain => "I.d - Lean Semantic Traps"
  | .infraError => "Infrastructure"

/-- Get severity for a category -/
def ErrorCategory.defaultSeverity : ErrorCategory → Severity
  | .truncatedSubtraction => .warning
  | .divisionByZero => .warning
  | .intDivTruncation => .error  -- Often critical bug
  | .intToNat => .warning
  | .listRange => .info
  | .modulo => .warning
  | .unsoundAxiom => .error     -- Axiom instead of theorem
  | .vacuousTheorem => .error   -- Contradictory hypotheses (omega)
  | .unusedBinder => .warning   -- Possibly intentional
  | .counterexample => .error   -- Definitively false proposition
  | .castAfterTruncation => .warning  -- Potential compounded truncation
  | .exponentTruncation => .warning   -- Possibly intentional
  | .analyticDomain => .warning       -- Missing domain guard for totalized function
  | .infraError => .info              -- Internal linter error (not a user issue)

instance : ToString ErrorCategory := ⟨ErrorCategory.toString⟩

instance : ToString Severity where
  toString
    | .error => "ERROR"
    | .warning => "WARNING"
    | .info => "INFO"

/-- Format a lint finding for display -/
def LintFinding.format (f : LintFinding) : String :=
  let severityStr := toString f.severity
  let catStr := toString f.category
  let taxonomyStr := f.category.taxonomyCategory
  let base := s!"[{severityStr}] {f.declName}: {catStr}\n  {f.message}\n  Taxonomy: {taxonomyStr}"
  match f.suggestion with
  | some sug => base ++ s!"\n  Suggestion: {sug}"
  | none => base

/-- Check if a string contains a substring -/
def containsSubstr (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Check if an expression is syntactically zero.
    Handles:
    - Direct `.lit (.natVal 0)`
    - `@OfNat.ofNat α 0 inst` (how `(0 : T)` appears after elaboration)
    - `@Zero.zero α inst`

    PERFORMANCE: Syntactic checks only, no `isDefEq` (which can hang on pathological inputs). -/
def isSyntacticZero (e : Expr) : Bool :=
  match e with
  -- Direct literal 0
  | .lit (.natVal 0) => true
  -- OfNat.ofNat α n inst — check that n (args[1]) is literal 0
  | e =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.getAppArgs[1]! with
      | .lit (.natVal 0) => true
      | _ => false
    else if e.isAppOfArity ``Zero.zero 2 then
      true
    else
      false

/-- Check if an expression is a syntactic non-zero literal (1, 2, 3, etc.)
    Used to skip false positive warnings for divisions like `x / 2` or `(2 : Rat)⁻¹`.
    SOUNDNESS NOTE: This is safe for ℕ, ℤ, ℚ, ℝ, ℂ but NOT for Fin n or ZMod n
    where e.g. (2 : Fin 2) = 0. Pair with `isSafeTypeForNonZeroLiteral`. -/
def isSyntacticNonZeroLiteral (e : Expr) : Bool :=
  match e with
  | .lit (.natVal n) => n > 0
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ => n > 0
  | .app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n)) => n > 0
  | .app (.app (.const ``One.one _) _) _ => true
  | .app (.const ``One.one _) _ => true
  | _ => false

/-- Check if a type is "safe" for syntactic non-zero optimization.
    Safe types are those where numeric literals mean what they say —
    i.e. no nonzero natural number coerces to zero. This is exactly
    the CharZero typeclass. Covers ℕ, ℤ, ℚ, ℝ, ℂ and any other
    CharZero type. Unsafe types (Fin n, ZMod n) will not have the
    instance and correctly return false.
    Falls back to Nat/Int name matching if instance synthesis fails
    (e.g. due to missing imports). -/
def isSafeTypeForNonZeroLiteral (ty : Expr) : MetaM Bool := do
  -- Fast path for Nat/Int (always safe, no instance needed)
  if ty.isConstOf ``Nat || ty.isConstOf ``Int then return true
  -- Principled check: does the type have CharZero?
  try
    let _ ← Meta.synthInstance (← Meta.mkAppM ``CharZero #[ty])
    return true
  catch _ =>
    return false

/-- Build a local context for analyzing binder j's type using "prop-full,
    data-prefix" semantics:
    - Keep all earlier binders (0..j-1)
    - Drop the current binder j
    - Drop all later NON-propositional binders (data evidence like Fin, Subtype
      values whose derived facts could circularly justify the type)
    - Keep later propositional binders UNLESS they depend on a dropped binder
      (prevents circular props like `h : x.1 < n - k` where x was dropped)

    This prevents:
    - Self-justification: `i : Fin (n - k)` using its own Fin.isLt
    - Same-type siblings: `(x y : Fin (n - k))` — y is data, dropped
    - Mixed-type witnesses: `(x : Fin (n-k)) (y : {m // m < n-k})` — y is data
    - Dependent circular props: `(x : Fin (n-k)) (h : x.1 < n-k)` — h depends on x

    While preserving:
    - Legitimate later guards: `(x : Fin (a/b)) (hb : b ≠ 0)` — hb is prop,
      independent of x -/
def mkSafeLCtxForType (fullLCtx : LocalContext) (fvars : Array Expr) (j : Nat) : MetaM LocalContext := do
  let mut lctx := fullLCtx
  -- Track which fvars are dropped so we can check dependency
  let mut dropped : Array FVarId := #[fvars[j]!.fvarId!]
  -- Always drop the current binder
  lctx := lctx.erase fvars[j]!.fvarId!
  -- Process later binders
  for k in [j + 1 : fvars.size] do
    let fvar := fvars[k]!
    let fid := fvar.fvarId!
    let ty ← Meta.inferType fvar
    if ← Meta.isProp ty then
      -- Propositional binder: keep UNLESS it depends on a dropped binder
      let dependsOnDropped := dropped.any fun did => ty.containsFVar did
      if dependsOnDropped then
        lctx := lctx.erase fid
        dropped := dropped.push fid
    else
      -- Data binder: always drop (could produce circular derived facts)
      lctx := lctx.erase fid
      dropped := dropped.push fid
  return lctx

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

end AtpLinter
