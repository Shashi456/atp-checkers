/-
  Guard Proving Tests

  Tests that the guard prover accepts/rejects guards correctly for
  division, Nat subtraction, Int.toNat, Int division variants, and edge cases.
-/

import AtpLinter
import TestAssertions
import Mathlib.Data.PNat.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Set.Basic
set_option linter.unusedVariables false

namespace GuardProving

-- ============================================================
-- Division Guard Proving
-- ============================================================

-- Should be UNGUARDED
def divUnguarded (x y : Nat) : Nat := x / y
/--
info: Analysis of GuardProving.divUnguarded:
──────────────────────────────────────────────────
[WARNING] GuardProving.divUnguarded: Potential Division by Zero
  x / y has no guard ensuring y ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : y ≠ 0` or `h : y > 0`

[WARNING] GuardProving.divUnguarded: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp divUnguarded

-- DivisionByZero: guarded (h : y ≠ 0). IntDivTruncation: still warns (x/y may truncate)
def divGuardedNe (x y : Nat) (h : y ≠ 0) : Nat := x / y
/--
info: Analysis of GuardProving.divGuardedNe:
──────────────────────────────────────────────────
[WARNING] GuardProving.divGuardedNe: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp divGuardedNe

/-- Instantiated universal nonzero facts should guard matching divisors. -/
def divGuardedForallNe (f : ℕ → ℕ) (h : ∀ x, f x ≠ 0) (a : ℕ) : ℕ := 1 / f a
#cov_assert_not divGuardedForallNe "Potential Division by Zero"
#cov_assert_has divGuardedForallNe "Integer Division Truncation"

-- DivisionByZero: guarded. IntDivTruncation: still warns
def divGuardedPos (x y : Nat) (h : 0 < y) : Nat := x / y
/--
info: Analysis of GuardProving.divGuardedPos:
──────────────────────────────────────────────────
[WARNING] GuardProving.divGuardedPos: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp divGuardedPos

-- DivisionByZero: guarded by omega. IntDivTruncation: still warns
def divGuardedOmega (x y : Nat) (h : y > 0) : Nat := x / y
/--
info: Analysis of GuardProving.divGuardedOmega:
──────────────────────────────────────────────────
[WARNING] GuardProving.divGuardedOmega: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp divGuardedOmega

/-- Casted Nat positivity should guard real division. -/
noncomputable def divGuardedNatCast (x : ℝ) (n : Nat) (h : 0 < n) : ℝ := x / (n : ℝ)
/-- info: ✓ GuardProving.divGuardedNatCast: No issues detected -/
#guard_msgs in #check_atp divGuardedNatCast

/-- Bare Real positivity should guard real division. -/
noncomputable def divGuardedRealPos (x y : ℝ) (h : 0 < y) : ℝ := x / y
/-- info: ✓ GuardProving.divGuardedRealPos: No issues detected -/
#guard_msgs in #check_atp divGuardedRealPos

/-- Conjunctive positivity hypothesis should guard product denominator. -/
noncomputable def divGuardedProductConj (x y z : ℝ) (h : 0 < y ∧ 0 < z) : ℝ := x / (y * z)
/-- info: ✓ GuardProving.divGuardedProductConj: No issues detected -/
#guard_msgs in #check_atp divGuardedProductConj

/-- Separate nonzero hypotheses should guard product denominators structurally. -/
noncomputable def divGuardedProductNe (x y z : ℝ) (hy : y ≠ 0) (hz : z ≠ 0) : ℝ := x / (y * z)
/-- info: ✓ GuardProving.divGuardedProductNe: No issues detected -/
#guard_msgs in #check_atp divGuardedProductNe

/-- Positivity should propagate through powers for division guards. -/
noncomputable def divGuardedSquare (x y : ℝ) (h : 0 < y) : ℝ := x / (y ^ 2)
/-- info: ✓ GuardProving.divGuardedSquare: No issues detected -/
#guard_msgs in #check_atp divGuardedSquare

/-- Nonzero hypotheses should propagate through powers structurally. -/
noncomputable def divGuardedPowNe (x y : ℝ) (hy : y ≠ 0) : ℝ := x / (y ^ 3)
/-- info: ✓ GuardProving.divGuardedPowNe: No issues detected -/
#guard_msgs in #check_atp divGuardedPowNe

/-- Structured positivity should discharge square-plus-one denominators. -/
noncomputable def divGuardedSquarePlusOne (x y : ℝ) : ℝ := x / (y ^ 2 + 1)
/-- info: ✓ GuardProving.divGuardedSquarePlusOne: No issues detected -/
#guard_msgs in #check_atp divGuardedSquarePlusOne

/-- Subtype nonzero properties should guard projected denominators. -/
noncomputable def divGuardedSubtypeNe (x : ℝ) (q : {q : ℝ // q ≠ 0}) : ℝ := x / q.1
/-- info: ✓ GuardProving.divGuardedSubtypeNe: No issues detected -/
#guard_msgs in #check_atp divGuardedSubtypeNe

structure NonZeroNat where
  val : ℕ
  ne_zero : val ≠ 0

/-- Proposition-valued structure fields should guard projected denominators. -/
def divGuardedStructField (x : NonZeroNat) : ℕ := 1 / x.val
#cov_assert_not divGuardedStructField "Potential Division by Zero"
#cov_assert_has divGuardedStructField "Integer Division Truncation"

/-- Positive subtypes should guard casted denominators. -/
noncomputable def divGuardedPNat (x : ℝ) (n : ℕ+) : ℝ := x / (n : ℝ)
/-- info: ✓ GuardProving.divGuardedPNat: No issues detected -/
#guard_msgs in #check_atp divGuardedPNat

-- ============================================================
-- Cast Transport Guard Proving
-- ============================================================

/-- Cast transport: ↑n with n > 0 should guard division on ℝ. -/
noncomputable def divGuardedNatCastPos (x : ℝ) (n : ℕ) (h : 0 < n) : ℝ := x / (n : ℝ)
/-- info: ✓ GuardProving.divGuardedNatCastPos: No issues detected -/
#guard_msgs in #check_atp divGuardedNatCastPos

/-- Cast transport: ↑n with n ≠ 0 should guard division on ℝ. -/
noncomputable def divGuardedNatCastNe (x : ℝ) (n : ℕ) (h : n ≠ 0) : ℝ := x / (n : ℝ)
/-- info: ✓ GuardProving.divGuardedNatCastNe: No issues detected -/
#guard_msgs in #check_atp divGuardedNatCastNe

/-- Cast transport: ↑k with k from Int and k ≠ 0 should guard on ℝ. -/
noncomputable def divGuardedIntCastNe (x : ℝ) (k : ℤ) (h : k ≠ 0) : ℝ := x / (k : ℝ)
/-- info: ✓ GuardProving.divGuardedIntCastNe: No issues detected -/
#guard_msgs in #check_atp divGuardedIntCastNe

/-- Unguarded Nat cast should still warn. -/
noncomputable def divUnguardedNatCast (x : ℝ) (n : ℕ) : ℝ := x / (n : ℝ)
/--
info: Analysis of GuardProving.divUnguardedNatCast:
──────────────────────────────────────────────────
[WARNING] GuardProving.divUnguardedNatCast: Potential Division by Zero
  x / ↑n has no guard ensuring ↑n ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : ↑n ≠ 0` or `h : ↑n > 0`

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp divUnguardedNatCast

/-- Cast transport: Rat cast with nonzero hypothesis. -/
noncomputable def divGuardedRatCast (x : ℝ) (q : ℚ) (h : q ≠ 0) : ℝ := x / (q : ℝ)
/-- info: ✓ GuardProving.divGuardedRatCast: No issues detected -/
#guard_msgs in #check_atp divGuardedRatCast

/-- Cast transport through analytic inverse: (↑n)⁻¹ with n ≠ 0. -/
noncomputable def invGuardedNatCast (n : ℕ) (h : n ≠ 0) : ℝ := ((n : ℝ))⁻¹
/-- info: ✓ GuardProving.invGuardedNatCast: No issues detected -/
#guard_msgs in #check_atp invGuardedNatCast

/-- Cast transport composes with structural nonzero: product of casts. -/
noncomputable def divGuardedCastProduct (x : ℝ) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) : ℝ :=
  x / ((m : ℝ) * (n : ℝ))
/-- info: ✓ GuardProving.divGuardedCastProduct: No issues detected -/
#guard_msgs in #check_atp divGuardedCastProduct

/-- Cast transport composes with structural nonzero: power of cast. -/
noncomputable def divGuardedCastPow (x : ℝ) (n : ℕ) (hn : n ≠ 0) : ℝ := x / ((n : ℝ) ^ 2)
/-- info: ✓ GuardProving.divGuardedCastPow: No issues detected -/
#guard_msgs in #check_atp divGuardedCastPow

-- ============================================================
-- Int.toNat Guard Proving (with enrichment)
-- ============================================================

/-- Subtype-guarded Int.toNat: Subtype.property should expose 0 ≤ n. -/
def toNatGuardedSubtype (n : {n : ℤ // 0 ≤ n}) : ℕ := n.1.toNat
/-- info: ✓ GuardProving.toNatGuardedSubtype: No issues detected -/
#guard_msgs in #check_atp toNatGuardedSubtype

/-- Conjunction-guarded Int.toNat: And expansion should expose 0 ≤ n. -/
def toNatGuardedConj (n : ℤ) (h : 0 ≤ n ∧ n < 100) : ℕ := n.toNat
/-- info: ✓ GuardProving.toNatGuardedConj: No issues detected -/
#guard_msgs in #check_atp toNatGuardedConj

-- ============================================================
-- Nat Subtraction Guard Proving
-- ============================================================

-- Should be UNGUARDED
def subUnguarded (a b : Nat) : Nat := a - b
/--
info: Analysis of GuardProving.subUnguarded:
──────────────────────────────────────────────────
[WARNING] GuardProving.subUnguarded: Truncated Nat Subtraction
  a - b has no guard ensuring b ≤ a
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≤ a` or use Int instead of Nat

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp subUnguarded

-- Should be guarded (direct assumption: h : b ≤ a)
def subGuarded (a b : Nat) (h : b ≤ a) : Nat := a - b
/-- info: ✓ GuardProving.subGuarded: No issues detected -/
#guard_msgs in #check_atp subGuarded

-- Should be guarded by omega (from h1 and h2, omega can derive b ≤ a)
def subGuardedOmega (a b c : Nat) (h1 : a ≥ c) (h2 : c ≥ b) : Nat := a - b
/-- info: ✓ GuardProving.subGuardedOmega: No issues detected -/
#guard_msgs in #check_atp subGuardedOmega

-- Should be guarded: conjunction-buried guard in positive position
def subGuardedConjDef (a b : Nat) (h : b ≤ a ∧ a > 0) : Nat := a - b
/-- info: ✓ GuardProving.subGuardedConjDef: No issues detected -/
#guard_msgs in #check_atp subGuardedConjDef

-- Should be guarded: conjunction with guard as second conjunct
def subGuardedConjHyp (a b : Nat) (h : b > 0 ∧ b ≤ a) : Nat := a - b
/-- info: ✓ GuardProving.subGuardedConjHyp: No issues detected -/
#guard_msgs in #check_atp subGuardedConjHyp

-- Should WARN: conjunction in negative position should NOT share guard
theorem subNegativeConj (a b : Nat) : ¬ (b ≤ a ∧ a - b = 0) → True := by intro; trivial
/--
info: Analysis of GuardProving.subNegativeConj:
──────────────────────────────────────────────────
[WARNING] GuardProving.subNegativeConj: Truncated Nat Subtraction
  a - b has no guard ensuring b ≤ a
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≤ a` or use Int instead of Nat

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp subNegativeConj

-- Should be CLEAN: implication antecedent becomes a real hypothesis via
-- forallTelescope, so b ≤ a is available from withExpandedAndHyps.
-- Polarity tracking in the traversal affects conjunction sharing during AST
-- walking, but binder-opened hypotheses are always real local facts.
theorem subImplAntecedent (a b : Nat) : (b ≤ a ∧ a - b = 0) → True := by intro; trivial
/-- info: ✓ GuardProving.subImplAntecedent: No issues detected -/
#guard_msgs in #check_atp subImplAntecedent

-- ============================================================
-- Int.toNat Guard Proving
-- ============================================================

-- Should be UNGUARDED
def toNatUnguarded (n : Int) : Nat := n.toNat
/--
info: Analysis of GuardProving.toNatUnguarded:
──────────────────────────────────────────────────
[WARNING] GuardProving.toNatUnguarded: Unguarded Int.toNat
  Int.toNat (n) has no guard ensuring (n) ≥ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : n ≥ 0` or use Int.natAbs for absolute value

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp toNatUnguarded

-- Should be guarded (direct assumption: h : 0 ≤ n)
def toNatGuarded (n : Int) (h : 0 ≤ n) : Nat := n.toNat
/-- info: ✓ GuardProving.toNatGuarded: No issues detected -/
#guard_msgs in #check_atp toNatGuarded

-- Should be guarded (direct assumption: h : n ≥ 0)
def toNatGuardedGe (n : Int) (h : n ≥ 0) : Nat := n.toNat
/-- info: ✓ GuardProving.toNatGuardedGe: No issues detected -/
#guard_msgs in #check_atp toNatGuardedGe

-- ============================================================
-- Int.natAbs vs Int.toNat
-- ============================================================

-- Should NOT flag: Int.natAbs is always safe (returns absolute value)
def absOk (a : Int) : Nat := Int.natAbs a
/-- info: ✓ GuardProving.absOk: No issues detected -/
#guard_msgs in #check_atp absOk

-- Should flag: Int.toNat without guard
def toNatBad (a : Int) : Nat := Int.toNat a
/--
info: Analysis of GuardProving.toNatBad:
──────────────────────────────────────────────────
[WARNING] GuardProving.toNatBad: Unguarded Int.toNat
  Int.toNat (a) has no guard ensuring (a) ≥ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : a ≥ 0` or use Int.natAbs for absolute value

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp toNatBad

-- Should NOT flag: Int.toNat with guard
def toNatOk (a : Int) (h : a ≥ 0) : Nat := Int.toNat a
/-- info: ✓ GuardProving.toNatOk: No issues detected -/
#guard_msgs in #check_atp toNatOk

-- ============================================================
-- Int Division Guard Variants
-- ============================================================

/-- DivisionByZero: guarded. IntDivTruncation: still warns (a/b may truncate) -/
def intTdivGuarded (a b : Int) (hb : b ≠ 0) : Int := Int.tdiv a b
/--
info: Analysis of GuardProving.intTdivGuarded:
──────────────────────────────────────────────────
[WARNING] GuardProving.intTdivGuarded: Integer Division Truncation
  a / b may truncate (truncates toward zero (Int.tdiv))
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp intTdivGuarded

/-- DivisionByZero: guarded (simp derives b ≠ 0). IntDivTruncation: still warns -/
def posGuardNat (a b : Nat) (h : 0 < b) : Nat := a / b
/--
info: Analysis of GuardProving.posGuardNat:
──────────────────────────────────────────────────
[WARNING] GuardProving.posGuardNat: Integer Division Truncation
  a / b may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp posGuardNat

/-- DivisionByZero: guarded. IntDivTruncation: still warns -/
def gtZeroGuardNat (a b : Nat) (h : b > 0) : Nat := a / b
/--
info: Analysis of GuardProving.gtZeroGuardNat:
──────────────────────────────────────────────────
[WARNING] GuardProving.gtZeroGuardNat: Integer Division Truncation
  a / b may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp gtZeroGuardNat

/-- DivisionByZero: guarded. IntDivTruncation: still warns -/
def posGuardInt (a b : Int) (h : 0 < b) : Int := a / b
/--
info: Analysis of GuardProving.posGuardInt:
──────────────────────────────────────────────────
[WARNING] GuardProving.posGuardInt: Integer Division Truncation
  a / b may truncate (truncates (Int default /))
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp posGuardInt

/-- DivisionByZero: guarded (simp derives b ≠ 0 from b < 0). IntDivTruncation: still warns -/
def negGuardInt (a b : Int) (h : b < 0) : Int := a / b
/--
info: Analysis of GuardProving.negGuardInt:
──────────────────────────────────────────────────
[WARNING] GuardProving.negGuardInt: Integer Division Truncation
  a / b may truncate (truncates (Int default /))
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp negGuardInt

-- ============================================================
-- Nat Subtraction Edge Cases
-- ============================================================

/-- Explicit n - 1 for comparison. Expected: NatSubtraction warning (unguarded). -/
def natMinusOneUnguarded (n : Nat) : Nat := n - 1
/--
info: Analysis of GuardProving.natMinusOneUnguarded:
──────────────────────────────────────────────────
[WARNING] GuardProving.natMinusOneUnguarded: Truncated Nat Subtraction
  n - 1 has no guard ensuring 1 ≤ n
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : 1 ≤ n` or use Int instead of Nat

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp natMinusOneUnguarded

-- ============================================================
-- Guard Proving: Omega and Chained Inequalities
-- ============================================================

/-- Subtraction guarded by omega-provable hypothesis -/
theorem subGuardedOmega2 (a b : Nat) (h : a ≥ b) : a - b + b = a := by omega
/-- info: ✓ GuardProving.subGuardedOmega2: No issues detected -/
#guard_msgs in #check_atp subGuardedOmega2

/-- Int.toNat guarded by h : x ≥ 2, omega should prove 0 ≤ x -/
theorem toNatGuardedFromGeTwo (x : Int) (h : x ≥ 2) : x.toNat ≥ 0 := by omega
/-- info: ✓ GuardProving.toNatGuardedFromGeTwo: No issues detected -/
#guard_msgs in #check_atp toNatGuardedFromGeTwo

/-- Chained inequalities: a ≥ c, c ≥ b ⟹ a ≥ b (omega should handle) -/
theorem chainedIneq (a b c : Nat) (h1 : a ≥ c) (h2 : c ≥ b) : a - b ≤ a := by omega
/--
info: ✓ GuardProving.chainedIneq: No issues detected
-/
#guard_msgs in #check_atp chainedIneq

-- ── Conjunction-aware guard mining ──────────────────────────────

/-- Existential with guard in sibling conjunct: ∃ q, 0 < q ∧ ... 1/q ... -/
def existsPositiveDenominator (α : ℝ) (n : Nat) : Prop :=
  ∃ q : ℝ, 0 < q ∧ |α - 1 / q| < 1 / (((n : ℝ) + 1) * q)

/-- info: ✓ GuardProving.existsPositiveDenominator: No issues detected -/
#guard_msgs in #check_atp existsPositiveDenominator

/-- Set predicate with guard in sibling conjunct: { q | q ≠ 0 ∧ ... 1/q ... } -/
def dirichletSetLike (α : ℝ) (n : Nat) : Set ℝ :=
  { q : ℝ | q ≠ 0 ∧ |α - 1 / q| < 1 / (((n : ℝ) + 1) * q) }

/-- info: ✓ GuardProving.dirichletSetLike: No issues detected -/
#guard_msgs in #check_atp dirichletSetLike

-- ── Positive-position conjunction: direct ─────────────────────

/-- Direct positive conjunction: x ≠ 0 guards 1/x in sibling -/
def positiveConjDiv (x : ℝ) : Prop :=
  x ≠ 0 ∧ 1 / x = x

/-- info: ✓ GuardProving.positiveConjDiv: No issues detected -/
#guard_msgs in #check_atp positiveConjDiv

/-- Direct positive conjunction: x ≠ 0 guards x⁻¹ in sibling -/
def positiveConjInv (x : Rat) : Prop :=
  x ≠ 0 ∧ x⁻¹ = x

/-- info: ✓ GuardProving.positiveConjInv: No issues detected -/
#guard_msgs in #check_atp positiveConjInv

-- ── Negative-position conjunction: warnings should fire ───────

/-- Negated conjunction: x ≠ 0 is NOT assumed, division warning should fire -/
def negatedConjunctionDiv (x : ℝ) : Prop :=
  ¬ (x ≠ 0 ∧ 1 / x = x)

/--
info: Analysis of GuardProving.negatedConjunctionDiv:
──────────────────────────────────────────────────
[WARNING] GuardProving.negatedConjunctionDiv: Potential Division by Zero
  1 / x has no guard ensuring x ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : x ≠ 0` or `h : x > 0`

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp negatedConjunctionDiv

/-- Implication antecedent: conjunction is hypothesis, not asserted -/
def antecedentConjunctionDiv (x : ℝ) : Prop :=
  (x ≠ 0 ∧ 1 / x = x) → True

/--
info: Analysis of GuardProving.antecedentConjunctionDiv:
──────────────────────────────────────────────────
[WARNING] GuardProving.antecedentConjunctionDiv: Potential Division by Zero
  1 / x has no guard ensuring x ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : x ≠ 0` or `h : x > 0`

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp antecedentConjunctionDiv

/-- Negated conjunction (analytic): x ≠ 0 is NOT assumed, inverse warning should fire -/
def negatedConjunctionInv (x : Rat) : Prop :=
  ¬ (x ≠ 0 ∧ x⁻¹ = x)

/--
info: Analysis of GuardProving.negatedConjunctionInv:
──────────────────────────────────────────────────
[WARNING] GuardProving.negatedConjunctionInv: Analytic Domain Totalization
  ⁻¹(x): x⁻¹ requires x ≠ 0 (returns 0 for zero input)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add guard hypothesis: x ≠ 0

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp negatedConjunctionInv

/-- Implication antecedent (analytic): conjunction is hypothesis, not asserted -/
def antecedentConjunctionInv (x : Rat) : Prop :=
  (x ≠ 0 ∧ x⁻¹ = x) → True

/--
info: Analysis of GuardProving.antecedentConjunctionInv:
──────────────────────────────────────────────────
[WARNING] GuardProving.antecedentConjunctionInv: Analytic Domain Totalization
  ⁻¹(x): x⁻¹ requires x ≠ 0 (returns 0 for zero input)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add guard hypothesis: x ≠ 0

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp antecedentConjunctionInv

-- ============================================================
-- Non-GroupWithZero Inverse Behavior
-- ============================================================

-- ============================================================
-- Modulo Conjunction Guard
-- ============================================================

/-- Conjunction-guarded modulo: sibling conjunct should discharge guard. -/
def modGuardedConj (a b : Nat) (h : b ≠ 0 ∧ a % b = 0) : Prop := a % b = 0
/-- info: ✓ GuardProving.modGuardedConj: No issues detected -/
#guard_msgs in #check_atp modGuardedConj

-- ============================================================
-- Non-GroupWithZero type inverse should NOT be checked (no x ≠ 0 warning).
-- Multiplicative group inverse is total — no domain issue.
-- Note: ℤ has Inv but not GroupWithZero. The analytic checker skips it
-- since GroupWithZero is not available.

-- ============================================================
-- Fin.isLt Success Path (positive regression)
-- ============================================================

/-- Fin.isLt from a PRECEDING binder should successfully guard a later
    body expression. Here i : Fin n gives i.val < n, so the body
    subtraction n - 1 is guarded when n > 0 is derivable from Fin context. -/
def finIsLtSuccessPath (n : Nat) (i : Fin n) : Nat := n - 1
-- Note: this warns because we can't derive 1 ≤ n from i < n alone
-- (Fin 0 is empty so i can't exist, but the type is still valid).
-- The Fin.isLt gives i.val < n. omega can derive n ≥ 1 from i.val < n
-- (since i.val : Nat, i.val < n means n ≥ 1). So this SHOULD be clean.
/-- info: ✓ GuardProving.finIsLtSuccessPath: No issues detected -/
#guard_msgs in #check_atp finIsLtSuccessPath

-- ============================================================
-- Modulo Binder-Type Regression
-- ============================================================

/-- Modulo in binder type: Fin (n % m) should warn when m could be 0.
    The binder's own Fin.isLt must not circularly justify m ≠ 0. -/
def moduloBinderTypeWarn (n m : Nat) : Fin (n % m) → Nat := fun _ => 0
/--
info: Analysis of GuardProving.moduloBinderTypeWarn:
──────────────────────────────────────────────────
[WARNING] GuardProving.moduloBinderTypeWarn: Modulo Edge Case
  n % m has no guard ensuring m ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : m ≠ 0`. Note: in Lean, n % 0 = n

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp moduloBinderTypeWarn

-- ============================================================
-- Binder Scope: prop-full, data-prefix semantics
-- ============================================================

/-- Later independent prop guard should still pass for div0 (prop-full).
    IntDivTruncation fires separately (a / b on Nat always truncates). -/
def laterPropGuard (a b : Nat) (x : Fin (a / b)) (hb : b ≠ 0) : Nat := 0
/--
info: Analysis of GuardProving.laterPropGuard:
──────────────────────────────────────────────────
[WARNING] GuardProving.laterPropGuard: Integer Division Truncation
  a / b may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp laterPropGuard

/-- Later independent nat-sub prop guard should still pass. -/
def laterNatSubPropGuard (n : Nat) (x : Fin (n - 1)) (h : 1 ≤ n) : Nat := 0
/-- info: ✓ GuardProving.laterNatSubPropGuard: No issues detected -/
#guard_msgs in #check_atp laterNatSubPropGuard

/-- Same-type sibling data leak should warn (data-prefix). -/
def siblingDataLeak (n k : Nat) (x y : Fin (n - k)) : Nat := 0
/--
info: Analysis of GuardProving.siblingDataLeak:
──────────────────────────────────────────────────
[WARNING] GuardProving.siblingDataLeak: Truncated Nat Subtraction
  n - k has no guard ensuring k ≤ n
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : k ≤ n` or use Int instead of Nat

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp siblingDataLeak

/-- Mixed-type dependent data leak should warn (data-prefix).
    y : {m // m < n - k} is data, not a proposition. Its Subtype.property
    would circularly provide evidence for the earlier binder type. -/
def mixedTypeLeak (n k : Nat) (x : Fin (n - k)) (y : {m : Nat // m < n - k}) : Nat := 0
/--
info: Analysis of GuardProving.mixedTypeLeak:
──────────────────────────────────────────────────
[WARNING] GuardProving.mixedTypeLeak: Truncated Nat Subtraction
  n - k has no guard ensuring k ≤ n
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : k ≤ n` or use Int instead of Nat

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp mixedTypeLeak

/-- Dependent proposition on dropped binder should also be dropped.
    h depends on x (which is data, dropped), so h is also dropped. -/
def dependentPropLeak (n k : Nat) (x : Fin (n - k)) (h : x.1 < n - k) : Nat := 0
/--
info: Analysis of GuardProving.dependentPropLeak:
──────────────────────────────────────────────────
[WARNING] GuardProving.dependentPropLeak: Truncated Nat Subtraction
  n - k has no guard ensuring k ≤ n
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : k ≤ n` or use Int instead of Nat

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp dependentPropLeak

end GuardProving
