/-
  Advanced Checker Tests

  Counterexample search, cast-after-truncation, exponent truncation,
  analytic domain, and combined checker tests.
-/
-- Future: adopt Lean linting infrastructure (lean-lang.org/doc/api/Lean/Linter/Basic.html)

import AtpLinter
import TestAssertions
set_option linter.unusedVariables false

namespace AdvancedChecker


-- ============================================================
-- Counterexample Search
-- ============================================================

-- Should find counterexample: 0 + 0 ≠ 1
theorem falseAddition : ∀ (a b : Nat), a + b = 1 := by sorry

/--
info: Analysis of AdvancedChecker.falseAddition:
──────────────────────────────────────────────────
[ERROR] AdvancedChecker.falseAddition: Counterexample Found
  Counterexample found: [a := 0, b := 0] makes proposition false
  Taxonomy: I.a - Specification Error
  Suggestion: The instantiated proposition `0 + 0 = 1` evaluates to false

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp falseAddition

-- Should find counterexample: false ≠ true
theorem falseBoolEquality : ∀ (b : Bool), b = true := by sorry
/--
info: Analysis of AdvancedChecker.falseBoolEquality:
──────────────────────────────────────────────────
[ERROR] AdvancedChecker.falseBoolEquality: Counterexample Found
  Counterexample found: [] makes proposition false
  Taxonomy: I.a - Specification Error
  Suggestion: The instantiated proposition `∀ (b : Bool), b = true` evaluates to false

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp falseBoolEquality

-- Should NOT find counterexample (true statement)
theorem trueStatement : ∀ (n : Nat), n + 0 = n := by
  intro n
  rfl
/-- info: ✓ AdvancedChecker.trueStatement: No issues detected -/
#guard_msgs in #check_atp trueStatement

-- Should find counterexample: 0 > 0 is false
theorem falseComparison : ∀ (n : Nat), n > 0 := by sorry
/--
info: Analysis of AdvancedChecker.falseComparison:
──────────────────────────────────────────────────
[ERROR] AdvancedChecker.falseComparison: Counterexample Found
  Counterexample found: [n := 0] makes proposition false
  Taxonomy: I.a - Specification Error
  Suggestion: The instantiated proposition `0 > 0` evaluates to false

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp falseComparison

-- Gate test: should run because it has sorry
theorem gatedBySorry : ∀ (n : Nat), n * 0 = 1 := by sorry
/--
info: Analysis of AdvancedChecker.gatedBySorry:
──────────────────────────────────────────────────
[ERROR] AdvancedChecker.gatedBySorry: Counterexample Found
  Counterexample found: [n := 0] makes proposition false
  Taxonomy: I.a - Specification Error
  Suggestion: The instantiated proposition `0 * 0 = 1` evaluates to false

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp gatedBySorry

-- ============================================================
-- Plausible Fallback
-- ============================================================

-- Values outside exhaustive range: exhaustive only tries 0–4, all pass n < 5.
-- Plausible finds n ≥ 5.
theorem plausibleLargeNat : ∀ (n : Nat), n < 5 := by sorry
/--
info: Analysis of AdvancedChecker.plausibleLargeNat:
──────────────────────────────────────────────────
[ERROR] AdvancedChecker.plausibleLargeNat: Counterexample Found
  Counterexample found: [n := 6] makes proposition false
  Taxonomy: I.a - Specification Error
  Suggestion: The instantiated proposition `6 < 5` evaluates to false (via random testing)

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp plausibleLargeNat
#cov_assert_has plausibleLargeNat "Counterexample Found"
#cov_assert_proved_by plausibleLargeNat "Counterexample Found" "plausible"

-- True proposition: neither searcher reports anything
theorem plausibleTrueStmt : ∀ (n : Nat), n + 0 = n := by intro n; rfl
/-- info: ✓ AdvancedChecker.plausibleTrueStmt: No issues detected -/
#guard_msgs in #check_atp plausibleTrueStmt

-- Exhaustive wins first: a + b = 1 is found by exhaustive (a:=0, b:=0), Plausible never runs
theorem plausibleExhaustiveFirst (a b : Nat) : a + b = 1 := by sorry
/--
info: Analysis of AdvancedChecker.plausibleExhaustiveFirst:
──────────────────────────────────────────────────
[ERROR] AdvancedChecker.plausibleExhaustiveFirst: Counterexample Found
  Counterexample found: [a := 0, b := 0] makes proposition false
  Taxonomy: I.a - Specification Error
  Suggestion: The instantiated proposition `0 + 0 = 1` evaluates to false

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp plausibleExhaustiveFirst
#cov_assert_proved_by plausibleExhaustiveFirst "Counterexample Found" "decide"

-- ============================================================
-- Cast-after-Truncation
-- ============================================================

-- Should flag: Int.toNat applied to division result
def castAfterDiv (a b : Int) : Nat := (a / b).toNat
/--
info: Analysis of AdvancedChecker.castAfterDiv:
──────────────────────────────────────────────────
[WARNING] AdvancedChecker.castAfterDiv: Potential Division by Zero
  a / b has no guard ensuring b ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≠ 0` or `h : b > 0`

[WARNING] AdvancedChecker.castAfterDiv: Integer Division Truncation
  a / b may truncate (truncates (Int default /))
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

[WARNING] AdvancedChecker.castAfterDiv: Unguarded Int.toNat
  Int.toNat (a / b) has no guard ensuring (a / b) ≥ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : a / b ≥ 0` or use Int.natAbs for absolute value

[WARNING] AdvancedChecker.castAfterDiv: Cast After Truncation
  Int.toNat applied after integer division: a / b
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: The inner operation may have already lost precision before the cast

──────────────────────────────────────────────────
Summary: 0 error(s), 4 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp castAfterDiv

-- Actual: warns Unguarded Int.toNat (no CastAfterTruncation for Int subtraction — Int sub doesn't truncate like Nat sub)
def castAfterSub (a b : Int) : Nat := (a - b).toNat
/--
info: Analysis of AdvancedChecker.castAfterSub:
──────────────────────────────────────────────────
[WARNING] AdvancedChecker.castAfterSub: Unguarded Int.toNat
  Int.toNat (a - b) has no guard ensuring (a - b) ≥ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : a - b ≥ 0` or use Int.natAbs for absolute value

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp castAfterSub

-- Actual: warns Unguarded Int.toNat (a has no ≥ 0 guard). No CastAfterTruncation (no inner truncating op).
def plainIntToNat (a : Int) : Nat := a.toNat
/--
info: Analysis of AdvancedChecker.plainIntToNat:
──────────────────────────────────────────────────
[WARNING] AdvancedChecker.plainIntToNat: Unguarded Int.toNat
  Int.toNat (a) has no guard ensuring (a) ≥ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : a ≥ 0` or use Int.natAbs for absolute value

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp plainIntToNat

-- Should flag in theorem context
theorem castAfterDivTheorem (a b : Int) : (a / b).toNat ≥ 0 := Nat.zero_le _
/--
info: Analysis of AdvancedChecker.castAfterDivTheorem:
──────────────────────────────────────────────────
[WARNING] AdvancedChecker.castAfterDivTheorem: Potential Division by Zero
  a / b has no guard ensuring b ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≠ 0` or `h : b > 0`

[WARNING] AdvancedChecker.castAfterDivTheorem: Integer Division Truncation
  a / b may truncate (truncates (Int default /))
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

[WARNING] AdvancedChecker.castAfterDivTheorem: Unguarded Int.toNat
  Int.toNat (a / b) has no guard ensuring (a / b) ≥ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : a / b ≥ 0` or use Int.natAbs for absolute value

[WARNING] AdvancedChecker.castAfterDivTheorem: Cast After Truncation
  Int.toNat applied after integer division: a / b
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: The inner operation may have already lost precision before the cast

──────────────────────────────────────────────────
Summary: 0 error(s), 4 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp castAfterDivTheorem

-- ============================================================
-- Exponent Truncation
-- ============================================================

-- Test with Nat exponent (should NOT flag for negativity)
def natPower (a n : Nat) : Nat := a ^ n
/-- info: ✓ AdvancedChecker.natPower: No issues detected -/
#guard_msgs in #check_atp natPower

-- Test theorem about powers
theorem powerOfZero (a : Nat) : a ^ 0 = 1 := by rfl
/-- info: ✓ AdvancedChecker.powerOfZero: No issues detected -/
#guard_msgs in #check_atp powerOfZero

-- ============================================================
-- Combined Phase 2
-- ============================================================

-- Multiple Phase 2 issues
def multiplePhase2Issues (a b : Int) : Nat :=
  let divided := a / b
  divided.toNat
/--
info: Analysis of AdvancedChecker.multiplePhase2Issues:
──────────────────────────────────────────────────
[WARNING] AdvancedChecker.multiplePhase2Issues: Potential Division by Zero
  a / b has no guard ensuring b ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≠ 0` or `h : b > 0`

[WARNING] AdvancedChecker.multiplePhase2Issues: Integer Division Truncation
  a / b may truncate (truncates (Int default /))
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

[WARNING] AdvancedChecker.multiplePhase2Issues: Unguarded Int.toNat
  Int.toNat (divided) has no guard ensuring (divided) ≥ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : divided ≥ 0` or use Int.natAbs for absolute value

──────────────────────────────────────────────────
Summary: 0 error(s), 3 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp multiplePhase2Issues

-- This should trigger counterexample search (has sorry) AND find one
theorem falseWithSorry : ∀ (n : Nat), n = n + 1 := by sorry
/--
info: Analysis of AdvancedChecker.falseWithSorry:
──────────────────────────────────────────────────
[ERROR] AdvancedChecker.falseWithSorry: Counterexample Found
  Counterexample found: [n := 0] makes proposition false
  Taxonomy: I.a - Specification Error
  Suggestion: The instantiated proposition `0 = 0 + 1` evaluates to false

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp falseWithSorry

-- ============================================================
-- Analytic Domain
-- ============================================================

-- Inv.inv without guard - should detect
def inv_unguarded (x : Rat) : Rat := x⁻¹
/--
info: Analysis of AdvancedChecker.inv_unguarded:
──────────────────────────────────────────────────
[WARNING] AdvancedChecker.inv_unguarded: Analytic Domain Totalization
  ⁻¹(x): x⁻¹ requires x ≠ 0 (returns 0 for zero input)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add guard hypothesis: x ≠ 0

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp inv_unguarded

-- Inv.inv with guard (x ≠ 0) - should NOT detect
def inv_guarded (x : Rat) (h : x ≠ 0) : Rat := x⁻¹
/-- info: ✓ AdvancedChecker.inv_guarded: No issues detected -/
#guard_msgs in #check_atp inv_guarded

-- Division (already covered by DivisionByZero, but inv is separate)
def div_test (x y : Rat) : Rat := x / y
/--
info: Analysis of AdvancedChecker.div_test:
──────────────────────────────────────────────────
[WARNING] AdvancedChecker.div_test: Potential Division by Zero
  x / y has no guard ensuring y ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : y ≠ 0` or `h : y > 0`

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp div_test

-- Multiple inverse operations
def multi_inv (x y : Rat) : Rat := x⁻¹ * y⁻¹
/--
info: Analysis of AdvancedChecker.multi_inv:
──────────────────────────────────────────────────
[WARNING] AdvancedChecker.multi_inv: Analytic Domain Totalization
  ⁻¹(x): x⁻¹ requires x ≠ 0 (returns 0 for zero input)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add guard hypothesis: x ≠ 0

[WARNING] AdvancedChecker.multi_inv: Analytic Domain Totalization
  ⁻¹(y): x⁻¹ requires x ≠ 0 (returns 0 for zero input)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add guard hypothesis: y ≠ 0

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp multi_inv

-- Inverse of obviously non-zero (like a literal)
def inv_literal : Rat := (2 : Rat)⁻¹
/--
info: Analysis of AdvancedChecker.inv_literal:
──────────────────────────────────────────────────
[WARNING] AdvancedChecker.inv_literal: Analytic Domain Totalization
  ⁻¹(2): x⁻¹ requires x ≠ 0 (returns 0 for zero input)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add guard hypothesis: 2 ≠ 0

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp inv_literal

-- Inverse in theorem statement
theorem inv_in_statement (x : Rat) : x * x⁻¹ = 1 ∨ x = 0 := by
  sorry
/--
info: Analysis of AdvancedChecker.inv_in_statement:
──────────────────────────────────────────────────
[WARNING] AdvancedChecker.inv_in_statement: Analytic Domain Totalization
  ⁻¹(x): x⁻¹ requires x ≠ 0 (returns 0 for zero input)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add guard hypothesis: x ≠ 0

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp inv_in_statement

-- Theorem with inverse that's guarded by hypothesis
theorem inv_guarded_hyp (x : Rat) (hx : x ≠ 0) : (x⁻¹)⁻¹ = x := by
  sorry
/--
info: Analysis of AdvancedChecker.inv_guarded_hyp:
──────────────────────────────────────────────────
[WARNING] AdvancedChecker.inv_guarded_hyp: Analytic Domain Totalization
  ⁻¹(x⁻¹): x⁻¹ requires x ≠ 0 (returns 0 for zero input)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add guard hypothesis: x⁻¹ ≠ 0

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp inv_guarded_hyp

-- ============================================================
-- Cast-after-Truncation Surface Syntax
-- ============================================================

-- Should detect: surface syntax / with Int.toNat
def divThenCast (a b : Int) : Nat := (a / b).toNat
/--
info: Analysis of AdvancedChecker.divThenCast:
──────────────────────────────────────────────────
[WARNING] AdvancedChecker.divThenCast: Potential Division by Zero
  a / b has no guard ensuring b ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≠ 0` or `h : b > 0`

[WARNING] AdvancedChecker.divThenCast: Integer Division Truncation
  a / b may truncate (truncates (Int default /))
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

[WARNING] AdvancedChecker.divThenCast: Unguarded Int.toNat
  Int.toNat (a / b) has no guard ensuring (a / b) ≥ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : a / b ≥ 0` or use Int.natAbs for absolute value

[WARNING] AdvancedChecker.divThenCast: Cast After Truncation
  Int.toNat applied after integer division: a / b
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: The inner operation may have already lost precision before the cast

──────────────────────────────────────────────────
Summary: 0 error(s), 4 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp divThenCast

-- Should detect: surface syntax - with Int.toNat (Int subtraction)
def subThenCastInt (a b : Int) : Nat := (a - b).toNat
/--
info: Analysis of AdvancedChecker.subThenCastInt:
──────────────────────────────────────────────────
[WARNING] AdvancedChecker.subThenCastInt: Unguarded Int.toNat
  Int.toNat (a - b) has no guard ensuring (a - b) ≥ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : a - b ≥ 0` or use Int.natAbs for absolute value

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp subThenCastInt

-- Should detect: surface syntax % with Int.toNat
def modThenCast (a b : Int) : Nat := (a % b).toNat
/--
info: Analysis of AdvancedChecker.modThenCast:
──────────────────────────────────────────────────
[WARNING] AdvancedChecker.modThenCast: Unguarded Int.toNat
  Int.toNat (a % b) has no guard ensuring (a % b) ≥ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : a % b ≥ 0` or use Int.natAbs for absolute value

[WARNING] AdvancedChecker.modThenCast: Modulo Edge Case
  a % b has no guard ensuring b ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≠ 0`. Note: in Lean, n % 0 = n

[WARNING] AdvancedChecker.modThenCast: Cast After Truncation
  Int.toNat applied after integer modulo: a % b
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: The inner operation may have already lost precision before the cast

──────────────────────────────────────────────────
Summary: 0 error(s), 3 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp modThenCast

-- ============================================================
-- Counterexample Prop-Binder & Budget
-- ============================================================

-- Should NOT abort due to Prop binder h : n = 0
theorem propBinderTest (n : Nat) (h : n = 0) : n = 0 := h
/-- info: ✓ AdvancedChecker.propBinderTest: No issues detected -/
#guard_msgs in #check_atp propBinderTest

-- Should find counterexample despite Prop binder
theorem propBinderFalse (n : Nat) (h : n > 0) : n + 1 = n := by sorry
/--
info: Analysis of AdvancedChecker.propBinderFalse:
──────────────────────────────────────────────────
[ERROR] AdvancedChecker.propBinderFalse: Counterexample Found
  Counterexample found: [n := 1] makes proposition false
  Taxonomy: I.a - Specification Error
  Suggestion: The instantiated proposition `1 > 0 → 1 + 1 = 1` evaluates to false

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp propBinderFalse

-- Exhaustive search skips at 5 binders, but Plausible fallback finds counterexample
theorem fiveBinders (a b c d e : Nat) : a + b + c + d + e > 0 := by sorry
/--
info: Analysis of AdvancedChecker.fiveBinders:
──────────────────────────────────────────────────
[ERROR] AdvancedChecker.fiveBinders: Counterexample Found
  Counterexample found: [a := 0, b := 0, c := 0, d := 0, e := 0] makes proposition false
  Taxonomy: I.a - Specification Error
  Suggestion: The instantiated proposition `0 < 0` evaluates to false (via random testing)

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp fiveBinders

-- Should work with exactly 4 binders
theorem fourBinders (a b c d : Nat) : a + b + c + d > 0 := by sorry
/--
info: Analysis of AdvancedChecker.fourBinders:
──────────────────────────────────────────────────
[ERROR] AdvancedChecker.fourBinders: Counterexample Found
  Counterexample found: [a := 0, b := 0, c := 0, d := 0] makes proposition false
  Taxonomy: I.a - Specification Error
  Suggestion: The instantiated proposition `0 + 0 + 0 + 0 > 0` evaluates to false

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp fourBinders

-- Budget stress test: 4 binders × 5 Nat values = 625 max assignments
theorem budgetStress (a b c d : Nat) : a * b = c * d := by sorry
/--
info: Analysis of AdvancedChecker.budgetStress:
──────────────────────────────────────────────────
[ERROR] AdvancedChecker.budgetStress: Counterexample Found
  Counterexample found: [a := 0, b := 0, c := 1, d := 1] makes proposition false
  Taxonomy: I.a - Specification Error
  Suggestion: The instantiated proposition `0 * 0 = 1 * 1` evaluates to false

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp budgetStress

-- ============================================================
-- Cast-after-Truncation (Nat→Int pattern)
-- ============================================================

namespace ReviewPatterns

/-- Cast after Nat subtraction - high signal error pattern. -/
def castAfterSub (a b : Nat) : Int := Int.ofNat (a - b)
/--
info: Analysis of AdvancedChecker.ReviewPatterns.castAfterSub:
──────────────────────────────────────────────────
[WARNING] AdvancedChecker.ReviewPatterns.castAfterSub: Truncated Nat Subtraction
  a - b has no guard ensuring b ≤ a
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≤ a` or use Int instead of Nat

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp castAfterSub

/-- Cast after Nat division - similar pattern. -/
def castAfterDiv (a b : Nat) : Int := Int.ofNat (a / b)
/--
info: Analysis of AdvancedChecker.ReviewPatterns.castAfterDiv:
──────────────────────────────────────────────────
[WARNING] AdvancedChecker.ReviewPatterns.castAfterDiv: Potential Division by Zero
  a / b has no guard ensuring b ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≠ 0` or `h : b > 0`

[WARNING] AdvancedChecker.ReviewPatterns.castAfterDiv: Integer Division Truncation
  a / b may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp castAfterDiv

end ReviewPatterns

end AdvancedChecker
