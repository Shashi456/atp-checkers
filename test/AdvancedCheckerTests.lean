/-
  Advanced Checker Tests

  Counterexample search, cast-after-truncation, exponent truncation,
  analytic domain, and combined checker tests.

  TODO (countexample search module):
  Instead of having a custom-written countereexample searcher,
  implement the counterexample searcher,
  as part of this overall framework,
  by integrating with 'plausible' (https://github.com/leanprover-community/plausible).

  TODO(integration with Lean linting infrastructure):
  rather than writing our own custom linter that has its own formatting,
  Lean has a linting infrastructure (https://lean-lang.org/doc/api/Lean/Linter/Basic.html)
  that we should integrate with, to report warnings
  in a more standard way, and to allow users to easily disable specific warnings.

  TODO(#guard_msgs): Write a #guard_msgs check for these,
  so that we know that the messages we expect are being produced.
  Note that this may need a MCP with LSP support, to 'accept the suggestion'
  for this to be easy.
-/

import AtpLinter
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
#check_atp plainIntToNat

-- Should flag in theorem context
theorem castAfterDivTheorem (a b : Int) : (a / b).toNat ≥ 0 := Nat.zero_le _
#check_atp castAfterDivTheorem

-- ============================================================
-- Exponent Truncation
-- ============================================================

-- Test with Nat exponent (should NOT flag for negativity)
def natPower (a n : Nat) : Nat := a ^ n
#check_atp natPower

-- Test theorem about powers
theorem powerOfZero (a : Nat) : a ^ 0 = 1 := by rfl
#check_atp powerOfZero

-- ============================================================
-- Combined Phase 2
-- ============================================================

-- Multiple Phase 2 issues
def multiplePhase2Issues (a b : Int) : Nat :=
  let divided := a / b
  divided.toNat
#check_atp multiplePhase2Issues

-- This should trigger counterexample search (has sorry) AND find one
theorem falseWithSorry : ∀ (n : Nat), n = n + 1 := by sorry
#check_atp falseWithSorry

-- ============================================================
-- Analytic Domain
-- ============================================================

-- Inv.inv without guard - should detect
def inv_unguarded (x : Rat) : Rat := x⁻¹
#check_atp inv_unguarded

-- Inv.inv with guard (x ≠ 0) - should NOT detect
def inv_guarded (x : Rat) (h : x ≠ 0) : Rat := x⁻¹
#check_atp inv_guarded

-- Division (already covered by DivisionByZero, but inv is separate)
def div_test (x y : Rat) : Rat := x / y
#check_atp div_test

-- Multiple inverse operations
def multi_inv (x y : Rat) : Rat := x⁻¹ * y⁻¹
#check_atp multi_inv

-- Inverse of obviously non-zero (like a literal)
def inv_literal : Rat := (2 : Rat)⁻¹
#check_atp inv_literal

-- Inverse in theorem statement
theorem inv_in_statement (x : Rat) : x * x⁻¹ = 1 ∨ x = 0 := by
  sorry
#check_atp inv_in_statement

-- Theorem with inverse that's guarded by hypothesis
theorem inv_guarded_hyp (x : Rat) (hx : x ≠ 0) : (x⁻¹)⁻¹ = x := by
  sorry
#check_atp inv_guarded_hyp

-- ============================================================
-- Cast-after-Truncation Surface Syntax
-- ============================================================

-- Should detect: surface syntax / with Int.toNat
def divThenCast (a b : Int) : Nat := (a / b).toNat
#check_atp divThenCast

-- Should detect: surface syntax - with Int.toNat (Int subtraction)
def subThenCastInt (a b : Int) : Nat := (a - b).toNat
#check_atp subThenCastInt

-- Should detect: surface syntax % with Int.toNat
def modThenCast (a b : Int) : Nat := (a % b).toNat
#check_atp modThenCast

-- ============================================================
-- Counterexample Prop-Binder & Budget
-- ============================================================

-- Should NOT abort due to Prop binder h : n = 0
theorem propBinderTest (n : Nat) (h : n = 0) : n = 0 := h
#check_atp propBinderTest

-- Should find counterexample despite Prop binder
theorem propBinderFalse (n : Nat) (h : n > 0) : n + 1 = n := by sorry
#check_atp propBinderFalse

-- Should respect maxBinders = 4 (5 binders, search should skip)
theorem fiveBinders (a b c d e : Nat) : a + b + c + d + e > 0 := by sorry
#check_atp fiveBinders

-- Should work with exactly 4 binders
theorem fourBinders (a b c d : Nat) : a + b + c + d > 0 := by sorry
#check_atp fourBinders

-- Budget stress test: 4 binders × 5 Nat values = 625 max assignments
theorem budgetStress (a b c d : Nat) : a * b = c * d := by sorry
#check_atp budgetStress

-- ============================================================
-- Cast-after-Truncation (Nat→Int pattern)
-- ============================================================

namespace ReviewPatterns

/-- Cast after Nat subtraction - high signal error pattern. -/
def castAfterSub (a b : Nat) : Int := Int.ofNat (a - b)
#check_atp castAfterSub

/-- Cast after Nat division - similar pattern. -/
def castAfterDiv (a b : Nat) : Int := Int.ofNat (a / b)
#check_atp castAfterDiv

end ReviewPatterns

end AdvancedChecker
