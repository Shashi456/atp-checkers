/-
  Advanced Checker Tests

  Counterexample search, cast-after-truncation, exponent truncation,
  analytic domain, and combined checker tests.
-/

import AtpLinter
set_option linter.unusedVariables false

namespace AdvancedChecker

-- ============================================================
-- Counterexample Search
-- ============================================================

-- Should find counterexample: 0 + 0 ≠ 1
theorem falseAddition : ∀ (a b : Nat), a + b = 1 := by sorry
#check_atp falseAddition

-- Should find counterexample: false ≠ true
theorem falseBoolEquality : ∀ (b : Bool), b = true := by sorry
#check_atp falseBoolEquality

-- Should NOT find counterexample (true statement)
theorem trueStatement : ∀ (n : Nat), n + 0 = n := by
  intro n
  rfl
#check_atp trueStatement

-- Should find counterexample: 0 > 0 is false
theorem falseComparison : ∀ (n : Nat), n > 0 := by sorry
#check_atp falseComparison

-- Gate test: should run because it has sorry
theorem gatedBySorry : ∀ (n : Nat), n * 0 = 1 := by sorry
#check_atp gatedBySorry

-- ============================================================
-- Cast-after-Truncation
-- ============================================================

-- Should flag: Int.toNat applied to division result
def castAfterDiv (a b : Int) : Nat := (a / b).toNat
#check_atp castAfterDiv

-- Actual: warns Unguarded Int.toNat (no CastAfterTruncation for Int subtraction — Int sub doesn't truncate like Nat sub)
def castAfterSub (a b : Int) : Nat := (a - b).toNat
#check_atp castAfterSub

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
