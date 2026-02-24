/-
  Coverage Tests

  Explicit TP/TN/FP/FN-style checks for checker behavior and confidence semantics.
  These are assertion-based (not observational #check output).
-/

import AtpLinter
import TestAssertions
set_option linter.unusedVariables false

namespace Coverage

-- ============================================================
-- Division by Zero (TP / TN / FP)
-- ============================================================

def covDivTP (a b : Nat) (h : b = 0) : Nat := a / b
#cov_assert_has covDivTP "Potential Division by Zero"
#cov_assert_confidence covDivTP "Potential Division by Zero" proven
#cov_assert_proved_by covDivTP "Potential Division by Zero" "assumption"

def covDivTN (a b : Nat) (h : b ≠ 0) : Nat := a / b
#cov_assert_not covDivTN "Potential Division by Zero"

def covDivFP_literal (a : Nat) : Nat := a / 2
#cov_assert_not covDivFP_literal "Potential Division by Zero"

-- ============================================================
-- Nat Subtraction (TP / TN / FP)
-- ============================================================

def covSubTP (a b : Nat) (h : a < b) : Nat := a - b
#cov_assert_has covSubTP "Truncated Nat Subtraction"
#cov_assert_confidence covSubTP "Truncated Nat Subtraction" proven
#cov_assert_proved_by covSubTP "Truncated Nat Subtraction" "assumption"

def covSubTN (a b : Nat) (h : b ≤ a) : Nat := a - b
#cov_assert_not covSubTN "Truncated Nat Subtraction"

def covSubFP_zero (a : Nat) : Nat := a - 0
#cov_assert_not covSubFP_zero "Truncated Nat Subtraction"

-- ============================================================
-- Int.toNat (TP / TN / FP)
-- ============================================================

def covToNatTP (x : Int) (h : x < 0) : Nat := Int.toNat x
#cov_assert_has covToNatTP "Unguarded Int.toNat"
#cov_assert_confidence covToNatTP "Unguarded Int.toNat" proven
#cov_assert_proved_by covToNatTP "Unguarded Int.toNat" "assumption"

def covToNatTN (x : Int) (h : 0 ≤ x) : Nat := Int.toNat x
#cov_assert_not covToNatTN "Unguarded Int.toNat"

def covToNatFP_natAbs (x : Int) : Nat := Int.natAbs x
#cov_assert_not covToNatFP_natAbs "Unguarded Int.toNat"

-- ============================================================
-- Modulo by Zero (TP / TN / FP)
-- ============================================================

def covModTP (a b : Nat) (h : b = 0) : Nat := a % b
#cov_assert_has covModTP "Modulo Edge Case"
#cov_assert_confidence covModTP "Modulo Edge Case" proven
#cov_assert_proved_by covModTP "Modulo Edge Case" "assumption"

def covModTN (a b : Nat) (h : b ≠ 0) : Nat := a % b
#cov_assert_not covModTN "Modulo Edge Case"

def covModFP_literal (a : Nat) : Nat := a % 2
#cov_assert_not covModFP_literal "Modulo Edge Case"

-- ============================================================
-- Integer Division Truncation (TP / TN / FP)
-- ============================================================

def covTruncTP : Nat := 1 / 4
#cov_assert_has covTruncTP "Integer Division Truncation"
#cov_assert_confidence covTruncTP "Integer Division Truncation" proven
#cov_assert_proved_by covTruncTP "Integer Division Truncation" "definitional"

def covTruncTN : Nat := 4 / 2
#cov_assert_not covTruncTN "Integer Division Truncation"

def covTruncFP_zeroNumerator (x : Nat) : Nat := 0 / x
#cov_assert_not covTruncFP_zeroNumerator "Integer Division Truncation"

-- ============================================================
-- List.range (TP / TN)
-- ============================================================

def covRangeTP (n : Nat) : List Nat := List.range n
#cov_assert_has covRangeTP "0-Indexed Range"

def covRangeTN (n : Nat) : List Nat := List.range' 1 n
#cov_assert_not covRangeTN "0-Indexed Range"

-- ============================================================
-- Axiom Checker (TP / TN / FP)
-- ============================================================

axiom covUserAxiomTP : ∀ n : Nat, n + 1 > n
#cov_assert_has covUserAxiomTP "Unsound Axiom"
#cov_assert_confidence covUserAxiomTP "Unsound Axiom" proven
#cov_assert_proved_by covUserAxiomTP "Unsound Axiom" "structural"

theorem covAxiomTN : 1 + 1 = 2 := rfl
#cov_assert_not covAxiomTN "Unsound Axiom"

axiom covAxiomFP_nonProp : Nat
#cov_assert_not covAxiomFP_nonProp "Unsound Axiom"

-- ============================================================
-- Vacuous Checker (TP / TN)
-- ============================================================

theorem covVacuousTP (n : Nat) (h : n < 0) : False := by omega
#cov_assert_has covVacuousTP "Vacuous Theorem"
#cov_assert_confidence covVacuousTP "Vacuous Theorem" proven

theorem covVacuousTN (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by omega
#cov_assert_not covVacuousTN "Vacuous Theorem"

-- ============================================================
-- Unused Binder (TP / TN / FP)
-- ============================================================

theorem covUnusedTP : ∀ (n : Nat), True := fun _ => trivial
#cov_assert_has covUnusedTP "Unused Quantified Variable"

theorem covUnusedTN : ∀ (n : Nat), n = n := fun n => rfl
#cov_assert_not covUnusedTN "Unused Quantified Variable"

theorem covUnusedFP_underscore : ∀ (_ : Nat), True := fun _ => trivial
#cov_assert_not covUnusedFP_underscore "Unused Quantified Variable"

-- ============================================================
-- Counterexample (TP / TN / FN-known-limit)
-- ============================================================

theorem covCexTP (n : Nat) : n = n + 1 := by sorry
#cov_assert_has covCexTP "Counterexample Found"
#cov_assert_confidence covCexTP "Counterexample Found" proven
#cov_assert_proved_by covCexTP "Counterexample Found" "decide"

theorem covCexTN (n : Nat) : n = n := by rfl
#cov_assert_not covCexTN "Counterexample Found"

-- Plausible fallback handles > 4 binders (exhaustive search limit)
theorem covCexFN_maxBinders (a b c d e : Nat) : a + b + c + d + e > 0 := by sorry
#cov_assert_has covCexFN_maxBinders "Counterexample Found"
#cov_assert_proved_by covCexFN_maxBinders "Counterexample Found" "plausible"

-- ============================================================
-- Cast After Truncation (TP / TN / FP)
-- ============================================================

def covCastTP (a b : Int) : Nat := (a / b).toNat
#cov_assert_has covCastTP "Cast After Truncation"

def covCastTN (a : Int) : Nat := a.toNat
#cov_assert_not covCastTN "Cast After Truncation"

def covCastFP_intSub (a b : Int) : Nat := (a - b).toNat
#cov_assert_not covCastFP_intSub "Cast After Truncation"

-- ============================================================
-- Exponent Truncation (TP / TN)
-- ============================================================

instance covHPowNatIntNat : HPow Nat Int Nat where
  hPow a b := if b < 0 then 0 else Nat.pow a b.toNat

def covExpTP (a : Nat) : Nat := a ^ (-1 : Int)
#cov_assert_has covExpTP "Exponent Truncation"
#cov_assert_confidence covExpTP "Exponent Truncation" proven

def covExpTN (a : Nat) : Nat := a ^ (2 : Int)
#cov_assert_not covExpTN "Exponent Truncation"

-- ============================================================
-- Analytic Domain (TP / TN / FP-known)
-- ============================================================

def covAnalyticTP (x : Rat) (h : x = 0) : Rat := x⁻¹
#cov_assert_has covAnalyticTP "Analytic Domain Totalization"
#cov_assert_confidence covAnalyticTP "Analytic Domain Totalization" proven
#cov_assert_proved_by covAnalyticTP "Analytic Domain Totalization" "assumption"

def covAnalyticTN (x : Rat) (h : x ≠ 0) : Rat := x⁻¹
#cov_assert_not covAnalyticTN "Analytic Domain Totalization"

-- Known FP currently accepted: inverse of non-zero literal still warns.
def covAnalyticFP_literal : Rat := (2 : Rat)⁻¹
#cov_assert_has covAnalyticFP_literal "Analytic Domain Totalization"

-- ============================================================
-- FN-known-gap (documented limitation)
-- ============================================================

def covKnownFN_natPred (n : Nat) : Nat := Nat.pred n
#cov_assert_count covKnownFN_natPred 0

end Coverage
