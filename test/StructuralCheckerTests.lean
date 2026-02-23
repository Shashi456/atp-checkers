/-
  Structural Checker Tests

  Axiom checker, vacuous hypotheses, empty domain vacuity,
  unused binder, and list/finset range checks.
-/

import AtpLinter
import Mathlib.Data.Finset.Basic
set_option linter.unusedVariables false

namespace StructuralChecker

-- ============================================================
-- Axiom Checker
-- ============================================================

-- Should flag: user axiom asserting a Prop
axiom myFakeTheorem : ∀ n : Nat, n + 1 > n
#check_atp myFakeTheorem

-- Should NOT flag: actual proof
theorem actualProof : 1 + 1 = 2 := rfl
#check_atp actualProof

-- ============================================================
-- Vacuous Hypotheses
-- ============================================================

-- Should flag: n < 0 is impossible for Nat
theorem vacuousNatNegative (n : Nat) (h : n < 0) : False := by omega
#check_atp vacuousNatNegative

-- Should flag: contradictory bounds
theorem vacuousContradictoryBounds (a b : Nat) (h1 : a < b) (h2 : b ≤ a) : 1 = 2 := by omega
#check_atp vacuousContradictoryBounds

-- Should NOT flag: consistent hypotheses
theorem nonVacuous (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by omega
#check_atp nonVacuous

-- Should flag: explicit False hypothesis (trivially vacuous)
theorem explicitFalse (h : False) : 1 = 2 := False.elim h
#check_atp explicitFalse

-- ============================================================
-- Empty Domain Vacuity
-- ============================================================

-- Fin 0 is empty - should detect vacuity
theorem fin0_vacuous : ∀ x : Fin 0, x.val < 100 := by
  intro x
  exact Fin.elim0 x
#check_atp fin0_vacuous

-- Empty type is empty - should detect vacuity
theorem empty_vacuous : ∀ x : Empty, True := by
  intro x
  exact Empty.elim x
#check_atp empty_vacuous

-- PEmpty is empty - should detect vacuity
theorem pempty_vacuous : ∀ x : PEmpty, True := by
  intro x
  exact PEmpty.elim x
#check_atp pempty_vacuous

-- Subtype with impossible predicate (n : Nat with n < 0)
theorem subtype_impossible : ∀ x : { n : Nat // n < 0 }, True := by
  intro ⟨n, h⟩
  omega
#check_atp subtype_impossible

-- Fin n with n > 0 should NOT be flagged
theorem fin_nonempty (n : Nat) (hn : n > 0) : ∀ x : Fin n, x.val < n := by
  intro x
  exact x.isLt
#check_atp fin_nonempty

-- Contradictory hypotheses (existing vacuity check)
theorem hyp_contradict (n : Nat) (h1 : n < 0) : True := by
  omega
#check_atp hyp_contradict

-- Normal theorem - should NOT be flagged
theorem normal_theorem (n : Nat) (h : n > 0) : n ≥ 1 := by
  omega
#check_atp normal_theorem

-- ============================================================
-- Unused Binder
-- ============================================================

-- Should flag: p is never used
theorem unusedExistential : ∃ (p q : Nat), q > 0 := ⟨0, 1, Nat.one_pos⟩
#check_atp unusedExistential

-- Should flag: n is never used
theorem unusedUniversal : ∀ (n : Nat), True := fun _ => trivial
#check_atp unusedUniversal

-- Should NOT flag: n is used
theorem usedUniversal : ∀ (n : Nat), n ≥ 0 := fun n => Nat.zero_le n
#check_atp usedUniversal

-- Should NOT flag: explicit underscore (user intended unused)
theorem explicitUnderscore : ∀ (_ : Nat), True := fun _ => trivial
#check_atp explicitUnderscore

-- Should NOT flag: proof hypothesis (Prop-typed binder)
theorem proofHypothesis (n : Nat) (h : n > 0) : n > 0 := h
#check_atp proofHypothesis

-- ============================================================
-- List/Finset Range
-- ============================================================

-- 0-indexed: List.range
def listRange0 (n : Nat) : List Nat := List.range n
#check_atp listRange0

-- "safer" start: List.range'
def listRange1 (n : Nat) : List Nat := List.range' 1 n
#check_atp listRange1

-- 0-indexed: Finset.range
def finsetRange0 (n : Nat) : Finset Nat := Finset.range n
#check_atp finsetRange0

end StructuralChecker
