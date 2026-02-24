/-
  Structural Checker Tests

  Axiom checker, vacuous hypotheses, empty domain vacuity,
  unused binder, and list/finset range checks.
-/

import AtpLinter
import TestAssertions
import Mathlib.Data.Finset.Basic
set_option linter.unusedVariables false

namespace StructuralChecker

-- ============================================================
-- Axiom Checker
-- ============================================================

-- Should flag: user axiom asserting a Prop
axiom myFakeTheorem : ∀ n : Nat, n + 1 > n
/--
info: Analysis of StructuralChecker.myFakeTheorem:
──────────────────────────────────────────────────
[ERROR] StructuralChecker.myFakeTheorem: Unsound Axiom
  Declaration uses `axiom` instead of `theorem` - this asserts without proof
  Taxonomy: I.c - Unproven Statement
  Suggestion: Replace with `theorem ... := by sorry` if unproven, or provide an actual proof

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp myFakeTheorem
#cov_assert_has myFakeTheorem "Unsound Axiom"

-- Should NOT flag: actual proof
theorem actualProof : 1 + 1 = 2 := rfl
/-- info: ✓ StructuralChecker.actualProof: No issues detected -/
#guard_msgs in #check_atp actualProof
#cov_assert_not actualProof "Unsound Axiom"

-- ============================================================
-- Vacuous Hypotheses
-- ============================================================

-- Should flag: n < 0 is impossible for Nat
theorem vacuousNatNegative (n : Nat) (h : n < 0) : False := by omega
/--
info: Analysis of StructuralChecker.vacuousNatNegative:
──────────────────────────────────────────────────
[ERROR] StructuralChecker.vacuousNatNegative: Vacuous Theorem
  Hypotheses are contradictory (proved by omega)
  Potentially relevant: h : n < 0
  Taxonomy: I.a - Specification Error
  Suggestion: Check inequality directions and type constraints

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp vacuousNatNegative
#cov_assert_has vacuousNatNegative "Vacuous Theorem"

-- Should flag: contradictory bounds
theorem vacuousContradictoryBounds (a b : Nat) (h1 : a < b) (h2 : b ≤ a) : 1 = 2 := by omega
/--
info: Analysis of StructuralChecker.vacuousContradictoryBounds:
──────────────────────────────────────────────────
[ERROR] StructuralChecker.vacuousContradictoryBounds: Vacuous Theorem
  Hypotheses are contradictory (proved by omega)
  Potentially relevant: h1 : a < b, h2 : b ≤ a
  Taxonomy: I.a - Specification Error
  Suggestion: Check inequality directions and type constraints

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp vacuousContradictoryBounds
#cov_assert_has vacuousContradictoryBounds "Vacuous Theorem"

-- Should NOT flag: consistent hypotheses
theorem nonVacuous (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by omega
/-- info: ✓ StructuralChecker.nonVacuous: No issues detected -/
#guard_msgs in #check_atp nonVacuous
#cov_assert_not nonVacuous "Vacuous Theorem"

-- Should flag: explicit False hypothesis (trivially vacuous)
theorem explicitFalse (h : False) : 1 = 2 := False.elim h
/--
info: Analysis of StructuralChecker.explicitFalse:
──────────────────────────────────────────────────
[ERROR] StructuralChecker.explicitFalse: Vacuous Theorem
  Hypotheses are contradictory (proved by assumption)
  Potentially relevant: h : False
  Taxonomy: I.a - Specification Error
  Suggestion: Check inequality directions and type constraints

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp explicitFalse

-- ============================================================
-- Empty Domain Vacuity
-- ============================================================

-- Fin 0 is empty - should detect vacuity
theorem fin0_vacuous : ∀ x : Fin 0, x.val < 100 := by
  intro x
  exact Fin.elim0 x
/--
info: Analysis of StructuralChecker.fin0_vacuous:
──────────────────────────────────────────────────
[ERROR] StructuralChecker.fin0_vacuous: Vacuous Theorem
  Quantified over empty domain: 'x' has type Fin 0 (Fin 0 has no elements)
  Taxonomy: I.a - Specification Error
  Suggestion: Check bounds - domain should likely be non-empty (e.g., Fin n with n > 0)

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp fin0_vacuous

-- Empty type is empty - should detect vacuity
theorem empty_vacuous : ∀ x : Empty, True := by
  intro x
  exact Empty.elim x
/--
info: Analysis of StructuralChecker.empty_vacuous:
──────────────────────────────────────────────────
[ERROR] StructuralChecker.empty_vacuous: Vacuous Theorem
  Quantified over empty domain: 'x' has type Empty (Empty type)
  Taxonomy: I.a - Specification Error
  Suggestion: Check bounds - domain should likely be non-empty (e.g., Fin n with n > 0)

[WARNING] StructuralChecker.empty_vacuous: Unused Quantified Variable
  ∀ x : Empty is bound but never used in body
  Taxonomy: I.a - Specification Error
  Suggestion: Remove unused variable or use it in the statement

──────────────────────────────────────────────────
Summary: 1 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp empty_vacuous

-- PEmpty is empty - should detect vacuity
theorem pempty_vacuous : ∀ x : PEmpty, True := by
  intro x
  exact PEmpty.elim x
/--
info: Analysis of StructuralChecker.pempty_vacuous:
──────────────────────────────────────────────────
[ERROR] StructuralChecker.pempty_vacuous: Vacuous Theorem
  Quantified over empty domain: 'x' has type PEmpty.{u_1} (PEmpty type)
  Taxonomy: I.a - Specification Error
  Suggestion: Check bounds - domain should likely be non-empty (e.g., Fin n with n > 0)

[WARNING] StructuralChecker.pempty_vacuous: Unused Quantified Variable
  ∀ x : PEmpty.{u_1} is bound but never used in body
  Taxonomy: I.a - Specification Error
  Suggestion: Remove unused variable or use it in the statement

──────────────────────────────────────────────────
Summary: 1 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp pempty_vacuous

-- Subtype with impossible predicate (n : Nat with n < 0)
theorem subtype_impossible : ∀ x : { n : Nat // n < 0 }, True := by
  intro ⟨n, h⟩
  omega
/--
info: Analysis of StructuralChecker.subtype_impossible:
──────────────────────────────────────────────────
[ERROR] StructuralChecker.subtype_impossible: Vacuous Theorem
  Quantified over empty domain: 'x' has type { n // n < 0 } (subtype predicate is never satisfied)
  Taxonomy: I.a - Specification Error
  Suggestion: Check bounds - domain should likely be non-empty (e.g., Fin n with n > 0)

[WARNING] StructuralChecker.subtype_impossible: Unused Quantified Variable
  ∀ x : { n // n < 0 } is bound but never used in body
  Taxonomy: I.a - Specification Error
  Suggestion: Remove unused variable or use it in the statement

──────────────────────────────────────────────────
Summary: 1 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp subtype_impossible

-- Fin n with n > 0 should NOT be flagged
theorem fin_nonempty (n : Nat) (hn : n > 0) : ∀ x : Fin n, x.val < n := by
  intro x
  exact x.isLt
/-- info: ✓ StructuralChecker.fin_nonempty: No issues detected -/
#guard_msgs in #check_atp fin_nonempty

-- Contradictory hypotheses (existing vacuity check)
theorem hyp_contradict (n : Nat) (h1 : n < 0) : True := by
  omega
/--
info: Analysis of StructuralChecker.hyp_contradict:
──────────────────────────────────────────────────
[ERROR] StructuralChecker.hyp_contradict: Vacuous Theorem
  Hypotheses are contradictory (proved by omega)
  Potentially relevant: h1 : n < 0
  Taxonomy: I.a - Specification Error
  Suggestion: Check inequality directions and type constraints

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp hyp_contradict

-- Normal theorem - should NOT be flagged
theorem normal_theorem (n : Nat) (h : n > 0) : n ≥ 1 := by
  omega
/-- info: ✓ StructuralChecker.normal_theorem: No issues detected -/
#guard_msgs in #check_atp normal_theorem

-- ============================================================
-- Unused Binder
-- ============================================================

-- Should flag: p is never used
theorem unusedExistential : ∃ (p q : Nat), q > 0 := ⟨0, 1, Nat.one_pos⟩
/--
info: Analysis of StructuralChecker.unusedExistential:
──────────────────────────────────────────────────
[WARNING] StructuralChecker.unusedExistential: Unused Quantified Variable
  λ p : ℕ is bound but never used in body
  Taxonomy: I.a - Specification Error
  Suggestion: Remove unused variable or use it in the statement

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp unusedExistential
#cov_assert_has unusedExistential "Unused Quantified Variable"

-- Should flag: n is never used
theorem unusedUniversal : ∀ (n : Nat), True := fun _ => trivial
/--
info: Analysis of StructuralChecker.unusedUniversal:
──────────────────────────────────────────────────
[WARNING] StructuralChecker.unusedUniversal: Unused Quantified Variable
  ∀ n : ℕ is bound but never used in body
  Taxonomy: I.a - Specification Error
  Suggestion: Remove unused variable or use it in the statement

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp unusedUniversal
#cov_assert_has unusedUniversal "Unused Quantified Variable"

-- Should NOT flag: n is used
theorem usedUniversal : ∀ (n : Nat), n ≥ 0 := fun n => Nat.zero_le n
/-- info: ✓ StructuralChecker.usedUniversal: No issues detected -/
#guard_msgs in #check_atp usedUniversal
#cov_assert_not usedUniversal "Unused Quantified Variable"

-- Should NOT flag: explicit underscore (user intended unused)
theorem explicitUnderscore : ∀ (_ : Nat), True := fun _ => trivial
/-- info: ✓ StructuralChecker.explicitUnderscore: No issues detected -/
#guard_msgs in #check_atp explicitUnderscore

-- Should NOT flag: proof hypothesis (Prop-typed binder)
theorem proofHypothesis (n : Nat) (h : n > 0) : n > 0 := h
/-- info: ✓ StructuralChecker.proofHypothesis: No issues detected -/
#guard_msgs in #check_atp proofHypothesis

-- ============================================================
-- List/Finset Range
-- ============================================================

-- 0-indexed: List.range
def listRange0 (n : Nat) : List Nat := List.range n
/--
info: Analysis of StructuralChecker.listRange0:
──────────────────────────────────────────────────
[INFO] StructuralChecker.listRange0: 0-Indexed Range
  List.range n is 0-indexed: [0, 1, ..., n-1]
  Taxonomy: I.b - Goal Misalignment (potential)
  Suggestion: If you need [1, 2, ..., n], use List.range' 1 n or Finset.Icc 1 n

──────────────────────────────────────────────────
Summary: 0 error(s), 0 warning(s), 1 info(s)
-/
#guard_msgs in #check_atp listRange0
#cov_assert_has listRange0 "0-Indexed Range"

-- "safer" start: List.range'
def listRange1 (n : Nat) : List Nat := List.range' 1 n
/-- info: ✓ StructuralChecker.listRange1: No issues detected -/
#guard_msgs in #check_atp listRange1
#cov_assert_not listRange1 "0-Indexed Range"

-- 0-indexed: Finset.range
def finsetRange0 (n : Nat) : Finset Nat := Finset.range n
/--
info: Analysis of StructuralChecker.finsetRange0:
──────────────────────────────────────────────────
[INFO] StructuralChecker.finsetRange0: 0-Indexed Range
  Finset.range n is 0-indexed: [0, 1, ..., n-1]
  Taxonomy: I.b - Goal Misalignment (potential)
  Suggestion: If you need [1, 2, ..., n], use List.range' 1 n or Finset.Icc 1 n

──────────────────────────────────────────────────
Summary: 0 error(s), 0 warning(s), 1 info(s)
-/
#guard_msgs in #check_atp finsetRange0
#cov_assert_has finsetRange0 "0-Indexed Range"

-- ============================================================
-- Axiom Checker: Classical.* Namespace
-- ============================================================

/-- User axiom in Classical namespace should still be flagged -/
axiom Classical.fake : 1 = 2
/--
info: Analysis of StructuralChecker.Classical.fake:
──────────────────────────────────────────────────
[ERROR] StructuralChecker.Classical.fake: Unsound Axiom
  Declaration uses `axiom` instead of `theorem` - this asserts without proof
  Taxonomy: I.c - Unproven Statement
  Suggestion: Replace with `theorem ... := by sorry` if unproven, or provide an actual proof

[ERROR] StructuralChecker.Classical.fake: Counterexample Found
  Counterexample found: [] makes proposition false
  Taxonomy: I.a - Specification Error
  Suggestion: The instantiated proposition `1 = 2` evaluates to false

──────────────────────────────────────────────────
Summary: 2 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp Classical.fake

end StructuralChecker
