/-
  Test examples for the ATP Linter

  These examples demonstrate the kinds of issues the linter detects.
-/

import AtpLinter

-- ═══════════════════════════════════════════════════════════════════
-- TRUNCATED NAT SUBTRACTION EXAMPLES
-- ═══════════════════════════════════════════════════════════════════

/-- BAD: Unguarded Nat subtraction - false when n = 0 -/
theorem bad_pred_succ (n : Nat) : (n - 1) + 1 = n := by
  sorry

#check_atp bad_pred_succ

/-- GOOD: Guarded with n > 0 -/
theorem good_pred_succ (n : Nat) (h : n > 0) : (n - 1) + 1 = n := by
  sorry

#check_atp good_pred_succ

/-- BAD: Subtraction in wrong order -/
theorem bad_subtraction_order (a b : Nat) : a - b = b - a := by
  sorry

#check_atp bad_subtraction_order

-- ═══════════════════════════════════════════════════════════════════
-- DIVISION BY ZERO EXAMPLES
-- ═══════════════════════════════════════════════════════════════════

/-- BAD: Unguarded division - false when n = 0 (since 0/0 = 0 ≠ 1) -/
theorem bad_div_self (n : Nat) : n / n = 1 := by
  sorry

#check_atp bad_div_self

/-- GOOD: Guarded with n > 0 -/
theorem good_div_self (n : Nat) (h : n > 0) : n / n = 1 := by
  sorry

#check_atp good_div_self

/-- GOOD: Literal non-zero divisor -/
theorem div_by_two (n : Nat) : n / 2 * 2 ≤ n := by
  sorry

#check_atp div_by_two

-- ═══════════════════════════════════════════════════════════════════
-- LIST.RANGE EXAMPLES
-- ═══════════════════════════════════════════════════════════════════

/-- SUSPICIOUS: Uses 0-indexed range for "sum of first n integers"
    List.range n = [0, 1, ..., n-1], not [1, 2, ..., n] -/
def sum_first_n_wrong (n : Nat) : Nat :=
  (List.range n).sum

#check_atp sum_first_n_wrong

/-- BETTER: Uses range' to start from 1 -/
def sum_first_n_better (n : Nat) : Nat :=
  (List.range' 1 n).sum

#check_atp sum_first_n_better

-- ═══════════════════════════════════════════════════════════════════
-- COMBINED ISSUES
-- ═══════════════════════════════════════════════════════════════════

/-- BAD: Multiple issues - unguarded subtraction AND division -/
theorem bad_combined (a b : Nat) : (a - b) / b = a / b - 1 := by
  sorry

#check_atp bad_combined

-- ═══════════════════════════════════════════════════════════════════
-- FALSE POSITIVE CHECKS (should not warn)
-- ═══════════════════════════════════════════════════════════════════

/-- Should not warn: subtracting 0 is always safe -/
theorem sub_zero (n : Nat) : n - 0 = n := by
  sorry

#check_atp sub_zero

/-- Should not warn: division by literal 1 -/
theorem div_one (n : Nat) : n / 1 = n := by
  sorry

#check_atp div_one
