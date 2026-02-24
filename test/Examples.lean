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

/--
info: Analysis of bad_pred_succ:
──────────────────────────────────────────────────
[WARNING] bad_pred_succ: Truncated Nat Subtraction
  n - 1 has no guard ensuring 1 ≤ n
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : 1 ≤ n` or use Int instead of Nat

[ERROR] bad_pred_succ: Counterexample Found
  Counterexample found: [n := 0] makes proposition false
  Taxonomy: I.a - Specification Error
  Suggestion: The instantiated proposition `0 - 1 + 1 = 0` evaluates to false

──────────────────────────────────────────────────
Summary: 1 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp bad_pred_succ

/-- GOOD: Guarded with n > 0 -/
theorem good_pred_succ (n : Nat) (h : n > 0) : (n - 1) + 1 = n := by
  sorry

/-- info: ✓ good_pred_succ: No issues detected -/
#guard_msgs in #check_atp good_pred_succ

/-- BAD: Subtraction in wrong order -/
theorem bad_subtraction_order (a b : Nat) : a - b = b - a := by
  sorry

/--
info: Analysis of bad_subtraction_order:
──────────────────────────────────────────────────
[WARNING] bad_subtraction_order: Truncated Nat Subtraction
  a - b has no guard ensuring b ≤ a
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≤ a` or use Int instead of Nat

[WARNING] bad_subtraction_order: Truncated Nat Subtraction
  b - a has no guard ensuring a ≤ b
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : a ≤ b` or use Int instead of Nat

[ERROR] bad_subtraction_order: Counterexample Found
  Counterexample found: [a := 0, b := 1] makes proposition false
  Taxonomy: I.a - Specification Error
  Suggestion: The instantiated proposition `0 - 1 = 1 - 0` evaluates to false

──────────────────────────────────────────────────
Summary: 1 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp bad_subtraction_order

-- ═══════════════════════════════════════════════════════════════════
-- DIVISION BY ZERO EXAMPLES
-- ═══════════════════════════════════════════════════════════════════

/-- BAD: Unguarded division - false when n = 0 (since 0/0 = 0 ≠ 1) -/
theorem bad_div_self (n : Nat) : n / n = 1 := by
  sorry

/--
info: Analysis of bad_div_self:
──────────────────────────────────────────────────
[WARNING] bad_div_self: Potential Division by Zero
  n / n has no guard ensuring n ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : n ≠ 0` or `h : n > 0`

[WARNING] bad_div_self: Integer Division Truncation
  n / n may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

[ERROR] bad_div_self: Counterexample Found
  Counterexample found: [n := 0] makes proposition false
  Taxonomy: I.a - Specification Error
  Suggestion: The instantiated proposition `0 / 0 = 1` evaluates to false

──────────────────────────────────────────────────
Summary: 1 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp bad_div_self

/-- GOOD: Guarded with n > 0 -/
theorem good_div_self (n : Nat) (h : n > 0) : n / n = 1 := by
  sorry

/--
info: Analysis of good_div_self:
──────────────────────────────────────────────────
[WARNING] good_div_self: Integer Division Truncation
  n / n may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp good_div_self

/-- GOOD: Literal non-zero divisor -/
theorem div_by_two (n : Nat) : n / 2 * 2 ≤ n := by
  sorry

/--
info: Analysis of div_by_two:
──────────────────────────────────────────────────
[WARNING] div_by_two: Integer Division Truncation
  n / 2 may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp div_by_two

-- ═══════════════════════════════════════════════════════════════════
-- LIST.RANGE EXAMPLES
-- ═══════════════════════════════════════════════════════════════════

/-- SUSPICIOUS: Uses 0-indexed range for "sum of first n integers"
    List.range n = [0, 1, ..., n-1], not [1, 2, ..., n] -/
def sum_first_n_wrong (n : Nat) : Nat :=
  (List.range n).sum

/--
info: Analysis of sum_first_n_wrong:
──────────────────────────────────────────────────
[INFO] sum_first_n_wrong: 0-Indexed Range
  List.range n is 0-indexed: [0, 1, ..., n-1]
  Taxonomy: I.b - Goal Misalignment (potential)
  Suggestion: If you need [1, 2, ..., n], use List.range' 1 n or Finset.Icc 1 n

──────────────────────────────────────────────────
Summary: 0 error(s), 0 warning(s), 1 info(s)
-/
#guard_msgs in #check_atp sum_first_n_wrong

/-- BETTER: Uses range' to start from 1 -/
def sum_first_n_better (n : Nat) : Nat :=
  (List.range' 1 n).sum

/-- info: ✓ sum_first_n_better: No issues detected -/
#guard_msgs in #check_atp sum_first_n_better

-- ═══════════════════════════════════════════════════════════════════
-- COMBINED ISSUES
-- ═══════════════════════════════════════════════════════════════════

/-- BAD: Multiple issues - unguarded subtraction AND division -/
theorem bad_combined (a b : Nat) : (a - b) / b = a / b - 1 := by
  sorry

/--
info: Analysis of bad_combined:
──────────────────────────────────────────────────
[WARNING] bad_combined: Truncated Nat Subtraction
  a - b has no guard ensuring b ≤ a
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≤ a` or use Int instead of Nat

[WARNING] bad_combined: Truncated Nat Subtraction
  a / b - 1 has no guard ensuring 1 ≤ a / b
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : 1 ≤ a / b` or use Int instead of Nat

[WARNING] bad_combined: Potential Division by Zero
  a - b / b has no guard ensuring b ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≠ 0` or `h : b > 0`

[WARNING] bad_combined: Potential Division by Zero
  a / b has no guard ensuring b ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≠ 0` or `h : b > 0`

[WARNING] bad_combined: Integer Division Truncation
  a - b / b may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

[WARNING] bad_combined: Integer Division Truncation
  a / b may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 6 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp bad_combined

-- ═══════════════════════════════════════════════════════════════════
-- FALSE POSITIVE CHECKS (should not warn)
-- ═══════════════════════════════════════════════════════════════════

/-- Should not warn: subtracting 0 is always safe -/
theorem sub_zero (n : Nat) : n - 0 = n := by
  sorry

/-- info: ✓ sub_zero: No issues detected -/
#guard_msgs in #check_atp sub_zero

/-- Should not warn: division by literal 1 -/
theorem div_one (n : Nat) : n / 1 = n := by
  sorry

/--
info: ✓ div_one: No issues detected
-/
#guard_msgs in #check_atp div_one
