/-
  Simple examples demonstrating ATP linter detection on definitions.
-/

import AtpLinter
import TestAssertions

-- ═══════════════════════════════════════════════════════════════════
-- DEFINITION-BASED EXAMPLES (work better than theorems)
-- ═══════════════════════════════════════════════════════════════════

/-- BAD: Uses 0-indexed List.range -/
def wrongSum (n : Nat) : Nat :=
  (List.range n).sum

/--
info: Analysis of wrongSum:
──────────────────────────────────────────────────
[INFO] wrongSum: 0-Indexed Range
  List.range n is 0-indexed: [0, 1, ..., n-1]
  Taxonomy: I.b - Goal Misalignment (potential)
  Suggestion: If you need [1, 2, ..., n], use List.range' 1 n or Finset.Icc 1 n

──────────────────────────────────────────────────
Summary: 0 error(s), 0 warning(s), 1 info(s)
-/
#guard_msgs in #check_atp wrongSum
#cov_assert_has wrongSum "0-Indexed Range"

/-- GOOD: Uses List.range' starting at 1 -/
def correctSum (n : Nat) : Nat :=
  (List.range' 1 n).sum

/-- info: ✓ correctSum: No issues detected -/
#guard_msgs in #check_atp correctSum
#cov_assert_count correctSum 0

/-- No DivisionByZero (2 is nonzero). IntDivTruncation: warns (n/2 may truncate). -/
def halfOf (n : Nat) : Nat :=
  n / 2

/--
info: Analysis of halfOf:
──────────────────────────────────────────────────
[WARNING] halfOf: Integer Division Truncation
  n / 2 may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp halfOf
#cov_assert_has halfOf "Integer Division Truncation"
#cov_assert_not halfOf "Potential Division by Zero"

/-- Division by parameter - flagged -/
def divideBy (n d : Nat) : Nat :=
  n / d

/--
info: Analysis of divideBy:
──────────────────────────────────────────────────
[WARNING] divideBy: Potential Division by Zero
  n / d has no guard ensuring d ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : d ≠ 0` or `h : d > 0`

[WARNING] divideBy: Integer Division Truncation
  n / d may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp divideBy
#cov_assert_has divideBy "Potential Division by Zero"

/-- Subtraction - will be flagged -/
def subtract (a b : Nat) : Nat :=
  a - b

/--
info: Analysis of subtract:
──────────────────────────────────────────────────
[WARNING] subtract: Truncated Nat Subtraction
  a - b has no guard ensuring b ≤ a
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≤ a` or use Int instead of Nat

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp subtract
#cov_assert_has subtract "Truncated Nat Subtraction"
