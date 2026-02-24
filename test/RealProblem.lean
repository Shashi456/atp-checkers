import AtpLinter
import TestAssertions

-- The actual problem (simplified without Mathlib Set notation)
-- This demonstrates the truncated subtraction issue

/-- The problematic expression: b^2 - 4*b + 5 on Nat -/
def problematicExpr (b : Nat) : Nat :=
  b^2 - 4 * b + 5

/--
info: Analysis of problematicExpr:
──────────────────────────────────────────────────
[WARNING] problematicExpr: Truncated Nat Subtraction
  b ^ 2 - 4 * b has no guard ensuring 4 * b ≤ b ^ 2
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : 4 * b ≤ b ^ 2` or use Int instead of Nat

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp problematicExpr
#cov_assert_has problematicExpr "Truncated Nat Subtraction"
