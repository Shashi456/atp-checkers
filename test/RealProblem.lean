import AtpLinter

-- The actual problem (simplified without Mathlib Set notation)
-- This demonstrates the truncated subtraction issue

/-- The problematic expression: b^2 - 4*b + 5 on Nat -/
def problematicExpr (b : Nat) : Nat :=
  b^2 - 4 * b + 5

#check_atp problematicExpr

-- Let's verify the truncation manually
#eval problematicExpr 1  -- Expected: 5 (not 2!) because 1 - 4 = 0
#eval problematicExpr 2  -- Expected: 5 (not 1!) because 4 - 8 = 0
#eval problematicExpr 3  -- Expected: 5 (not 2!) because 9 - 12 = 0
#eval problematicExpr 4  -- Expected: 5 (correct: 16 - 16 = 0)
#eval problematicExpr 5  -- Expected: 10 (correct: 25 - 20 = 5)
