/-
  Simple examples demonstrating ATP linter detection on definitions.
-/

import AtpLinter

-- ═══════════════════════════════════════════════════════════════════
-- DEFINITION-BASED EXAMPLES (work better than theorems)
-- ═══════════════════════════════════════════════════════════════════

/-- BAD: Uses 0-indexed List.range -/
def wrongSum (n : Nat) : Nat :=
  (List.range n).sum

#check_atp wrongSum
-- Expected: INFO about List.range being 0-indexed

/-- GOOD: Uses List.range' starting at 1 -/
def correctSum (n : Nat) : Nat :=
  (List.range' 1 n).sum

#check_atp correctSum
-- Expected: No issues

/-- No DivisionByZero (2 is nonzero). IntDivTruncation: warns (n/2 may truncate). -/
def halfOf (n : Nat) : Nat :=
  n / 2

#check_atp halfOf

/-- Division by parameter - flagged -/
def divideBy (n d : Nat) : Nat :=
  n / d

#check_atp divideBy
-- Expected: WARNING about d potentially being 0

/-- Subtraction - will be flagged -/
def subtract (a b : Nat) : Nat :=
  a - b

#check_atp subtract
-- Expected: WARNING about truncated subtraction
