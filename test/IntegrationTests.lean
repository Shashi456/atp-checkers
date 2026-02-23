/-
  Integration Tests

  Cross-checker, batch, deduplication, and integration tests.
-/

import AtpLinter
set_option linter.unusedVariables false

namespace Integration

-- ============================================================
-- Prop-Skip / Type-Only Analysis
-- ============================================================

-- This theorem has a division in its statement - should be flagged
theorem divInStatement (x y : Nat) : x / y = x / y := rfl
#check_atp divInStatement

-- This def has a division in its body - should be flagged
def divInBody (x : Nat) : Nat := x / 2
#check_atp divInBody

-- A theorem with clean statement but messy proof - should report no issues
theorem cleanStatement (n : Nat) : n = n := by
  rfl
#check_atp cleanStatement

-- ============================================================
-- Batch Check (#check_atp_all)
-- ============================================================

/-- Test definition with integer division truncation -/
def badDiv : Nat := 1 / 4

/-- Test definition that's clean -/
def goodDef : Nat := 2 + 2

/-- Test with potential truncation -/
def maybeBad (x : Nat) : Nat := x / 3

#check_atp_all

-- ============================================================
-- Deduplication
-- ============================================================

/--
Same division expression in two branches: one guarded, one not.
If deduplication hides the unguarded one, this is a bug.

Expected: Should warn about the unguarded division in else branch.
-/
def dedupTest_diteBranches (a b : Nat) : Nat :=
  if h : b ≠ 0 then
    a / b  -- guarded by h
  else
    a / b  -- NOT guarded (h : ¬(b ≠ 0) = h : b = 0)
#check_atp dedupTest_diteBranches

/--
Division appears in both type and body with different contexts.

Expected: Should warn for type occurrence (guard after).
-/
def dedupTest_typeAndBody (a b : Nat) (x : Fin (a / b)) (hb : b ≠ 0) : Nat :=
  a / b  -- body occurrence - hb IS in scope here
#check_atp dedupTest_typeAndBody

-- ============================================================
-- Type-Specific Edge Cases
-- ============================================================

/-- Actual: no warnings. Fin division doesn't use Nat.div internally, so DivisionByZero doesn't fire. -/
def finDivision (n : Nat) (a b : Fin (n + 1)) (hb : b ≠ 0) : Fin (n + 1) := a / b
#check_atp finDivision

/-- Generic division (no concrete type). mkZeroOf may fail. -/
def genericDiv {α : Type} [HDiv α α α] [OfNat α 0] (a b : α) : α := a / b
#check_atp genericDiv

-- ============================================================
-- Prop-valued Definitions
-- ============================================================

/-
Actual: warns DivisionByZero + IntDivTruncation.
Prop-valued *definitions* are analyzed (only theorem *proof terms* are skipped).
-/
def propValuedDefWithDiv (x y : Nat) : Prop := (x / y = x)
#check_atp propValuedDefWithDiv

-- ============================================================
-- Multiple Issues in One Declaration
-- ============================================================

-- ATP linter flags: DivisionByZero + IntDivTruncation. (Unused n is flagged by Lean's built-in linter, not ATP.)
def multipleIssues (n a b : Nat) : Nat := a / b
#check_atp multipleIssues

-- ============================================================
-- Cross-checker Combined
-- ============================================================

-- Both empty domain AND another issue
theorem combined_vacuous_div : ∀ x : Fin 0, ∀ n : Nat, n / 0 = 0 := by
  intro x
  exact Fin.elim0 x
#check_atp combined_vacuous_div

end Integration
