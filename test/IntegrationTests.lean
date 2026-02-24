/-
  Integration Tests

  Cross-checker, batch, deduplication, and integration tests.
-/

import AtpLinter
import TestAssertions
set_option linter.unusedVariables false

namespace Integration

-- ============================================================
-- Prop-Skip / Type-Only Analysis
-- ============================================================

-- This theorem has a division in its statement - should be flagged
theorem divInStatement (x y : Nat) : x / y = x / y := rfl
/--
info: Analysis of Integration.divInStatement:
──────────────────────────────────────────────────
[WARNING] Integration.divInStatement: Potential Division by Zero
  x / y has no guard ensuring y ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : y ≠ 0` or `h : y > 0`

[WARNING] Integration.divInStatement: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp divInStatement

-- This def has a division in its body - should be flagged
def divInBody (x : Nat) : Nat := x / 2
/--
info: Analysis of Integration.divInBody:
──────────────────────────────────────────────────
[WARNING] Integration.divInBody: Integer Division Truncation
  x / 2 may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp divInBody

-- A theorem with clean statement but messy proof - should report no issues
theorem cleanStatement (n : Nat) : n = n := by
  rfl
/-- info: ✓ Integration.cleanStatement: No issues detected -/
#guard_msgs in #check_atp cleanStatement

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
/--
info: Analysis of Integration.dedupTest_diteBranches:
──────────────────────────────────────────────────
[WARNING] Integration.dedupTest_diteBranches: Potential Division by Zero
  a / b has no guard ensuring b ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≠ 0` or `h : b > 0`

[WARNING] Integration.dedupTest_diteBranches: Integer Division Truncation
  a / b may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp dedupTest_diteBranches

/--
Division appears in both type and body with different contexts.

Expected: hb guards the division in both type and body (full-scope).
Only IntDivTruncation fires.
-/
def dedupTest_typeAndBody (a b : Nat) (x : Fin (a / b)) (hb : b ≠ 0) : Nat :=
  a / b  -- body occurrence - hb IS in scope here
/--
info: Analysis of Integration.dedupTest_typeAndBody:
──────────────────────────────────────────────────
[WARNING] Integration.dedupTest_typeAndBody: Integer Division Truncation
  a / b may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp dedupTest_typeAndBody

-- ============================================================
-- Type-Specific Edge Cases
-- ============================================================

/-- Actual: no warnings. Fin division doesn't use Nat.div internally, so DivisionByZero doesn't fire. -/
def finDivision (n : Nat) (a b : Fin (n + 1)) (hb : b ≠ 0) : Fin (n + 1) := a / b
/-- info: ✓ Integration.finDivision: No issues detected -/
#guard_msgs in #check_atp finDivision

/-- Generic division (no concrete type). mkZeroOf may fail. -/
def genericDiv {α : Type} [HDiv α α α] [OfNat α 0] (a b : α) : α := a / b
/--
info: Analysis of Integration.genericDiv:
──────────────────────────────────────────────────
[WARNING] Integration.genericDiv: Potential Division by Zero
  a / b has no guard ensuring b ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≠ 0` or `h : b > 0`

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp genericDiv

-- ============================================================
-- Prop-valued Definitions
-- ============================================================

/-
Actual: warns DivisionByZero + IntDivTruncation.
Prop-valued *definitions* are analyzed (only theorem *proof terms* are skipped).
-/
def propValuedDefWithDiv (x y : Nat) : Prop := (x / y = x)
/--
info: Analysis of Integration.propValuedDefWithDiv:
──────────────────────────────────────────────────
[WARNING] Integration.propValuedDefWithDiv: Potential Division by Zero
  x / y has no guard ensuring y ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : y ≠ 0` or `h : y > 0`

[WARNING] Integration.propValuedDefWithDiv: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp propValuedDefWithDiv

-- ============================================================
-- Multiple Issues in One Declaration
-- ============================================================

-- ATP linter flags: DivisionByZero + IntDivTruncation. (Unused n is flagged by Lean's built-in linter, not ATP.)
def multipleIssues (n a b : Nat) : Nat := a / b
/--
info: Analysis of Integration.multipleIssues:
──────────────────────────────────────────────────
[WARNING] Integration.multipleIssues: Potential Division by Zero
  a / b has no guard ensuring b ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≠ 0` or `h : b > 0`

[WARNING] Integration.multipleIssues: Integer Division Truncation
  a / b may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp multipleIssues

-- ============================================================
-- Cross-checker Combined
-- ============================================================

-- Both empty domain AND another issue
theorem combined_vacuous_div : ∀ x : Fin 0, ∀ n : Nat, n / 0 = 0 := by
  intro x
  exact Fin.elim0 x
/--
info: Analysis of Integration.combined_vacuous_div:
──────────────────────────────────────────────────
[ERROR] Integration.combined_vacuous_div: Potential Division by Zero
  n / 0 divides by literal zero!
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: This is definitely division by zero - the divisor is 0

[ERROR] Integration.combined_vacuous_div: Vacuous Theorem
  Quantified over empty domain: 'x' has type Fin 0 (Fin 0 has no elements)
  Taxonomy: I.a - Specification Error
  Suggestion: Check bounds - domain should likely be non-empty (e.g., Fin n with n > 0)

[WARNING] Integration.combined_vacuous_div: Unused Quantified Variable
  ∀ x : Fin 0 is bound but never used in body
  Taxonomy: I.a - Specification Error
  Suggestion: Remove unused variable or use it in the statement

──────────────────────────────────────────────────
Summary: 2 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp combined_vacuous_div

-- ============================================================
-- Dedup Finding Count Assertions
-- ============================================================

/-- HDiv.hDiv and Nat.div fire on the same expression.
    Dedup merges into 1 division finding + 1 truncation finding = 2 total.
    With h : b = 0, unsafety proof upgrades division to proven. -/
def dedupBugDiv (a b : Nat) (h : b = 0) : Nat := a / b
/--
info: Analysis of Integration.dedupBugDiv:
──────────────────────────────────────────────────
[WARNING] Integration.dedupBugDiv: Potential Division by Zero
  a / b has no guard ensuring b ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≠ 0` or `h : b > 0`

[WARNING] Integration.dedupBugDiv: Integer Division Truncation
  a / b may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp dedupBugDiv
#cov_assert_count dedupBugDiv 2

/-- HMod.hMod and Nat.mod fire on the same expression.
    Dedup merges into exactly 1 modulo finding. -/
def dedupBugMod (a b : Nat) (h : b = 0) : Nat := a % b
/--
info: Analysis of Integration.dedupBugMod:
──────────────────────────────────────────────────
[WARNING] Integration.dedupBugMod: Modulo Edge Case
  a % b has no guard ensuring b ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≠ 0`. Note: in Lean, n % 0 = n

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp dedupBugMod
#cov_assert_count dedupBugMod 1

/-- Division with no unsafety evidence — 1 division + 1 truncation = 2 findings. -/
def dedupBugDivMaybe (a b : Nat) : Nat := a / b
/--
info: Analysis of Integration.dedupBugDivMaybe:
──────────────────────────────────────────────────
[WARNING] Integration.dedupBugDivMaybe: Potential Division by Zero
  a / b has no guard ensuring b ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≠ 0` or `h : b > 0`

[WARNING] Integration.dedupBugDivMaybe: Integer Division Truncation
  a / b may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp dedupBugDivMaybe
#cov_assert_count dedupBugDivMaybe 2

-- ============================================================
-- Regression: #check_atp_all must not skip proof_* names
-- ============================================================

-- Verify #check_atp_all doesn't skip proof_* names
def proof_user (a b : Nat) : Nat := a / b
/--
info: Analysis of Integration.proof_user:
──────────────────────────────────────────────────
[WARNING] Integration.proof_user: Potential Division by Zero
  a / b has no guard ensuring b ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≠ 0` or `h : b > 0`

[WARNING] Integration.proof_user: Integer Division Truncation
  a / b may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp proof_user
#cov_assert_count proof_user 2

-- ============================================================
-- Regression: Int.natAbs must not suppress Int.toNat findings
-- ============================================================

-- Verify Int.natAbs doesn't suppress Int.toNat findings
def intToNatDedupBug (a : Int) : Nat := Int.natAbs a + Int.toNat a
/--
info: Analysis of Integration.intToNatDedupBug:
──────────────────────────────────────────────────
[WARNING] Integration.intToNatDedupBug: Unguarded Int.toNat
  Int.toNat (a) has no guard ensuring (a) ≥ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : a ≥ 0` or use Int.natAbs for absolute value

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp intToNatDedupBug
#cov_assert_count intToNatDedupBug 1

end Integration
