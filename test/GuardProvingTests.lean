/-
  Guard Proving Tests

  Tests that the guard prover accepts/rejects guards correctly for
  division, Nat subtraction, Int.toNat, Int division variants, and edge cases.
-/

import AtpLinter
set_option linter.unusedVariables false

namespace GuardProving

-- ============================================================
-- Division Guard Proving
-- ============================================================

-- Should be UNGUARDED
def divUnguarded (x y : Nat) : Nat := x / y
/--
info: Analysis of GuardProving.divUnguarded:
──────────────────────────────────────────────────
[WARNING] GuardProving.divUnguarded: Potential Division by Zero
  x / y has no guard ensuring y ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : y ≠ 0` or `h : y > 0`

[WARNING] GuardProving.divUnguarded: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp divUnguarded

-- DivisionByZero: guarded (h : y ≠ 0). IntDivTruncation: still warns (x/y may truncate)
def divGuardedNe (x y : Nat) (h : y ≠ 0) : Nat := x / y
/--
info: Analysis of GuardProving.divGuardedNe:
──────────────────────────────────────────────────
[WARNING] GuardProving.divGuardedNe: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp divGuardedNe

-- DivisionByZero: guarded. IntDivTruncation: still warns
def divGuardedPos (x y : Nat) (h : 0 < y) : Nat := x / y
/--
info: Analysis of GuardProving.divGuardedPos:
──────────────────────────────────────────────────
[WARNING] GuardProving.divGuardedPos: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp divGuardedPos

-- DivisionByZero: guarded by omega. IntDivTruncation: still warns
def divGuardedOmega (x y : Nat) (h : y > 0) : Nat := x / y
/--
info: Analysis of GuardProving.divGuardedOmega:
──────────────────────────────────────────────────
[WARNING] GuardProving.divGuardedOmega: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp divGuardedOmega

-- ============================================================
-- Nat Subtraction Guard Proving
-- ============================================================

-- Should be UNGUARDED
def subUnguarded (a b : Nat) : Nat := a - b
/--
info: Analysis of GuardProving.subUnguarded:
──────────────────────────────────────────────────
[WARNING] GuardProving.subUnguarded: Truncated Nat Subtraction
  a - b has no guard ensuring b ≤ a
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≤ a` or use Int instead of Nat

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp subUnguarded

-- Should be guarded (direct assumption: h : b ≤ a)
def subGuarded (a b : Nat) (h : b ≤ a) : Nat := a - b
/-- info: ✓ GuardProving.subGuarded: No issues detected -/
#guard_msgs in #check_atp subGuarded

-- Should be guarded by omega (from h1 and h2, omega can derive b ≤ a)
def subGuardedOmega (a b c : Nat) (h1 : a ≥ c) (h2 : c ≥ b) : Nat := a - b
/-- info: ✓ GuardProving.subGuardedOmega: No issues detected -/
#guard_msgs in #check_atp subGuardedOmega

-- ============================================================
-- Int.toNat Guard Proving
-- ============================================================

-- Should be UNGUARDED
def toNatUnguarded (n : Int) : Nat := n.toNat
/--
info: Analysis of GuardProving.toNatUnguarded:
──────────────────────────────────────────────────
[WARNING] GuardProving.toNatUnguarded: Unguarded Int.toNat
  Int.toNat (n) has no guard ensuring (n) ≥ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : n ≥ 0` or use Int.natAbs for absolute value

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp toNatUnguarded

-- Should be guarded (direct assumption: h : 0 ≤ n)
def toNatGuarded (n : Int) (h : 0 ≤ n) : Nat := n.toNat
/-- info: ✓ GuardProving.toNatGuarded: No issues detected -/
#guard_msgs in #check_atp toNatGuarded

-- Should be guarded (direct assumption: h : n ≥ 0)
def toNatGuardedGe (n : Int) (h : n ≥ 0) : Nat := n.toNat
/-- info: ✓ GuardProving.toNatGuardedGe: No issues detected -/
#guard_msgs in #check_atp toNatGuardedGe

-- ============================================================
-- Int.natAbs vs Int.toNat
-- ============================================================

-- Should NOT flag: Int.natAbs is always safe (returns absolute value)
def absOk (a : Int) : Nat := Int.natAbs a
/-- info: ✓ GuardProving.absOk: No issues detected -/
#guard_msgs in #check_atp absOk

-- Should flag: Int.toNat without guard
def toNatBad (a : Int) : Nat := Int.toNat a
/--
info: Analysis of GuardProving.toNatBad:
──────────────────────────────────────────────────
[WARNING] GuardProving.toNatBad: Unguarded Int.toNat
  Int.toNat (a) has no guard ensuring (a) ≥ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : a ≥ 0` or use Int.natAbs for absolute value

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp toNatBad

-- Should NOT flag: Int.toNat with guard
def toNatOk (a : Int) (h : a ≥ 0) : Nat := Int.toNat a
/-- info: ✓ GuardProving.toNatOk: No issues detected -/
#guard_msgs in #check_atp toNatOk

-- ============================================================
-- Int Division Guard Variants
-- ============================================================

/-- DivisionByZero: guarded. IntDivTruncation: still warns (a/b may truncate) -/
def intTdivGuarded (a b : Int) (hb : b ≠ 0) : Int := Int.tdiv a b
/--
info: Analysis of GuardProving.intTdivGuarded:
──────────────────────────────────────────────────
[WARNING] GuardProving.intTdivGuarded: Integer Division Truncation
  a / b may truncate (truncates toward zero (Int.tdiv))
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp intTdivGuarded

/-- DivisionByZero: guarded (simp derives b ≠ 0). IntDivTruncation: still warns -/
def posGuardNat (a b : Nat) (h : 0 < b) : Nat := a / b
/--
info: Analysis of GuardProving.posGuardNat:
──────────────────────────────────────────────────
[WARNING] GuardProving.posGuardNat: Integer Division Truncation
  a / b may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp posGuardNat

/-- DivisionByZero: guarded. IntDivTruncation: still warns -/
def gtZeroGuardNat (a b : Nat) (h : b > 0) : Nat := a / b
/--
info: Analysis of GuardProving.gtZeroGuardNat:
──────────────────────────────────────────────────
[WARNING] GuardProving.gtZeroGuardNat: Integer Division Truncation
  a / b may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp gtZeroGuardNat

/-- DivisionByZero: guarded. IntDivTruncation: still warns -/
def posGuardInt (a b : Int) (h : 0 < b) : Int := a / b
/--
info: Analysis of GuardProving.posGuardInt:
──────────────────────────────────────────────────
[WARNING] GuardProving.posGuardInt: Integer Division Truncation
  a / b may truncate (truncates (Int default /))
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp posGuardInt

/-- DivisionByZero: guarded (simp derives b ≠ 0 from b < 0). IntDivTruncation: still warns -/
def negGuardInt (a b : Int) (h : b < 0) : Int := a / b
/--
info: Analysis of GuardProving.negGuardInt:
──────────────────────────────────────────────────
[WARNING] GuardProving.negGuardInt: Integer Division Truncation
  a / b may truncate (truncates (Int default /))
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp negGuardInt

-- ============================================================
-- Nat Subtraction Edge Cases
-- ============================================================

/-- Explicit n - 1 for comparison. Expected: NatSubtraction warning (unguarded). -/
def natMinusOneUnguarded (n : Nat) : Nat := n - 1
/--
info: Analysis of GuardProving.natMinusOneUnguarded:
──────────────────────────────────────────────────
[WARNING] GuardProving.natMinusOneUnguarded: Truncated Nat Subtraction
  n - 1 has no guard ensuring 1 ≤ n
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : 1 ≤ n` or use Int instead of Nat

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp natMinusOneUnguarded

-- ============================================================
-- Guard Proving: Omega and Chained Inequalities
-- ============================================================

/-- Subtraction guarded by omega-provable hypothesis -/
theorem subGuardedOmega2 (a b : Nat) (h : a ≥ b) : a - b + b = a := by omega
/-- info: ✓ GuardProving.subGuardedOmega2: No issues detected -/
#guard_msgs in #check_atp subGuardedOmega2

/-- Int.toNat guarded by h : x ≥ 2, omega should prove 0 ≤ x -/
theorem toNatGuardedFromGeTwo (x : Int) (h : x ≥ 2) : x.toNat ≥ 0 := by omega
/-- info: ✓ GuardProving.toNatGuardedFromGeTwo: No issues detected -/
#guard_msgs in #check_atp toNatGuardedFromGeTwo

/-- Chained inequalities: a ≥ c, c ≥ b ⟹ a ≥ b (omega should handle) -/
theorem chainedIneq (a b c : Nat) (h1 : a ≥ c) (h2 : c ≥ b) : a - b ≤ a := by omega
/--
info: ✓ GuardProving.chainedIneq: No issues detected
-/
#guard_msgs in #check_atp chainedIneq

end GuardProving
