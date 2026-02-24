/-
  Arithmetic Semantics Tests

  Integer division truncation, division-by-zero detection, modulo-by-zero,
  Int division variants, and Int division variant zero checking.
-/

import AtpLinter
set_option linter.unusedVariables false

namespace ArithmeticSemantics

-- ============================================================
-- Integer Division Truncation
-- ============================================================

/-- BAD: 1/4 = 0 in Nat! Should be ERROR -/
def fourthRoot (x : Nat) : Nat := x ^ (1 / 4)
/--
info: Analysis of ArithmeticSemantics.fourthRoot:
──────────────────────────────────────────────────
[ERROR] ArithmeticSemantics.fourthRoot: Integer Division Truncation
  1 / 4 definitely truncates to wrong value (1 / 4 = 0 in integer division, but 0.250000 mathematically)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Use Real/Rat division, or restructure to avoid fractional division

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp fourthRoot

/-- BAD: 1/2 = 0 in Nat! Should be ERROR -/
def halfPower (x : Nat) : Nat := x ^ (1 / 2)
/--
info: Analysis of ArithmeticSemantics.halfPower:
──────────────────────────────────────────────────
[ERROR] ArithmeticSemantics.halfPower: Integer Division Truncation
  1 / 2 definitely truncates to wrong value (1 / 2 = 0 in integer division, but 0.500000 mathematically)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Use Real/Rat division, or restructure to avoid fractional division

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp halfPower

/-- BAD: 3/4 = 0 in Nat! Should be ERROR -/
def threeFourths (x : Nat) : Nat := x ^ (3 / 4)
/--
info: Analysis of ArithmeticSemantics.threeFourths:
──────────────────────────────────────────────────
[ERROR] ArithmeticSemantics.threeFourths: Integer Division Truncation
  3 / 4 definitely truncates to wrong value (3 / 4 = 0 in integer division, but 0.750000 mathematically)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Use Real/Rat division, or restructure to avoid fractional division

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp threeFourths

/-- GOOD: 4/2 = 2 (exact division) - Should NOT trigger linter -/
def exactDiv (x : Nat) : Nat := x + (4 / 2)
/-- info: ✓ ArithmeticSemantics.exactDiv: No issues detected -/
#guard_msgs in #check_atp exactDiv

/-- MAYBE: x / 2 - Possible precision loss. Should show "x / 2" not "_fvar.NNN / 2" -/
def maybeTrunc (x : Nat) : Nat := x / 2
/--
info: Analysis of ArithmeticSemantics.maybeTrunc:
──────────────────────────────────────────────────
[WARNING] ArithmeticSemantics.maybeTrunc: Integer Division Truncation
  x / 2 may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp maybeTrunc

/-- MAYBE: 10 / x - Possible truncation. Should show "10 / x" not "10 / _fvar.NNN" -/
def maybeTrunc2 (x : Nat) : Nat := 10 / x
/--
info: Analysis of ArithmeticSemantics.maybeTrunc2:
──────────────────────────────────────────────────
[WARNING] ArithmeticSemantics.maybeTrunc2: Potential Division by Zero
  10 / x has no guard ensuring x ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : x ≠ 0` or `h : x > 0`

[WARNING] ArithmeticSemantics.maybeTrunc2: Integer Division Truncation
  10 / x may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp maybeTrunc2

/-- ZERO DIV: 1 / 0 - Should be handled by DivisionByZero, not IntDivTruncation -/
def zeroDiv : Nat := 1 / 0
/--
info: Analysis of ArithmeticSemantics.zeroDiv:
──────────────────────────────────────────────────
[ERROR] ArithmeticSemantics.zeroDiv: Potential Division by Zero
  1 / 0 divides by literal zero!
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: This is definitely division by zero - the divisor is 0

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp zeroDiv

-- ============================================================
-- Division-by-Zero Detection
-- ============================================================

-- Should flag: no guard
def testUnguarded (x y : Nat) : Nat := x / y
/--
info: Analysis of ArithmeticSemantics.testUnguarded:
──────────────────────────────────────────────────
[WARNING] ArithmeticSemantics.testUnguarded: Potential Division by Zero
  x / y has no guard ensuring y ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : y ≠ 0` or `h : y > 0`

[WARNING] ArithmeticSemantics.testUnguarded: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp testUnguarded

-- No DivisionByZero (guarded); still triggers IntDivTruncation (x/y may truncate)
def testGuardedNe (x y : Nat) (h : y ≠ 0) : Nat := x / y
/--
info: Analysis of ArithmeticSemantics.testGuardedNe:
──────────────────────────────────────────────────
[WARNING] ArithmeticSemantics.testGuardedNe: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp testGuardedNe

-- No DivisionByZero (guarded); still triggers IntDivTruncation
def testGuardedGt (x y : Nat) (h : y > 0) : Nat := x / y
/--
info: Analysis of ArithmeticSemantics.testGuardedGt:
──────────────────────────────────────────────────
[WARNING] ArithmeticSemantics.testGuardedGt: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp testGuardedGt

-- No DivisionByZero (guarded); still triggers IntDivTruncation
def testGuardedLt (x y : Nat) (h : 0 < y) : Nat := x / y
/--
info: Analysis of ArithmeticSemantics.testGuardedLt:
──────────────────────────────────────────────────
[WARNING] ArithmeticSemantics.testGuardedLt: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp testGuardedLt

-- BUG TEST: y ≠ 5 should NOT be accepted as a guard for division!
def testWrongGuard (x y : Nat) (h : y ≠ 5) : Nat := x / y
/--
info: Analysis of ArithmeticSemantics.testWrongGuard:
──────────────────────────────────────────────────
[WARNING] ArithmeticSemantics.testWrongGuard: Potential Division by Zero
  x / y has no guard ensuring y ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : y ≠ 0` or `h : y > 0`

[WARNING] ArithmeticSemantics.testWrongGuard: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp testWrongGuard

-- ============================================================
-- Modulo-by-Zero
-- ============================================================

-- Should flag: unguarded modulo
def unguardedMod (a b : Nat) : Nat := a % b
/--
info: Analysis of ArithmeticSemantics.unguardedMod:
──────────────────────────────────────────────────
[WARNING] ArithmeticSemantics.unguardedMod: Modulo Edge Case
  a % b has no guard ensuring b ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≠ 0`. Note: in Lean, n % 0 = n

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp unguardedMod

-- Should NOT flag: guarded modulo
def guardedMod (a b : Nat) (h : b ≠ 0) : Nat := a % b
/-- info: ✓ ArithmeticSemantics.guardedMod: No issues detected -/
#guard_msgs in #check_atp guardedMod

-- Should NOT flag: simp derives b ≠ 0 from 0 < b
def positivityGuardedMod (a b : Nat) (h : 0 < b) : Nat := a % b
/-- info: ✓ ArithmeticSemantics.positivityGuardedMod: No issues detected -/
#guard_msgs in #check_atp positivityGuardedMod

-- ============================================================
-- Int Division Variants
-- ============================================================

-- Int division (HDiv) with literals: should be detected as "willTruncate" (5/2)
def intDivWillTruncate : Int := (5 : Int) / (2 : Int)
/--
info: Analysis of ArithmeticSemantics.intDivWillTruncate:
──────────────────────────────────────────────────
[ERROR] ArithmeticSemantics.intDivWillTruncate: Integer Division Truncation
  5 / 2 definitely truncates to wrong value (5 / 2 = 2 in integer division, but 2.500000 mathematically)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Use Real/Rat division, or restructure to avoid fractional division

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp intDivWillTruncate

-- Int division (HDiv) exact: should NOT be flagged by IntDivTruncation (4/2)
def intDivExact : Int := (4 : Int) / (2 : Int)
/-- info: ✓ ArithmeticSemantics.intDivExact: No issues detected -/
#guard_msgs in #check_atp intDivExact

-- Int division with negative literal
def intDivNegative : Int := (-5 : Int) / (2 : Int)
/--
info: Analysis of ArithmeticSemantics.intDivNegative:
──────────────────────────────────────────────────
[ERROR] ArithmeticSemantics.intDivNegative: Integer Division Truncation
  -5 / 2 definitely truncates to wrong value (-5 / 2 = -3 in integer division, but -2.500000 mathematically)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Use Real/Rat division, or restructure to avoid fractional division

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp intDivNegative

-- Int.tdiv / Int.fdiv / Int.ediv
def intTdivWillTruncate : Int := Int.tdiv (5 : Int) (2 : Int)
/--
info: Analysis of ArithmeticSemantics.intTdivWillTruncate:
──────────────────────────────────────────────────
[ERROR] ArithmeticSemantics.intTdivWillTruncate: Integer Division Truncation
  5 / 2 definitely truncates to wrong value (5 / 2 = 2 in integer division, but 2.500000 mathematically)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Use Real/Rat division, or restructure to avoid fractional division

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp intTdivWillTruncate

def intFdivWillTruncate : Int := Int.fdiv (5 : Int) (2 : Int)
/--
info: Analysis of ArithmeticSemantics.intFdivWillTruncate:
──────────────────────────────────────────────────
[ERROR] ArithmeticSemantics.intFdivWillTruncate: Integer Division Truncation
  5 / 2 definitely truncates to wrong value (5 / 2 = 2 in integer division, but 2.500000 mathematically)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Use Real/Rat division, or restructure to avoid fractional division

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp intFdivWillTruncate

def intEdivWillTruncate : Int := Int.ediv (5 : Int) (2 : Int)
/--
info: Analysis of ArithmeticSemantics.intEdivWillTruncate:
──────────────────────────────────────────────────
[ERROR] ArithmeticSemantics.intEdivWillTruncate: Integer Division Truncation
  5 / 2 definitely truncates to wrong value (5 / 2 = 2 in integer division, but 2.500000 mathematically)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Use Real/Rat division, or restructure to avoid fractional division

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp intEdivWillTruncate

-- Int division by variable with guard: guarded for DivisionByZero, still "mayTruncate"
def intDivMaybe (a b : Int) (hb : b ≠ 0) : Int := a / b
/--
info: Analysis of ArithmeticSemantics.intDivMaybe:
──────────────────────────────────────────────────
[WARNING] ArithmeticSemantics.intDivMaybe: Integer Division Truncation
  a / b may truncate (truncates (Int default /))
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp intDivMaybe

-- ============================================================
-- Int Division Variant Zero Checking
-- ============================================================

/-- Int.tdiv (truncated toward zero division). Expected: warn unguarded. -/
def intTdivUnguarded (a b : Int) : Int := Int.tdiv a b
/--
info: Analysis of ArithmeticSemantics.intTdivUnguarded:
──────────────────────────────────────────────────
[WARNING] ArithmeticSemantics.intTdivUnguarded: Potential Division by Zero
  a / b has no guard ensuring b ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≠ 0` or `h : b > 0`

[WARNING] ArithmeticSemantics.intTdivUnguarded: Integer Division Truncation
  a / b may truncate (truncates toward zero (Int.tdiv))
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp intTdivUnguarded

/-- Int.fdiv (floored division). Expected: warn unguarded. -/
def intFdivUnguarded (a b : Int) : Int := Int.fdiv a b
/--
info: Analysis of ArithmeticSemantics.intFdivUnguarded:
──────────────────────────────────────────────────
[WARNING] ArithmeticSemantics.intFdivUnguarded: Potential Division by Zero
  a / b has no guard ensuring b ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≠ 0` or `h : b > 0`

[WARNING] ArithmeticSemantics.intFdivUnguarded: Integer Division Truncation
  a / b may truncate (floors toward -∞ (Int.fdiv))
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp intFdivUnguarded

/-- Int.ediv (Euclidean division). Expected: warn unguarded. -/
def intEdivUnguarded (a b : Int) : Int := Int.ediv a b
/--
info: Analysis of ArithmeticSemantics.intEdivUnguarded:
──────────────────────────────────────────────────
[WARNING] ArithmeticSemantics.intEdivUnguarded: Potential Division by Zero
  a / b has no guard ensuring b ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≠ 0` or `h : b > 0`

[WARNING] ArithmeticSemantics.intEdivUnguarded: Integer Division Truncation
  a / b may truncate (Euclidean division (Int.ediv))
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp intEdivUnguarded

-- ============================================================
-- Division by Literal Zero
-- ============================================================

/-- Division by literal zero should be flagged as ERROR -/
def div_by_zero_nat (a : Nat) : Nat := a / 0
/--
info: Analysis of ArithmeticSemantics.div_by_zero_nat:
──────────────────────────────────────────────────
[ERROR] ArithmeticSemantics.div_by_zero_nat: Potential Division by Zero
  a / 0 divides by literal zero!
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: This is definitely division by zero - the divisor is 0

──────────────────────────────────────────────────
Summary: 1 error(s), 0 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp div_by_zero_nat

-- ============================================================
-- Nat.pred (documents current gap)
-- ============================================================

/-- Nat.pred without guard. Current linter does NOT check Nat.pred. -/
def natPredUnguarded (n : Nat) : Nat := Nat.pred n
/--
info: ✓ ArithmeticSemantics.natPredUnguarded: No issues detected
-/
#guard_msgs in #check_atp natPredUnguarded

end ArithmeticSemantics
