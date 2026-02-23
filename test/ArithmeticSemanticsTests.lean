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
#check_atp fourthRoot

/-- BAD: 1/2 = 0 in Nat! Should be ERROR -/
def halfPower (x : Nat) : Nat := x ^ (1 / 2)
#check_atp halfPower

/-- BAD: 3/4 = 0 in Nat! Should be ERROR -/
def threeFourths (x : Nat) : Nat := x ^ (3 / 4)
#check_atp threeFourths

/-- GOOD: 4/2 = 2 (exact division) - Should NOT trigger linter -/
def exactDiv (x : Nat) : Nat := x + (4 / 2)
#check_atp exactDiv

/-- MAYBE: x / 2 - Possible precision loss. Should show "x / 2" not "_fvar.NNN / 2" -/
def maybeTrunc (x : Nat) : Nat := x / 2
#check_atp maybeTrunc

/-- MAYBE: 10 / x - Possible truncation. Should show "10 / x" not "10 / _fvar.NNN" -/
def maybeTrunc2 (x : Nat) : Nat := 10 / x
#check_atp maybeTrunc2

/-- ZERO DIV: 1 / 0 - Should be handled by DivisionByZero, not IntDivTruncation -/
def zeroDiv : Nat := 1 / 0
#check_atp zeroDiv

-- Verify the truncation values
#eval (1 : Nat) / 4  -- 0, not 0.25
#eval (1 : Nat) / 2  -- 0, not 0.5
#eval (3 : Nat) / 4  -- 0, not 0.75
#eval (4 : Nat) / 2  -- 2 (exact)
#eval (16 : Nat) ^ ((1 : Nat) / 4)  -- Returns 1, not 2!
#eval (81 : Nat) ^ ((1 : Nat) / 4)  -- Returns 1, not 3!

-- ============================================================
-- Division-by-Zero Detection
-- ============================================================

-- Should flag: no guard
def testUnguarded (x y : Nat) : Nat := x / y
#check_atp testUnguarded

-- No DivisionByZero (guarded); still triggers IntDivTruncation (x/y may truncate)
def testGuardedNe (x y : Nat) (h : y ≠ 0) : Nat := x / y
#check_atp testGuardedNe

-- No DivisionByZero (guarded); still triggers IntDivTruncation
def testGuardedGt (x y : Nat) (h : y > 0) : Nat := x / y
#check_atp testGuardedGt

-- No DivisionByZero (guarded); still triggers IntDivTruncation
def testGuardedLt (x y : Nat) (h : 0 < y) : Nat := x / y
#check_atp testGuardedLt

-- BUG TEST: y ≠ 5 should NOT be accepted as a guard for division!
def testWrongGuard (x y : Nat) (h : y ≠ 5) : Nat := x / y
#check_atp testWrongGuard

-- ============================================================
-- Modulo-by-Zero
-- ============================================================

-- Should flag: unguarded modulo
def unguardedMod (a b : Nat) : Nat := a % b
#check_atp unguardedMod

-- Should NOT flag: guarded modulo
def guardedMod (a b : Nat) (h : b ≠ 0) : Nat := a % b
#check_atp guardedMod

-- Should NOT flag: simp derives b ≠ 0 from 0 < b
def positivityGuardedMod (a b : Nat) (h : 0 < b) : Nat := a % b
#check_atp positivityGuardedMod

-- ============================================================
-- Int Division Variants
-- ============================================================

-- Int division (HDiv) with literals: should be detected as "willTruncate" (5/2)
def intDivWillTruncate : Int := (5 : Int) / (2 : Int)
#check_atp intDivWillTruncate

-- Int division (HDiv) exact: should NOT be flagged by IntDivTruncation (4/2)
def intDivExact : Int := (4 : Int) / (2 : Int)
#check_atp intDivExact

-- Int division with negative literal
def intDivNegative : Int := (-5 : Int) / (2 : Int)
#check_atp intDivNegative

-- Int.tdiv / Int.fdiv / Int.ediv
def intTdivWillTruncate : Int := Int.tdiv (5 : Int) (2 : Int)
#check_atp intTdivWillTruncate

def intFdivWillTruncate : Int := Int.fdiv (5 : Int) (2 : Int)
#check_atp intFdivWillTruncate

def intEdivWillTruncate : Int := Int.ediv (5 : Int) (2 : Int)
#check_atp intEdivWillTruncate

-- Int division by variable with guard: guarded for DivisionByZero, still "mayTruncate"
def intDivMaybe (a b : Int) (hb : b ≠ 0) : Int := a / b
#check_atp intDivMaybe

-- ============================================================
-- Int Division Variant Zero Checking
-- ============================================================

/-- Int.tdiv (truncated toward zero division). Expected: warn unguarded. -/
def intTdivUnguarded (a b : Int) : Int := Int.tdiv a b
#check_atp intTdivUnguarded

/-- Int.fdiv (floored division). Expected: warn unguarded. -/
def intFdivUnguarded (a b : Int) : Int := Int.fdiv a b
#check_atp intFdivUnguarded

/-- Int.ediv (Euclidean division). Expected: warn unguarded. -/
def intEdivUnguarded (a b : Int) : Int := Int.ediv a b
#check_atp intEdivUnguarded

end ArithmeticSemantics
