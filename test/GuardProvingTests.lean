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
#check_atp divUnguarded

-- DivisionByZero: guarded (h : y ≠ 0). IntDivTruncation: still warns (x/y may truncate)
def divGuardedNe (x y : Nat) (h : y ≠ 0) : Nat := x / y
#check_atp divGuardedNe

-- DivisionByZero: guarded. IntDivTruncation: still warns
def divGuardedPos (x y : Nat) (h : 0 < y) : Nat := x / y
#check_atp divGuardedPos

-- DivisionByZero: guarded by omega. IntDivTruncation: still warns
def divGuardedOmega (x y : Nat) (h : y > 0) : Nat := x / y
#check_atp divGuardedOmega

-- ============================================================
-- Nat Subtraction Guard Proving
-- ============================================================

-- Should be UNGUARDED
def subUnguarded (a b : Nat) : Nat := a - b
#check_atp subUnguarded

-- Should be guarded (direct assumption: h : b ≤ a)
def subGuarded (a b : Nat) (h : b ≤ a) : Nat := a - b
#check_atp subGuarded

-- Should be guarded by omega (from h1 and h2, omega can derive b ≤ a)
def subGuardedOmega (a b c : Nat) (h1 : a ≥ c) (h2 : c ≥ b) : Nat := a - b
#check_atp subGuardedOmega

-- ============================================================
-- Int.toNat Guard Proving
-- ============================================================

-- Should be UNGUARDED
def toNatUnguarded (n : Int) : Nat := n.toNat
#check_atp toNatUnguarded

-- Should be guarded (direct assumption: h : 0 ≤ n)
def toNatGuarded (n : Int) (h : 0 ≤ n) : Nat := n.toNat
#check_atp toNatGuarded

-- Should be guarded (direct assumption: h : n ≥ 0)
def toNatGuardedGe (n : Int) (h : n ≥ 0) : Nat := n.toNat
#check_atp toNatGuardedGe

-- ============================================================
-- Int.natAbs vs Int.toNat
-- ============================================================

-- Should NOT flag: Int.natAbs is always safe (returns absolute value)
def absOk (a : Int) : Nat := Int.natAbs a
#check_atp absOk

-- Should flag: Int.toNat without guard
def toNatBad (a : Int) : Nat := Int.toNat a
#check_atp toNatBad

-- Should NOT flag: Int.toNat with guard
def toNatOk (a : Int) (h : a ≥ 0) : Nat := Int.toNat a
#check_atp toNatOk

-- ============================================================
-- Int Division Guard Variants
-- ============================================================

/-- DivisionByZero: guarded. IntDivTruncation: still warns (a/b may truncate) -/
def intTdivGuarded (a b : Int) (hb : b ≠ 0) : Int := Int.tdiv a b
#check_atp intTdivGuarded

/-- DivisionByZero: guarded (simp derives b ≠ 0). IntDivTruncation: still warns -/
def posGuardNat (a b : Nat) (h : 0 < b) : Nat := a / b
#check_atp posGuardNat

/-- DivisionByZero: guarded. IntDivTruncation: still warns -/
def gtZeroGuardNat (a b : Nat) (h : b > 0) : Nat := a / b
#check_atp gtZeroGuardNat

/-- DivisionByZero: guarded. IntDivTruncation: still warns -/
def posGuardInt (a b : Int) (h : 0 < b) : Int := a / b
#check_atp posGuardInt

/-- DivisionByZero: guarded (simp derives b ≠ 0 from b < 0). IntDivTruncation: still warns -/
def negGuardInt (a b : Int) (h : b < 0) : Int := a / b
#check_atp negGuardInt

-- ============================================================
-- Nat Subtraction Edge Cases
-- ============================================================

/-- Explicit n - 1 for comparison. Expected: NatSubtraction warning (unguarded). -/
def natMinusOneUnguarded (n : Nat) : Nat := n - 1
#check_atp natMinusOneUnguarded

end GuardProving
