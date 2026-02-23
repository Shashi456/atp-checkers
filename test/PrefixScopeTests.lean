/-
  Prefix Scope Tests

  Prefix-context soundness, pathological types, binder-type traversal edge cases.
  Tests core soundness invariants of the ATP linter.
-/

import AtpLinter
set_option linter.unusedVariables false

namespace PrefixScope

-- ============================================================
-- Binder-Scope Correctness
-- ============================================================

/-!
The key soundness invariant: when analyzing a binder type, only hypotheses
that PRECEDE that binder should be available for guard proving.
-/

/--
Division is in the type of `x`. The guard `hb : b ≠ 0` is introduced AFTER `x`,
so it is NOT in scope for that binder type.

Expected: DivisionByZero should warn UNGUARDED for the division in x's type.
-/
def scopeDiv_guardAfter (a b : Nat) (x : Fin (a / b)) (hb : b ≠ 0) : Nat := 0
#check_atp scopeDiv_guardAfter

/--
Guard is introduced BEFORE the binder type that mentions `a / b`.

Expected: No DivisionByZero (guarded). IntDivTruncation still fires (not guard-gated).
-/
def scopeDiv_guardBefore (a b : Nat) (hb : b ≠ 0) (x : Fin (a / b)) : Nat := 0
#check_atp scopeDiv_guardBefore

/--
Nat subtraction is in the type of `x`. Guard `h : b ≤ a` is introduced AFTER `x`,
so it must not silence the warning.

Expected: NatSubtraction should warn UNGUARDED.
-/
def scopeSub_guardAfter (a b : Nat) (x : Fin (a - b)) (h : b ≤ a) : Nat := 0
#check_atp scopeSub_guardAfter

/--
Guard is in scope (before the binder type).

Expected: No NatSubtraction warning.
-/
def scopeSub_guardBefore (a b : Nat) (h : b ≤ a) (x : Fin (a - b)) : Nat := 0
#check_atp scopeSub_guardBefore

/--
Int.toNat is in the type of `x`. Guard `hz : 0 ≤ z` is introduced AFTER `x`,
so it must not silence the warning.

Expected: IntToNat should warn UNGUARDED.
-/
def scopeToNat_guardAfter (z : Int) (x : Fin (Int.toNat z)) (hz : 0 ≤ z) : Nat := 0
#check_atp scopeToNat_guardAfter

/--
Guard is in scope.

Expected: No IntToNat warning.
-/
def scopeToNat_guardBefore (z : Int) (hz : 0 ≤ z) (x : Fin (Int.toNat z)) : Nat := 0
#check_atp scopeToNat_guardBefore


-- ============================================================
-- Pathological OfNat (AllZero type)
-- ============================================================

/-!
A type where EVERY numeral is definitionally the same value.
This catches any optimization that treats a literal `1` as "definitely nonzero".

In AllZero: (0 : AllZero) = (1 : AllZero) = (42 : AllZero) by definitional equality.
-/

inductive AllZero : Type where
  | mk : AllZero
deriving Repr

instance (n : Nat) : OfNat AllZero n := ⟨AllZero.mk⟩
instance : Inhabited AllZero := ⟨AllZero.mk⟩

-- Prove that 1 = 0 in this type (definitionally!)
theorem allZero_one_eq_zero : (1 : AllZero) = (0 : AllZero) := rfl

instance : HDiv AllZero AllZero AllZero where
  hDiv _ _ := AllZero.mk

/--
Dividing by the literal `1` is actually dividing by (defeq) `0` in this type.

Expected: DivisionByZero should WARN (unguarded).
-/
def allZero_divByOne : AllZero := (0 : AllZero) / (1 : AllZero)
#check_atp allZero_divByOne

/-- Pathological LT: everything is `<` everything (including 0 < 0). -/
instance : LT AllZero := ⟨fun _ _ => True⟩

-- We can prove 0 < 0 in this type!
theorem allZero_zero_lt_zero : (0 : AllZero) < (0 : AllZero) := trivial

/--
Even with a hypothesis `h : 0 < (1 : AllZero)`, divisor is still defeq to 0.

Actual: no warnings. The AllZero HDiv instance ignores its arguments, so the checker
sees no real division risk here. (This may be a false negative — the guard prover does
not currently reject pathological LT instances for non-Nat/Int types.)
-/
def allZero_badLtGuard (x : AllZero) (h : (0 : AllZero) < (1 : AllZero)) : AllZero :=
  x / (1 : AllZero)
#check_atp allZero_badLtGuard


-- ============================================================
-- Proof-term Noise Regression
-- ============================================================

/--
Statement is `n = n` (clean). Proof contains division and subtraction.

Expected: No warnings (proof terms are not analyzed for Prop types).
-/
theorem proofNoise_shouldNotWarn (n : Nat) : n = n := by
  have hDiv : (10 : Nat) / 0 = (10 : Nat) / 0 := rfl
  have hSub : (0 : Nat) - 5 = (0 : Nat) - 5 := rfl
  exact rfl
#check_atp proofNoise_shouldNotWarn


-- ============================================================
-- 0/x Not Truncation
-- ============================================================

/--
`0 / x` should not trigger truncation warnings.

Expected:
- IntDivTruncation: NO warning (0/x is exact, no precision loss)
- DivisionByZero: MAY warn if x is unguarded (separate concern)
-/
def zeroOverVar (x : Nat) : Nat := 0 / x
#check_atp zeroOverVar

/--
Same with a guarded divisor - still no truncation.

Expected:
- IntDivTruncation: NO warning
- DivisionByZero: NO warning (guarded)
-/
def zeroOverGuarded (x : Nat) (hx : x ≠ 0) : Nat := 0 / x
#check_atp zeroOverGuarded


-- ============================================================
-- Multi-binder Scope Edge Cases
-- ============================================================

/--
Multiple binders with interleaved guards and risky ops.
Division in `y`'s type should see `ha` but NOT `hb`.

Expected:
- Division `a / b` in Fin type: UNGUARDED (hb comes after)
-/
def multiBinderScope (a b : Nat) (ha : a ≠ 0) (y : Fin (a / b)) (hb : b ≠ 0) : Nat := 0
#check_atp multiBinderScope

/--
Nested function type with division in inner binder.

Expected: Should detect and warn about the unguarded division.
-/
def nestedFunctionType : (n m : Nat) → Fin (n / m) → Nat := fun _ _ _ => 0
#check_atp nestedFunctionType


-- ============================================================
-- Extra Guard Forms + Binder-Type Traversal
-- ============================================================

-- Should be guarded: (0 ≠ y) orientation
def divGuardedNeSymm (x y : Nat) (h : (0 : Nat) ≠ y) : Nat := x / y
#check_atp divGuardedNeSymm

-- Should be guarded: y ≠ Nat.zero (different 0 representation)
def divGuardedNatZero (x y : Nat) (h : y ≠ Nat.zero) : Nat := x / y
#check_atp divGuardedNatZero

-- Should be guarded by omega: 2 ≤ y implies 0 < y, hence y ≠ 0
def divGuardedFromGeTwo (x y : Nat) (h : 2 ≤ y) : Nat := x / y
#check_atp divGuardedFromGeTwo

-- Explicit Nat.div form (unguarded)
def divNatDivUnguarded (x y : Nat) : Nat := Nat.div x y
#check_atp divNatDivUnguarded

-- Structural-safe divisor: succ y is never 0.
def divBySucc (x y : Nat) : Nat := x / Nat.succ y
#check_atp divBySucc

-- Division appearing in a *later binder type* (unguarded)
def finDivTypeUnguarded (n m : Nat) : Fin (n / m) → Nat :=
  fun _ => 0
#check_atp finDivTypeUnguarded

-- Division appearing in a *later binder type* (guarded by hypothesis)
def finDivTypeGuarded (n m : Nat) (h : m ≠ 0) : Fin (n / m) → Nat :=
  fun _ => 0
#check_atp finDivTypeGuarded

-- Theorem statement: division is in the statement, guard is a hypothesis
theorem divInStatementGuarded (x y : Nat) (h : y ≠ 0) : x / y = x / y := by
  rfl
#check_atp divInStatementGuarded


-- ============================================================
-- Nat.sub Edge Cases
-- ============================================================

-- Explicit Nat.sub form (unguarded)
def subNatSubUnguarded (a b : Nat) : Nat := Nat.sub a b
#check_atp subNatSubUnguarded

-- Should be guarded by omega: (b + 2 ≤ a) implies b ≤ a
def subGuardedFromOffset (a b : Nat) (h : b + 2 ≤ a) : Nat := a - b
#check_atp subGuardedFromOffset

-- Safe subtraction: a - 0 should never truncate.
def subByZero (a : Nat) : Nat := a - 0
#check_atp subByZero

-- Subtraction in a later binder type (unguarded)
def finSubTypeUnguarded (n k : Nat) : Fin (n - k) → Nat :=
  fun _ => 0
#check_atp finSubTypeUnguarded

-- Subtraction in a later binder type (guarded)
def finSubTypeGuarded (n k : Nat) (h : k ≤ n) : Fin (n - k) → Nat :=
  fun _ => 0
#check_atp finSubTypeGuarded

-- Theorem statement with subtraction + guard hypothesis
theorem subInStatementGuarded (a b : Nat) (h : b ≤ a) : a - b = a - b := by
  rfl
#check_atp subInStatementGuarded


-- ============================================================
-- Int.toNat Edge Cases
-- ============================================================

-- Should be UNGUARDED: `n > -10` does not imply `0 ≤ n`
def toNatWrongGuard (n : Int) (h : n > (-10 : Int)) : Nat := n.toNat
#check_atp toNatWrongGuard

-- Should be guarded by omega: 2 ≤ n implies 0 ≤ n
def toNatGuardedFromGeTwo (n : Int) (h : (2 : Int) ≤ n) : Nat := n.toNat
#check_atp toNatGuardedFromGeTwo

-- Negative constant: should be UNGUARDED (and evaluates to 0)
def toNatNegConst : Nat := (-3 : Int).toNat
#check_atp toNatNegConst
#eval (-3 : Int).toNat  -- 0

-- Int.natAbs is a different conversion (absolute value).
def natAbsExample (n : Int) : Nat := Int.natAbs n
#check_atp natAbsExample

-- A common "round-trip" in generated code: (Int.ofNat n).toNat.
def toNatOfOfNat (n : Nat) : Nat := (Int.ofNat n).toNat
#check_atp toNatOfOfNat

-- Int.toNat in a later binder type (unguarded)
def finToNatTypeUnguarded (n : Int) : Fin (n.toNat) → Nat :=
  fun _ => 0
#check_atp finToNatTypeUnguarded

-- Int.toNat in a later binder type (guarded)
def finToNatTypeGuarded (n : Int) (h : 0 ≤ n) : Fin (n.toNat) → Nat :=
  fun _ => 0
#check_atp finToNatTypeGuarded

-- Theorem statement with Int.toNat + guard hypothesis
theorem toNatInStatementGuarded (n : Int) (h : 0 ≤ n) : n.toNat = n.toNat := by
  rfl
#check_atp toNatInStatementGuarded

end PrefixScope
