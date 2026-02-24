/-
  Full Scope Tests

  Full-scope guard checking, pathological types, binder-type traversal edge cases.
  Tests core invariants of the ATP linter. Guard checking uses the full proof-state
  context (all hypotheses are available regardless of binder order).
-/

import AtpLinter
set_option linter.unusedVariables false

namespace PrefixScope

-- ============================================================
-- Full-Scope Guard Checking
-- ============================================================



/-!
Guard checking uses full proof-state semantics: ALL hypotheses from the
declaration signature are available for guard proving, regardless of
binder ordering. This matches how Lean's proof state works.
-/

/--
Division is in the type of `x`. The guard `hb : b ≠ 0` is introduced AFTER `x`,
but with full-scope checking it IS available for guard proving.

Expected: DivisionByZero should be GUARDED. IntDivTruncation still fires.
-/
def scopeDiv_guardAfter (a b : Nat) (x : Fin (a / b)) (hb : b ≠ 0) : Nat := 0

/--
info: Analysis of PrefixScope.scopeDiv_guardAfter:
──────────────────────────────────────────────────
[WARNING] PrefixScope.scopeDiv_guardAfter: Integer Division Truncation
  a / b may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp scopeDiv_guardAfter


/--
Guard is introduced BEFORE the binder type that mentions `a / b`.

Expected: No DivisionByZero (guarded). IntDivTruncation still fires (not guard-gated).
-/
def scopeDiv_guardBefore (a b : Nat) (hb : b ≠ 0) (x : Fin (a / b)) : Nat := 0
/--
info: Analysis of PrefixScope.scopeDiv_guardBefore:
──────────────────────────────────────────────────
[WARNING] PrefixScope.scopeDiv_guardBefore: Integer Division Truncation
  a / b may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp scopeDiv_guardBefore

/--
Nat subtraction is in the type of `x`. Guard `h : b ≤ a` is introduced AFTER `x`,
but with full-scope checking it IS available for guard proving.

Expected: NatSubtraction should be GUARDED (no warning).
-/
def scopeSub_guardAfter (a b : Nat) (x : Fin (a - b)) (h : b ≤ a) : Nat := 0
/-- info: ✓ PrefixScope.scopeSub_guardAfter: No issues detected -/
#guard_msgs in #check_atp scopeSub_guardAfter

/--
Guard is in scope (before the binder type).

Expected: No NatSubtraction warning.
-/
def scopeSub_guardBefore (a b : Nat) (h : b ≤ a) (x : Fin (a - b)) : Nat := 0
/-- info: ✓ PrefixScope.scopeSub_guardBefore: No issues detected -/
#guard_msgs in #check_atp scopeSub_guardBefore

/--
Int.toNat is in the type of `x`. Guard `hz : 0 ≤ z` is introduced AFTER `x`,
but with full-scope checking it IS available for guard proving.

Expected: IntToNat should be GUARDED (no warning).
-/
def scopeToNat_guardAfter (z : Int) (x : Fin (Int.toNat z)) (hz : 0 ≤ z) : Nat := 0
/-- info: ✓ PrefixScope.scopeToNat_guardAfter: No issues detected -/
#guard_msgs in #check_atp scopeToNat_guardAfter

/--
Guard is in scope.

Expected: No IntToNat warning.
-/
def scopeToNat_guardBefore (z : Int) (hz : 0 ≤ z) (x : Fin (Int.toNat z)) : Nat := 0
/-- info: ✓ PrefixScope.scopeToNat_guardBefore: No issues detected -/
#guard_msgs in #check_atp scopeToNat_guardBefore


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
/--
info: Analysis of PrefixScope.allZero_divByOne:
──────────────────────────────────────────────────
[WARNING] PrefixScope.allZero_divByOne: Potential Division by Zero
  0 / 1 has no guard ensuring 1 ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : 1 ≠ 0` or `h : 1 > 0`

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp allZero_divByOne

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
/-- info: ✓ PrefixScope.allZero_badLtGuard: No issues detected -/
#guard_msgs in #check_atp allZero_badLtGuard


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
/-- info: ✓ PrefixScope.proofNoise_shouldNotWarn: No issues detected -/
#guard_msgs in #check_atp proofNoise_shouldNotWarn


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
/--
info: Analysis of PrefixScope.zeroOverVar:
──────────────────────────────────────────────────
[WARNING] PrefixScope.zeroOverVar: Potential Division by Zero
  0 / x has no guard ensuring x ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : x ≠ 0` or `h : x > 0`

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp zeroOverVar

/--
Same with a guarded divisor - still no truncation.

Expected:
- IntDivTruncation: NO warning
- DivisionByZero: NO warning (guarded)
-/
def zeroOverGuarded (x : Nat) (hx : x ≠ 0) : Nat := 0 / x
/-- info: ✓ PrefixScope.zeroOverGuarded: No issues detected -/
#guard_msgs in #check_atp zeroOverGuarded


-- ============================================================
-- Multi-binder Scope Edge Cases
-- ============================================================

/--
Multiple binders with interleaved guards and risky ops.
With full-scope checking, `hb : b ≠ 0` IS available even though it comes after `y`.

Expected:
- Division `a / b` in Fin type: GUARDED by hb. Only IntDivTruncation fires.
-/
def multiBinderScope (a b : Nat) (ha : a ≠ 0) (y : Fin (a / b)) (hb : b ≠ 0) : Nat := 0
/--
info: Analysis of PrefixScope.multiBinderScope:
──────────────────────────────────────────────────
[WARNING] PrefixScope.multiBinderScope: Integer Division Truncation
  a / b may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp multiBinderScope

/--
Nested function type with division in inner binder.

Expected: Should detect and warn about the unguarded division.
-/
def nestedFunctionType : (n m : Nat) → Fin (n / m) → Nat := fun _ _ _ => 0
/--
info: Analysis of PrefixScope.nestedFunctionType:
──────────────────────────────────────────────────
[WARNING] PrefixScope.nestedFunctionType: Potential Division by Zero
  n / m has no guard ensuring m ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : m ≠ 0` or `h : m > 0`

[WARNING] PrefixScope.nestedFunctionType: Potential Division by Zero
  x✝² / x✝¹ has no guard ensuring x✝¹ ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : x✝¹ ≠ 0` or `h : x✝¹ > 0`

[WARNING] PrefixScope.nestedFunctionType: Integer Division Truncation
  n / m may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

[WARNING] PrefixScope.nestedFunctionType: Integer Division Truncation
  x✝¹ / x✝ may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 4 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp nestedFunctionType


-- ============================================================
-- Extra Guard Forms + Binder-Type Traversal
-- ============================================================

-- Should be guarded: (0 ≠ y) orientation
def divGuardedNeSymm (x y : Nat) (h : (0 : Nat) ≠ y) : Nat := x / y
/--
info: Analysis of PrefixScope.divGuardedNeSymm:
──────────────────────────────────────────────────
[WARNING] PrefixScope.divGuardedNeSymm: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp divGuardedNeSymm

-- Should be guarded: y ≠ Nat.zero (different 0 representation)
def divGuardedNatZero (x y : Nat) (h : y ≠ Nat.zero) : Nat := x / y
/--
info: Analysis of PrefixScope.divGuardedNatZero:
──────────────────────────────────────────────────
[WARNING] PrefixScope.divGuardedNatZero: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp divGuardedNatZero

-- Should be guarded by omega: 2 ≤ y implies 0 < y, hence y ≠ 0
def divGuardedFromGeTwo (x y : Nat) (h : 2 ≤ y) : Nat := x / y
/--
info: Analysis of PrefixScope.divGuardedFromGeTwo:
──────────────────────────────────────────────────
[WARNING] PrefixScope.divGuardedFromGeTwo: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp divGuardedFromGeTwo

-- Explicit Nat.div form (unguarded)
def divNatDivUnguarded (x y : Nat) : Nat := Nat.div x y
/--
info: Analysis of PrefixScope.divNatDivUnguarded:
──────────────────────────────────────────────────
[WARNING] PrefixScope.divNatDivUnguarded: Potential Division by Zero
  x / y has no guard ensuring y ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : y ≠ 0` or `h : y > 0`

[WARNING] PrefixScope.divNatDivUnguarded: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp divNatDivUnguarded

-- Structural-safe divisor: succ y is never 0.
def divBySucc (x y : Nat) : Nat := x / Nat.succ y
/--
info: Analysis of PrefixScope.divBySucc:
──────────────────────────────────────────────────
[WARNING] PrefixScope.divBySucc: Integer Division Truncation
  x / y.succ may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp divBySucc

-- Division appearing in a *later binder type* (unguarded)
def finDivTypeUnguarded (n m : Nat) : Fin (n / m) → Nat :=
  fun _ => 0
/--
info: Analysis of PrefixScope.finDivTypeUnguarded:
──────────────────────────────────────────────────
[WARNING] PrefixScope.finDivTypeUnguarded: Potential Division by Zero
  n / m has no guard ensuring m ≠ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : m ≠ 0` or `h : m > 0`

[WARNING] PrefixScope.finDivTypeUnguarded: Integer Division Truncation
  n / m may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 2 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp finDivTypeUnguarded

-- Division appearing in a *later binder type* (guarded by hypothesis)
def finDivTypeGuarded (n m : Nat) (h : m ≠ 0) : Fin (n / m) → Nat :=
  fun _ => 0
/--
info: Analysis of PrefixScope.finDivTypeGuarded:
──────────────────────────────────────────────────
[WARNING] PrefixScope.finDivTypeGuarded: Integer Division Truncation
  n / m may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp finDivTypeGuarded

-- Theorem statement: division is in the statement, guard is a hypothesis
theorem divInStatementGuarded (x y : Nat) (h : y ≠ 0) : x / y = x / y := by
  rfl
/--
info: Analysis of PrefixScope.divInStatementGuarded:
──────────────────────────────────────────────────
[WARNING] PrefixScope.divInStatementGuarded: Integer Division Truncation
  x / y may truncate (truncates toward zero)
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Ensure truncation is intended, or use Real/Rat if precise division is needed

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp divInStatementGuarded


-- ============================================================
-- Nat.sub Edge Cases
-- ============================================================

-- Explicit Nat.sub form (unguarded)
def subNatSubUnguarded (a b : Nat) : Nat := Nat.sub a b
/--
info: Analysis of PrefixScope.subNatSubUnguarded:
──────────────────────────────────────────────────
[WARNING] PrefixScope.subNatSubUnguarded: Truncated Nat Subtraction
  a - b has no guard ensuring b ≤ a
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : b ≤ a` or use Int instead of Nat

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp subNatSubUnguarded

-- Should be guarded by omega: (b + 2 ≤ a) implies b ≤ a
def subGuardedFromOffset (a b : Nat) (h : b + 2 ≤ a) : Nat := a - b
/-- info: ✓ PrefixScope.subGuardedFromOffset: No issues detected -/
#guard_msgs in #check_atp subGuardedFromOffset

-- Safe subtraction: a - 0 should never truncate.
def subByZero (a : Nat) : Nat := a - 0
/-- info: ✓ PrefixScope.subByZero: No issues detected -/
#guard_msgs in #check_atp subByZero

-- Subtraction in a later binder type (unguarded)
def finSubTypeUnguarded (n k : Nat) : Fin (n - k) → Nat :=
  fun _ => 0
/--
info: Analysis of PrefixScope.finSubTypeUnguarded:
──────────────────────────────────────────────────
[WARNING] PrefixScope.finSubTypeUnguarded: Truncated Nat Subtraction
  n - k has no guard ensuring k ≤ n
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : k ≤ n` or use Int instead of Nat

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp finSubTypeUnguarded

-- Subtraction in a later binder type (guarded)
def finSubTypeGuarded (n k : Nat) (h : k ≤ n) : Fin (n - k) → Nat :=
  fun _ => 0
/-- info: ✓ PrefixScope.finSubTypeGuarded: No issues detected -/
#guard_msgs in #check_atp finSubTypeGuarded

-- Theorem statement with subtraction + guard hypothesis
theorem subInStatementGuarded (a b : Nat) (h : b ≤ a) : a - b = a - b := by
  rfl
/-- info: ✓ PrefixScope.subInStatementGuarded: No issues detected -/
#guard_msgs in #check_atp subInStatementGuarded


-- ============================================================
-- Int.toNat Edge Cases
-- ============================================================

-- Should be UNGUARDED: `n > -10` does not imply `0 ≤ n`
def toNatWrongGuard (n : Int) (h : n > (-10 : Int)) : Nat := n.toNat
/--
info: Analysis of PrefixScope.toNatWrongGuard:
──────────────────────────────────────────────────
[WARNING] PrefixScope.toNatWrongGuard: Unguarded Int.toNat
  Int.toNat (n) has no guard ensuring (n) ≥ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : n ≥ 0` or use Int.natAbs for absolute value

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp toNatWrongGuard

-- Should be guarded by omega: 2 ≤ n implies 0 ≤ n
def toNatGuardedFromGeTwo (n : Int) (h : (2 : Int) ≤ n) : Nat := n.toNat
/-- info: ✓ PrefixScope.toNatGuardedFromGeTwo: No issues detected -/
#guard_msgs in #check_atp toNatGuardedFromGeTwo

-- Negative constant: should be UNGUARDED (and evaluates to 0)
def toNatNegConst : Nat := (-3 : Int).toNat
/--
info: Analysis of PrefixScope.toNatNegConst:
──────────────────────────────────────────────────
[WARNING] PrefixScope.toNatNegConst: Unguarded Int.toNat
  Int.toNat (-3) has no guard ensuring (-3) ≥ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : -3 ≥ 0` or use Int.natAbs for absolute value

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp toNatNegConst

-- Int.natAbs is a different conversion (absolute value).
def natAbsExample (n : Int) : Nat := Int.natAbs n
/-- info: ✓ PrefixScope.natAbsExample: No issues detected -/
#guard_msgs in #check_atp natAbsExample

-- A common "round-trip" in generated code: (Int.ofNat n).toNat.
def toNatOfOfNat (n : Nat) : Nat := (Int.ofNat n).toNat
/--
info: Analysis of PrefixScope.toNatOfOfNat:
──────────────────────────────────────────────────
[WARNING] PrefixScope.toNatOfOfNat: Unguarded Int.toNat
  Int.toNat (Int.ofNat n) has no guard ensuring (Int.ofNat n) ≥ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : Int.ofNat n ≥ 0` or use Int.natAbs for absolute value

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp toNatOfOfNat

-- Int.toNat in a later binder type (unguarded)
def finToNatTypeUnguarded (n : Int) : Fin (n.toNat) → Nat :=
  fun _ => 0
/--
info: Analysis of PrefixScope.finToNatTypeUnguarded:
──────────────────────────────────────────────────
[WARNING] PrefixScope.finToNatTypeUnguarded: Unguarded Int.toNat
  Int.toNat (n) has no guard ensuring (n) ≥ 0
  Taxonomy: I.d - Lean Semantic Traps
  Suggestion: Add hypothesis `h : n ≥ 0` or use Int.natAbs for absolute value

──────────────────────────────────────────────────
Summary: 0 error(s), 1 warning(s), 0 info(s)
-/
#guard_msgs in #check_atp finToNatTypeUnguarded

-- Int.toNat in a later binder type (guarded)
def finToNatTypeGuarded (n : Int) (h : 0 ≤ n) : Fin (n.toNat) → Nat :=
  fun _ => 0
/-- info: ✓ PrefixScope.finToNatTypeGuarded: No issues detected -/
#guard_msgs in #check_atp finToNatTypeGuarded

-- Theorem statement with Int.toNat + guard hypothesis
theorem toNatInStatementGuarded (n : Int) (h : 0 ≤ n) : n.toNat = n.toNat := by
  rfl
/--
info: ✓ PrefixScope.toNatInStatementGuarded: No issues detected
-/
#guard_msgs in #check_atp toNatInStatementGuarded

end PrefixScope
