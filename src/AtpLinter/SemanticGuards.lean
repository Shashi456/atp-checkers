/-
  Semantic Guard Prover

  Instead of syntactically pattern-matching hypothesis types,
  we build a goal and try to prove it using tactics.

  Approach:
  1. Try `assumption` (catches direct hypotheses like `h : x ≠ 0`)
  2. Try a small, targeted simp for structural cases (e.g., `Nat.succ n ≠ 0`)
  3. Try `omega` (Nat/Int linear arithmetic), via falseOrByContra pipeline
  4. Side-effect free: saves/restores meta state

  SOUNDNESS NOTES:
  - For division: only `d ≠ 0` (or `0 ≠ d`) counts as a valid guard
  - We do NOT directly accept `0 < d` because `<` is a typeclass relation
    that doesn't necessarily imply `≠` in arbitrary types
  - The simp phase may derive `d ≠ 0` from `0 < d` using standard lemmas

  Based on feedback from Lean community.
-/

import Lean
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Simp.Main
import Lean.Elab.Tactic.FalseOrByContra
import Lean.Elab.Tactic.Omega
import Lean.Meta.Tactic.Grind

open Lean Meta

namespace AtpLinter
namespace SemanticGuards

/-- Where a guard proof came from (useful for debugging / stats). -/
inductive ProvedBy where
  | assumption  -- Found directly in local context via assumptionCore
  | simp        -- Closed by simp with default lemmas
  | byContra    -- Closed by falseOrByContra transformation (trivially true/false)
  | omega       -- Closed by omega tactic on linear arithmetic
  | positivity  -- Derived from positivity hypothesis (0 < x → x ≠ 0)
  | grind       -- Closed by grind SMT-style solver
  deriving Inhabited, Repr, BEq

/--
A snapshot you can use when your checker carries its own `(lctx, localInstances)`
instead of relying on the ambient `MetaM` context.
-/
structure LocalCtxSnapshot where
  lctx  : LocalContext
  insts : LocalInstances

/-- Run `k` under a specific local context/instances snapshot. -/
def withSnapshot (snap : LocalCtxSnapshot) (k : MetaM α) : MetaM α :=
  Meta.withLCtx snap.lctx snap.insts k

/-- Collect all *propositional* local hypotheses as expressions (fvars). -/
private def getLocalPropHyps : MetaM (List Expr) := do
  let lctx ← getLCtx
  lctx.foldlM (init := []) fun acc decl => do
    if decl.isImplementationDetail then
      return acc
    else
      let h : Expr := mkFVar decl.fvarId
      let ht ← inferType h
      if (← isProp ht) then
        return h :: acc
      else
        return acc

/-- Check if a proposition is a linear arithmetic fact that omega can use.
    Accepts LE.le, LT.lt, Eq, Ne on Nat/Int, plus And/Not compounds.
    Also accepts type-specific versions like Nat.le, Nat.lt after whnf. -/
private partial def isArithmeticProp (ty : Expr) : MetaM Bool := do
  let ty ← whnf ty
  match ty.getAppFn.constName? with
  -- Typeclass-based comparisons
  | some ``LE.le | some ``LT.lt | some ``GE.ge | some ``GT.gt =>
    -- Verify arguments are Nat or Int typed
    let args := ty.getAppArgs
    if args.size >= 1 then
      let argTy ← whnf args[0]!
      return argTy.isConstOf ``Nat || argTy.isConstOf ``Int
    return false
  -- Type-specific comparisons (after whnf, typeclass versions reduce to these)
  | some ``Nat.le | some ``Nat.lt =>
    return true  -- Already known to be Nat
  | some ``Int.le | some ``Int.lt =>
    return true  -- Already known to be Int
  | some ``Eq | some ``Ne =>
    -- For Eq/Ne, check the type argument (first arg)
    let args := ty.getAppArgs
    if args.size >= 1 then
      let argTy ← whnf args[0]!
      return argTy.isConstOf ``Nat || argTy.isConstOf ``Int
    return false
  | some ``And =>
    -- Recurse into both conjuncts
    let args := ty.getAppArgs
    if args.size >= 2 then
      let left ← isArithmeticProp args[0]!
      let right ← isArithmeticProp args[1]!
      return left && right
    return false
  | some ``Not =>
    -- Recurse into negated prop
    let args := ty.getAppArgs
    if args.size >= 1 then
      isArithmeticProp args[0]!
    else
      return false
  | _ => return false

/-- Collect local hypotheses that are arithmetic facts omega can use. -/
private def getLocalArithmeticHyps : MetaM (List Expr) := do
  let lctx ← getLCtx
  lctx.foldlM (init := []) fun acc decl => do
    if decl.isImplementationDetail then
      return acc
    let h : Expr := mkFVar decl.fvarId
    let ht ← inferType h
    if (← isProp ht) && (← isArithmeticProp ht) then
      return h :: acc
    else
      return acc

/-- True iff `e` has (whnf) type exactly `Nat` or `Int`. -/
def isNatOrInt (e : Expr) : MetaM Bool := do
  let ty ← whnf (← inferType e)
  pure (ty.isConstOf ``Nat || ty.isConstOf ``Int)

/-- Build `0 : ty` using `mkNumeral` or `Zero.zero`. Returns `none` if neither works. -/
def mkZeroOf (ty : Expr) : MetaM (Option Expr) := do
  let saved ← Meta.saveState
  try
    -- Try OfNat first (most common for Nat, Int, etc.)
    let z ← Lean.Meta.mkNumeral ty 0
    return some z
  catch _ =>
    try
      -- Fallback to Zero.zero for types with Zero but not OfNat
      let z ← mkAppOptM ``Zero.zero #[some ty]
      return some z
    catch _ =>
      return none
  finally
    saved.restore

/-- Check if a hypothesis proves `0 < d` or `d > 0` (positivity).
    Returns true if the hypothesis type matches these patterns for the given divisor.
    NOTE: Don't use whnf here - it unfolds LT.lt to type-specific versions like Real.lt -/
private def isPositivityHyp (hypType : Expr) (d : Expr) : MetaM Bool := do
  -- Check for LT.lt 0 d (i.e., 0 < d)
  if hypType.isAppOfArity ``LT.lt 4 then
    let args := hypType.getAppArgs
    let lhs := args[2]!
    let rhs := args[3]!
    -- Check if lhs is 0 and rhs is our divisor
    let lhsIsZero ← do
      let lhsTy ← inferType lhs
      match ← mkZeroOf lhsTy with
      | some zero => isDefEq lhs zero
      | none => pure false
    if lhsIsZero && (← isDefEq rhs d) then return true
    -- Also check GT form: d > 0 (GT.gt d 0 which is LT.lt 0 d in Mathlib)
    pure false
  -- Check for GT.gt d 0 (i.e., d > 0)
  else if hypType.isAppOfArity ``GT.gt 4 then
    let args := hypType.getAppArgs
    let lhs := args[2]!
    let rhs := args[3]!
    let rhsIsZero ← do
      let rhsTy ← inferType rhs
      match ← mkZeroOf rhsTy with
      | some zero => isDefEq rhs zero
      | none => pure false
    if rhsIsZero && (← isDefEq lhs d) then return true
    pure false
  -- Check for LE.le 1 d or GE.ge d 1 (implies 0 < d for positive ordered types)
  else if hypType.isAppOfArity ``LE.le 4 then
    let args := hypType.getAppArgs
    let lhs := args[2]!
    let rhs := args[3]!
    -- Check if lhs is 1 and rhs is our divisor (1 ≤ d implies 0 < d)
    let lhsIsOne ← do
      let lhsTy ← inferType lhs
      try
        let one ← Lean.Meta.mkNumeral lhsTy 1
        isDefEq lhs one
      catch _ => pure false
    if lhsIsOne && (← isDefEq rhs d) then return true
    pure false
  else if hypType.isAppOfArity ``GE.ge 4 then
    let args := hypType.getAppArgs
    let lhs := args[2]!
    let rhs := args[3]!
    -- Check if rhs is 1 and lhs is our divisor (d ≥ 1 implies 0 < d)
    let rhsIsOne ← do
      let rhsTy ← inferType rhs
      try
        let one ← Lean.Meta.mkNumeral rhsTy 1
        isDefEq rhs one
      catch _ => pure false
    if rhsIsOne && (← isDefEq lhs d) then return true
    pure false
  else
    pure false

/-- Search local context for a positivity hypothesis about `d`. -/
private def findPositivityHyp (d : Expr) : MetaM Bool := do
  let lctx ← getLCtx
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let hypType ← inferType (mkFVar decl.fvarId)
    if ← isPositivityHyp hypType d then
      return true
  return false

/-- Grind config for guard proofs (d ≠ 0, b ≤ a, 0 ≤ x, etc.).
    Strict caps for performance. -/
private def grindConfigGuard : Lean.Grind.Config where
  splits := 3
  ematch := 2
  gen := 3
  instances := 50
  canonHeartbeats := 400
  splitMatch := false
  splitIte := false
  splitIndPred := false
  splitImp := false
  matchEqs := false
  ext := false
  extAll := false
  funext := false
  ring := true
  ringSteps := 500
  linarith := true
  cutsat := true
  ac := false
  acSteps := 200
  mbtc := false
  verbose := false
  trace := false
  abstractProof := false

/-- Grind config for proving False from hypotheses (vacuity checking).
    More generous limits since vacuity detection is high-value. -/
private def grindConfigVacuity : Lean.Grind.Config where
  splits := 5
  ematch := 4
  gen := 5
  instances := 200
  canonHeartbeats := 800
  splitMatch := true
  splitIte := true
  splitIndPred := false
  splitImp := true
  matchEqs := true
  ext := false
  extAll := false
  funext := false
  ring := true
  ringSteps := 2000
  linarith := true
  cutsat := true
  ac := true
  acSteps := 500
  mbtc := true
  verbose := false
  trace := false
  abstractProof := false

/-- Try to close `mvarId` using grind with the given config.
    Side-effect free (restores meta state). -/
private def tryGrind? (mvarId : MVarId) (config : Lean.Grind.Config) : MetaM (Option ProvedBy) := do
  let saved ← Meta.saveState
  try
    let params ← Lean.Meta.Grind.mkParams config
    let result ← Lean.Meta.Grind.main mvarId params (pure ())
    if result.failure?.isNone then return some .grind
    else return none
  catch _ => return none
  finally saved.restore

/--
Try to prove `goal` using a controlled sequence:
1) `assumptionCore` (catches direct hypotheses)
2) `omega` (Nat/Int linear arithmetic), by first turning the goal into `False`
   via `falseOrByContra`, then calling `Lean.Elab.Tactic.Omega.omega` on local hyps.
3) `grind` (SMT-style solver with linear arithmetic, ring, congruence closure)

Note: simp is disabled for performance - the full Mathlib simp set is too slow.

This function is side-effect free (restores meta state).
-/
def tryProve? (goal : Expr) (useOmega : Bool := true) (useGrind : Bool := false)
    : MetaM (Option ProvedBy) := do
  let saved ← Meta.saveState
  try
    let m ← mkFreshExprMVar goal
    let g := m.mvarId!

    -- 1) assumption (very fast)
    if (← g.withContext <| g.assumptionCore) then
      return some .assumption

    -- 2) omega (when enabled) - can be slow, but necessary for Nat/Int guards
    if useOmega then
      let g? ← g.withContext <| g.falseOrByContra
      match g? with
      | none =>
          if ← g.isAssigned then
            return some .byContra
          else
            pure ()
      | some gFalse =>
          -- Pass ALL propositional hypotheses to omega, not just pre-filtered
          -- arithmetic ones. The previous getLocalArithmeticHyps filter was too
          -- aggressive: whnf could unfold to unrecognized forms, and chained
          -- inequalities (a ≥ c, c ≥ b ⟹ b ≤ a) were dropped.
          -- Omega is robust and will ignore irrelevant hypotheses.
          let facts ← gFalse.withContext getLocalPropHyps
          Lean.Elab.Tactic.Omega.omega facts gFalse
          if ← gFalse.isAssigned then
            return some .omega

    -- 3) grind (when enabled, last resort — SMT-style solver)
    if useGrind then
      -- Need a fresh mvar since the previous one may have been partially assigned
      let m' ← mkFreshExprMVar goal
      let g' := m'.mvarId!
      if let some result ← tryGrind? g' grindConfigGuard then
        return some result

    return none
  catch _ =>
    return none
  finally
    saved.restore

/-- Try to prove `goal` is False from hypotheses, using omega then grind.
    Used for vacuity checking where we want maximum power. -/
def tryProveVacuity? (goal : Expr) : MetaM (Option ProvedBy) := do
  let saved ← Meta.saveState
  try
    let m ← mkFreshExprMVar goal
    let g := m.mvarId!

    -- 1) assumption (very fast)
    if (← g.withContext <| g.assumptionCore) then
      return some .assumption

    -- 2) omega first (fast for Nat/Int contradictions)
    let g? ← g.withContext <| g.falseOrByContra
    match g? with
    | none =>
        if ← g.isAssigned then
          return some .byContra
        else
          pure ()
    | some gFalse =>
        let facts ← gFalse.withContext getLocalPropHyps
        Lean.Elab.Tactic.Omega.omega facts gFalse
        if ← gFalse.isAssigned then
          return some .omega

    -- 3) grind only after omega fails (more powerful but slower)
    let m' ← mkFreshExprMVar goal
    let g' := m'.mvarId!
    if let some result ← tryGrind? g' grindConfigVacuity then
      return some result

    return none
  catch _ =>
    return none
  finally
    saved.restore

/-- Like `tryProve?`, but run it under an explicit `(lctx, insts)` snapshot. -/
def tryProveIn? (snap : LocalCtxSnapshot) (goal : Expr) (useOmega : Bool := true)
    (useGrind : Bool := false) : MetaM (Option ProvedBy) :=
  withSnapshot snap (tryProve? goal useOmega useGrind)

/-- Try to prove a dangerous condition (e.g., d = 0, a < b, x < 0).
    Uses the same prover stack as guard proving but with grind enabled by default
    for maximum power. Intended for unsafety proofs when safety cannot be established. -/
def tryProveUnsafety? (goal : Expr) (snap : LocalCtxSnapshot)
    (useOmega : Bool := true) (useGrind : Bool := true)
    : MetaM (Option ProvedBy) :=
  withSnapshot snap (tryProve? goal (useOmega := useOmega) (useGrind := useGrind))

/--
Division-by-zero guard prover.

SOUNDNESS: Accepts these as valid guards:
- Direct `d ≠ 0` or `0 ≠ d` hypotheses
- Positivity hypotheses: `0 < d`, `d > 0`, `1 ≤ d`, `d ≥ 1`
  (for ordered types, positive implies nonzero)

For Nat/Int divisors, it enables `omega` and `simp` (can derive nonzero from
linear facts like `2 ≤ d` or structural facts like `Nat.succ n`).

Side-effect free.
-/
def proveDivisorSafe? (d : Expr) (useGrind : Bool := false) : MetaM (Option ProvedBy) := do
  let saved ← Meta.saveState
  try
    let ty ← inferType d
    let omegaOk := (← isNatOrInt d)

    match (← mkZeroOf ty) with
    | none => return none
    | some zero =>
        -- Primary goal: d ≠ 0
        -- omega can derive this from order facts (0 < d, d > 0, etc.)
        try
          let g1 ← Lean.Meta.mkAppM ``Ne #[d, zero]
          if let some how ← tryProve? g1 omegaOk useGrind then return some how
        catch _ => pure ()

        -- Also try 0 ≠ d (symmetric form)
        try
          let g2 ← Lean.Meta.mkAppM ``Ne #[zero, d]
          if let some how ← tryProve? g2 omegaOk useGrind then return some how
        catch _ => pure ()

        -- For non-Nat/Int types (Real, Complex, etc.), check positivity hypotheses
        -- Since 0 < d implies d ≠ 0 in any ordered semiring
        if !omegaOk then
          if ← findPositivityHyp d then
            return some .positivity

        return none
  finally
    saved.restore

/-- Nat subtraction guard prover: prove `b ≤ a`. (Uses omega, optionally grind.) -/
def proveNatSubGuard? (a b : Expr) (useGrind : Bool := false) : MetaM (Option ProvedBy) := do
  let saved ← Meta.saveState
  try
    let goal ← Lean.Meta.mkLe b a
    tryProve? goal (useOmega := true) (useGrind := useGrind)
  finally
    saved.restore

/-- Int-to-Nat guard prover: prove `0 ≤ x`. (Uses omega.) -/
def proveIntNonneg? (x : Expr) : MetaM (Option ProvedBy) := do
  let saved ← Meta.saveState
  try
    let zero : Expr := Lean.mkIntLit 0
    let goal ← Lean.Meta.mkLe zero x
    tryProve? goal (useOmega := true)
  finally
    saved.restore

/-- Convert ProvedBy to a human-readable string for evidence -/
def ProvedBy.toString : ProvedBy → String
  | .assumption => "assumption"
  | .simp => "simp"
  | .byContra => "byContra"
  | .omega => "omega"
  | .positivity => "positivity"
  | .grind => "grind"

end SemanticGuards
end AtpLinter
