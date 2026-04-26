/-
  Guard proof orchestration.

  This module owns the solver order and checker-facing guard entry points.
  Keep proof order stable: changing it can change `provedBy` tags and benchmark
  output even when final safety decisions are logically equivalent.
-/

import Lean
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.Assumption
import Lean.Elab.Tactic.FalseOrByContra
import Lean.Elab.Tactic.Omega
import Lean.Meta.Tactic.Grind
import AtpLinter.GuardFacts
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.CharZero.Defs

open Lean Meta
open Qq

namespace AtpLinter
namespace SemanticGuards

/-- Where a guard proof came from (useful for debugging / stats). -/
inductive ProvedBy where
  | assumption  -- Found directly in local context via assumptionCore
  | structural  -- Built from reusable algebraic nonzero lemmas
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
  lia := true
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
  lia := true
  ac := true
  acSteps := 500
  mbtc := true
  verbose := false
  trace := false
  abstractProof := false

/-- Try to close `mvarId` using grind with the given config.
    Side-effect free (restores meta state). -/
private def tryGrind? (mvarId : MVarId) (config : Lean.Grind.Config) :
    MetaM (Option ProvedBy) := do
  let saved ← Meta.saveState
  try
    let params ← Lean.Meta.Grind.mkParams config default
    let result ← Lean.Meta.Grind.main mvarId params
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
private def tryProveProof? (goal : Expr) (useOmega : Bool := true) (useGrind : Bool := false)
    : MetaM (Option (Expr × ProvedBy)) := do
  let saved ← Meta.saveState
  try
    let m ← mkFreshExprMVar goal
    let g := m.mvarId!

    -- 1) assumption (very fast)
    if (← g.withContext <| g.assumptionCore) then
      return some ((← instantiateMVars m), ProvedBy.assumption)

    -- 2) exact fact lookup, including let-bound derived facts and bounded
    -- universal instantiations that match the goal exactly.
    if let some proof ← g.withContext <| tryExactLocalFactProof? goal then
      return some (proof, ProvedBy.assumption)
    if let some proof ← g.withContext <| tryForallInstantiatedProof? goal then
      return some (proof, ProvedBy.assumption)

    -- 3) positivity (fast for nonnegativity/nonzeroness goals over ordered structures)
    let solvedPos ← g.withContext do
      let t : Q(Prop) ← g.getType
      if t.approxDepth.toNat > 64 then
        return false
      let shouldTry ← match t with
        | ~q(@LE.le $α $_a $z $e) => pure (isSyntacticZero z)
        | ~q(@LT.lt $α $_a $z $e) => pure (isSyntacticZero z)
        | ~q(@Ne $α $e $z) => pure (isSyntacticZero z)
        | ~q(@Ne $α $z $e) => pure (isSyntacticZero z)
        | _ => pure false
      if !shouldTry then
        return false
      let proof ← withOptions (fun opts => maxRecDepth.set opts 1000000) do
        Mathlib.Meta.Positivity.solve t
      g.assign proof
      pure true
    if solvedPos && (← g.isAssigned) then
      return some ((← instantiateMVars m), ProvedBy.positivity)

    -- 4) omega (when enabled) - can be slow, but necessary for Nat/Int guards
    if useOmega then
      let g? ← g.withContext <| g.falseOrByContra
      match g? with
      | none =>
          if ← g.isAssigned then
            return some ((← instantiateMVars m), ProvedBy.byContra)
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
            return some ((← instantiateMVars m), ProvedBy.omega)

    -- 5) grind (when enabled, last resort — SMT-style solver)
    if useGrind then
      -- Need a fresh mvar since the previous one may have been partially assigned
      let m' ← mkFreshExprMVar goal
      let g' := m'.mvarId!
      let params ← Lean.Meta.Grind.mkParams grindConfigGuard default
      let result ← Lean.Meta.Grind.main g' params
      if result.failure?.isNone then
        return some ((← instantiateMVars m'), ProvedBy.grind)

    return none
  catch _ =>
    return none
  finally
    saved.restore

def tryProve? (goal : Expr) (useOmega : Bool := true) (useGrind : Bool := false)
    : MetaM (Option ProvedBy) := do
  return (← tryProveProof? goal (useOmega := useOmega) (useGrind := useGrind)).map Prod.snd

/-- Try to prove `d ≠ 0` by unwrapping a cast and proving nonzero on the source type.
    Handles `Nat.cast`, `Int.cast`, and `Rat.cast` when the target type has `CharZero`
    (plus `DivisionRing` for Rat). For example, proves `(↑n : ℝ) ≠ 0` from `n ≠ 0`
    on ℕ via `Nat.cast_ne_zero`. Returns a proof term and `ProvedBy` tag if successful. -/
partial def proveCastTransport? (d : Expr) (useGrind : Bool := false)
    : MetaM (Option (Expr × ProvedBy)) := do
  let saved ← Meta.saveState
  try
    -- Check for Nat.cast (arity 3: type, NatCast instance, value)
    if d.isAppOfArity ``Nat.cast 3 then
      let args := d.getAppArgs
      let targetTy := args[0]!
      let innerVal := args[2]!
      -- Nat.cast_ne_zero requires CharZero on the target type
      try
        let _ ← synthInstance (← mkAppM ``CharZero #[targetTy])
        let natZero := Lean.mkNatLit 0
        let innerGoal ← mkAppM ``Ne #[innerVal, natZero]
        if let some (innerProof, _) ← tryProveProof? innerGoal true useGrind then
          let transported ← mkAppM ``Iff.mpr #[← mkAppM ``Nat.cast_ne_zero #[innerVal], innerProof]
          return some (transported, .structural)
      catch _ => pure ()

    -- Check for Int.cast (arity 3: type, IntCast instance, value)
    if d.isAppOfArity ``Int.cast 3 then
      let args := d.getAppArgs
      let targetTy := args[0]!
      let innerVal := args[2]!
      try
        let _ ← synthInstance (← mkAppM ``CharZero #[targetTy])
        let intZero := Lean.mkIntLit 0
        let innerGoal ← mkAppM ``Ne #[innerVal, intZero]
        if let some (innerProof, _) ← tryProveProof? innerGoal true useGrind then
          let transported ← mkAppM ``Iff.mpr #[← mkAppM ``Int.cast_ne_zero #[innerVal], innerProof]
          return some (transported, .structural)
      catch _ => pure ()

    -- Check for Rat.cast (arity 3: type, RatCast instance, value)
    if d.isAppOfArity ``Rat.cast 3 then
      let args := d.getAppArgs
      let targetTy := args[0]!
      let innerVal := args[2]!
      try
        let _ ← synthInstance (← mkAppM ``CharZero #[targetTy])
        match ← mkZeroOf (mkConst ``Rat) with
        | some ratZero =>
          let innerGoal ← mkAppM ``Ne #[innerVal, ratZero]
          if let some (innerProof, _) ← tryProveProof? innerGoal false useGrind then
            let transported ← mkAppM ``Iff.mpr #[← mkAppM ``Rat.cast_ne_zero #[innerVal], innerProof]
            return some (transported, .structural)
        | none => pure ()
      catch _ => pure ()

    return none
  catch _ => return none
  finally saved.restore

/-- Try to prove `e ≠ 0` for a sub-expression (factor or base), using the
    prover pipeline plus cast transport. Used by proveStructuralNonzero? to
    compose structural decomposition with cast unwrapping. -/
private def proveSubExprNonzero? (e : Expr) (useGrind : Bool := false)
    : MetaM (Option (Expr × ProvedBy)) := do
  let ty ← inferType e
  match ← mkZeroOf ty with
  | none => return none
  | some zero =>
    let goal ← Lean.Meta.mkAppM ``Ne #[e, zero]
    if let some result ← tryProveProof? goal (← isNatOrInt e) useGrind then
      return some result
    if let some result ← proveCastTransport? e useGrind then
      return some result
    return none

/-- Recursively assemble nonzero proofs for simple algebraic expressions.
    Composes with cast transport so that `(↑m : ℝ) * (↑n : ℝ)` is handled
    when `m ≠ 0` and `n ≠ 0` are in the local context. -/
partial def proveStructuralNonzero? (d : Expr) (useGrind : Bool := false)
    : MetaM (Option (Expr × ProvedBy)) := do
  let ty ← inferType d
  match (← mkZeroOf ty) with
  | none => return none
  | some _ =>
      if d.isAppOfArity ``HMul.hMul 6 then
        let args := d.getAppArgs
        let lhs := args[4]!
        let rhs := args[5]!
        if let some (lhsProof, _) ← proveSubExprNonzero? lhs useGrind then
          if let some (rhsProof, _) ← proveSubExprNonzero? rhs useGrind then
            try
              return some ((← mkAppM ``mul_ne_zero #[lhsProof, rhsProof]), ProvedBy.structural)
            catch _ => pure ()

      if d.isAppOfArity ``HPow.hPow 6 then
        let args := d.getAppArgs
        let base := args[4]!
        let exp := args[5]!
        if let some (baseProof, _) ← proveSubExprNonzero? base useGrind then
          try
            return some ((← mkAppM ``pow_ne_zero #[exp, baseProof]), ProvedBy.structural)
          catch _ => pure ()

      return none

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
- Proofs of `d ≠ 0` derivable by Lean tactics from standard arithmetic facts
- Standard Real/Complex magnitude lower bounds such as `1 ≤ |d|` or `1 ≤ ‖d‖`

For Nat/Int divisors, it enables `omega` for linear facts like `2 ≤ d`.

Side-effect free.
-/
def proveDivisorSafe? (d : Expr) (useGrind : Bool := false) : MetaM (Option ProvedBy) := do
  let saved ← Meta.saveState
  try
    withGuardFacts do
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

          -- Reusable algebraic closure rules like `mul_ne_zero` and `pow_ne_zero`.
          if let some (_, how) ← proveStructuralNonzero? d useGrind then
            return some how

          -- Cast transport: unwrap Nat.cast/Int.cast, prove nonzero on source
          -- type, transport via Nat.cast_ne_zero / Int.cast_ne_zero (CharZero).
          if let some (_, how) ← proveCastTransport? d useGrind then
            return some how

          -- Bare positive bounds are valid nonzero evidence for standard
          -- ordered scalar domains, but not for arbitrary ordered instances.
          if ← findStandardPositiveBoundHyp d then
            return some .positivity

          -- Standard magnitude lower bounds, including instantiated universal
          -- facts such as `h z : 1 ≤ |f z|`, imply nonzeroness for Real/Complex.
          if ← findStandardMagnitudeLowerBoundHyp d then
            return some .structural

          return none
  finally
    saved.restore

/-- Nat subtraction guard prover: prove `b ≤ a`. (Uses omega, optionally grind.)
    Enriches the local context with derived facts (Subtype.property, Fin.isLt)
    and expanded conjunctions before proving, matching proveDivisorSafe?. -/
def proveNatSubGuard? (a b : Expr) (useGrind : Bool := false) : MetaM (Option ProvedBy) := do
  let saved ← Meta.saveState
  try
    withGuardFacts do
      let goal ← Lean.Meta.mkLe b a
      tryProve? goal (useOmega := true) (useGrind := useGrind)
  finally
    saved.restore

/-- Int-to-Nat guard prover: prove `0 ≤ x`. (Uses omega.)
    Enriches the local context with derived facts (Subtype.property, Fin.isLt)
    and expanded conjunctions before proving, matching proveDivisorSafe?. -/
def proveIntNonneg? (x : Expr) : MetaM (Option ProvedBy) := do
  let saved ← Meta.saveState
  try
    withGuardFacts do
      let zero : Expr := Lean.mkIntLit 0
      let goal ← Lean.Meta.mkLe zero x
      tryProve? goal (useOmega := true) (useGrind := true)
  finally
    saved.restore

/-- Convert ProvedBy to a human-readable string for evidence -/
def ProvedBy.toString : ProvedBy → String
  | .assumption => "assumption"
  | .structural => "structural"
  | .simp => "simp"
  | .byContra => "byContra"
  | .omega => "omega"
  | .positivity => "positivity"
  | .grind => "grind"

end SemanticGuards
end AtpLinter
