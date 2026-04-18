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
import AtpLinter.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith

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
  | nlinarith   -- Closed by Mathlib's nonlinear linarith variant
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


/-- Map from a Finset/Set interval-head name to the `mem_*` iff lemma whose `.mp`
    extracts the order facts we want in scope. Returns `none` when the container
    head isn't a recognised interval shape. -/
private def intervalMemLemma? (headName : Name) : Option Name :=
  match headName with
  -- Finset intervals
  | ``Finset.Icc   => some ``Finset.mem_Icc
  | ``Finset.Ico   => some ``Finset.mem_Ico
  | ``Finset.Ioc   => some ``Finset.mem_Ioc
  | ``Finset.Ioo   => some ``Finset.mem_Ioo
  | ``Finset.range => some ``Finset.mem_range
  -- Set intervals
  | ``Set.Icc      => some ``Set.mem_Icc
  | ``Set.Ico      => some ``Set.mem_Ico
  | ``Set.Ioc      => some ``Set.mem_Ioc
  | ``Set.Ioo      => some ``Set.mem_Ioo
  | ``Set.Ici      => some ``Set.mem_Ici
  | ``Set.Iic      => some ``Set.mem_Iic
  | ``Set.Ioi      => some ``Set.mem_Ioi
  | ``Set.Iio      => some ``Set.mem_Iio
  | _              => none

/-- Apply an iff-lemma with all-implicit args by instantiating the lemma with
    fresh mvars, unifying its LHS with the type of `h`, synthesising any
    remaining instance-implicit mvars, and projecting via `Iff.mp`. -/
private def tryApplyMemIff (lemmaName : Name) (h : Expr) :
    MetaM (Option Expr) := do
  try
    let lemmaConst ← mkConstWithFreshMVarLevels lemmaName
    let lemmaType ← inferType lemmaConst
    let (mvars, binderInfos, iffType) ← forallMetaTelescope lemmaType
    let some (lhs, _) := iffType.iff? | return none
    let hType ← inferType h
    unless (← isDefEq lhs hType) do return none
    for i in [:mvars.size] do
      if binderInfos[i]!.isInstImplicit then
        try
          let mvarType ← inferType mvars[i]!
          let inst ← synthInstance mvarType
          unless (← isDefEq mvars[i]! inst) do return none
        catch _ => return none
    let iffProof := mkAppN lemmaConst mvars
    some <$> mkAppM ``Iff.mp #[iffProof, h]
  catch _ =>
    return none

/-- Resolve let-bindings to expose the container's concrete head. Critically
    does NOT whnf — that would unfold reducible defs like `Finset.Icc` into
    their constructor form, losing the name we match on. -/
private def resolveContainer (container : Expr) : MetaM Expr := do
  let stepped ← instantiateMVars container
  Meta.transform stepped (post := fun e => do
    if e.isFVar then
      if let some decl := (← getLCtx).find? e.fvarId! then
        if let some value := decl.value? then return .done value
    return .done e)

/-- Try to derive order facts from an `elem ∈ interval` hypothesis via the
    corresponding `mem_*` iff lemma. -/
private def tryIntervalMembershipFact (h ht : Expr) : MetaM (Option Expr) := do
  unless ht.isAppOfArity ``Membership.mem 5 do return none
  let container := ht.getAppArgs[3]!
  let containerResolved ← resolveContainer container
  let hn := containerResolved.getAppFn.constName?.getD .anonymous
  let some lemmaName := intervalMemLemma? hn | return none
  tryApplyMemIff lemmaName h

/-- Introduce proposition-valued structure fields that are worth exposing to the
    guard prover: `Subtype.property`, `Fin.isLt`, Finset/Set interval membership
    bounds, and `Nat.Prime`/`Fact (Nat.Prime _)` ⇒ `2 ≤ p`. -/
def withDerivedLocalFacts (k : MetaM α) : MetaM α := do
  let lctx ← getLCtx
  let facts ← lctx.foldlM (init := []) fun acc decl => do
    if decl.isImplementationDetail then
      return acc
    let h : Expr := mkFVar decl.fvarId
    let htRaw ← inferType h
    let ht ← whnf htRaw
    -- Subtype.property
    if ht.getAppFn.isConstOf ``Subtype then
      try return (← mkAppM ``Subtype.property #[h]) :: acc
      catch _ => return acc
    -- Fin.isLt
    if ht.getAppFn.isConstOf ``Fin then
      try return (← mkAppM ``Fin.isLt #[h]) :: acc
      catch _ => return acc
    -- Nat.Prime p  ⇒  2 ≤ p  (check raw type; Nat.Prime is reducible in Mathlib)
    if htRaw.isAppOfArity ``Nat.Prime 1 then
      try return (← mkAppM ``Nat.Prime.two_le #[h]) :: acc
      catch _ => return acc
    -- Fact (Nat.Prime p)  ⇒  2 ≤ p  (via Fact.out)
    if htRaw.isAppOfArity ``Fact 1 then
      let inner := htRaw.appArg!
      if inner.isAppOfArity ``Nat.Prime 1 then
        try
          let primePf ← mkAppM ``Fact.out #[h]
          return (← mkAppM ``Nat.Prime.two_le #[primePf]) :: acc
        catch _ => return acc
    -- elem ∈ Finset.Icc/Ico/Ioc/Ioo/range or Set.Icc/.../Ioi/Iio
    -- Use htRaw: whnf can unfold `Membership.mem` past the head we want to match.
    if let some memFact ← tryIntervalMembershipFact h htRaw then
      return memFact :: acc
    return acc
  let rec go (todo : List Expr) : MetaM α := do
    match todo with
    | [] => k
    | fact :: rest =>
        let factType ← inferType fact
        withLetDecl `_atpFact factType fact fun _ =>
          go rest
  go facts


/-- Expand asserted local conjunctions into their component proofs. -/
partial def withExpandedAndHyps (k : MetaM α) : MetaM α := do
  let lctx ← getLCtx
  let hyps ← lctx.foldlM (init := []) fun acc decl => do
    if decl.isImplementationDetail then
      return acc
    else
      let h : Expr := mkFVar decl.fvarId
      let ht ← inferType h
      if (← isProp ht) then
        return h :: acc
      else
        return acc
  let rec go (todo : List Expr) : MetaM α := do
    match todo with
    | [] => k
    | h :: hs =>
        let ht ← whnf (← inferType h)
        if ht.isAppOfArity ``And 2 then
          let args := ht.getAppArgs
          let lhsType := args[0]!
          let rhsType := args[1]!
          let lhsProof ← mkAppM ``And.left #[h]
          let rhsProof ← mkAppM ``And.right #[h]
          withLetDecl `_atpAndLeft lhsType lhsProof fun lhsFVar => do
            withLetDecl `_atpAndRight rhsType rhsProof fun rhsFVar => do
              go (lhsFVar :: rhsFVar :: hs)
        else
          go hs
  go hyps


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
      let z ← mkAppOptM ``Zero.zero #[some ty, none]
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
private def tryGrind? (mvarId : MVarId) (config : Lean.Grind.Config) : MetaM (Option ProvedBy) := do
  let saved ← Meta.saveState
  try
    let params ← Lean.Meta.Grind.mkParams config default
    let result ← Lean.Meta.Grind.main mvarId params
    if result.failure?.isNone then return some .grind
    else return none
  catch _ => return none
  finally saved.restore

/-- Try to close a fresh mvar for `goal` using nlinarith (linarith with the
    nonlinear preprocessor extras). Bounded by a tight heartbeat budget so a
    single unsolvable goal can't dominate per-decl runtime (nlinarith's
    nonlinear preprocessing is exponential in the number of hypotheses).
    Side-effect free. -/
private def tryNlinarith? (goal : Expr) : MetaM (Option (Expr × ProvedBy)) := do
  let saved ← Meta.saveState
  try
    withOptions (fun opts => opts.set `maxHeartbeats (20000 : Nat)) do
      let m ← mkFreshExprMVar goal
      let g := m.mvarId!
      let baseCfg : Mathlib.Tactic.Linarith.LinarithConfig := {}
      let cfg := { baseCfg with
        preprocessors := baseCfg.preprocessors.concat Mathlib.Tactic.Linarith.nlinarithExtras }
      Mathlib.Tactic.Linarith.linarith false [] cfg g
      if ← g.isAssigned then
        return some ((← instantiateMVars m), ProvedBy.nlinarith)
      return none
  catch _ => return none
  finally saved.restore


/-- Try to close a positivity-shaped goal using Mathlib's positivity engine. -/
private def tryPositivity? (goal : Expr) : MetaM (Option ProvedBy) := do
  let saved ← Meta.saveState
  try
    let m ← mkFreshExprMVar goal
    let g := m.mvarId!
    let solved ← g.withContext do
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
    if solved && (← g.isAssigned) then
      return some .positivity
    return none
  catch _ =>
    return none
  finally
    saved.restore

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
    (useNlinarith : Bool := false) : MetaM (Option (Expr × ProvedBy)) := do
  let saved ← Meta.saveState
  try
    let m ← mkFreshExprMVar goal
    let g := m.mvarId!

    -- 1) assumption (very fast)
    if (← g.withContext <| g.assumptionCore) then
      return some ((← instantiateMVars m), ProvedBy.assumption)

    -- 2) positivity (fast for nonnegativity/nonzeroness goals over ordered structures)
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

    -- 3) omega (when enabled) - can be slow, but necessary for Nat/Int guards
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

    -- 4) grind (when enabled — SMT-style solver)
    if useGrind then
      -- Need a fresh mvar since the previous one may have been partially assigned
      let m' ← mkFreshExprMVar goal
      let g' := m'.mvarId!
      let params ← Lean.Meta.Grind.mkParams grindConfigGuard default
      let result ← Lean.Meta.Grind.main g' params
      if result.failure?.isNone then
        return some ((← instantiateMVars m'), ProvedBy.grind)

    -- 5) nlinarith (when enabled — nonlinear linarith, last resort for real arith)
    if useNlinarith then
      if let some result ← tryNlinarith? goal then
        return some result

    return none
  catch _ =>
    return none
  finally
    saved.restore

def tryProve? (goal : Expr) (useOmega : Bool := true) (useGrind : Bool := false)
    (useNlinarith : Bool := false) : MetaM (Option ProvedBy) := do
  return (← tryProveProof? goal (useOmega := useOmega) (useGrind := useGrind)
    (useNlinarith := useNlinarith)).map Prod.snd


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
- Positivity hypotheses: `0 < d`, `d > 0`, `1 ≤ d`, `d ≥ 1`
  (for ordered types, positive implies nonzero)

For Nat/Int divisors, it enables `omega` and `simp` (can derive nonzero from
linear facts like `2 ≤ d` or structural facts like `Nat.succ n`).

Side-effect free.
-/
def proveDivisorSafe? (d : Expr) (useGrind : Bool := false) : MetaM (Option ProvedBy) := do
  let saved ← Meta.saveState
  try
    withDerivedLocalFacts <| withExpandedAndHyps do
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

          -- For ordered targets, positivity is often easier to establish than
          -- nonzeroness directly, especially for products, powers, and casted terms.
          try
            let gPos ← Lean.Meta.mkLt zero d
            if let some _ ← tryProve? gPos omegaOk useGrind then
              return some .positivity
          catch _ => pure ()

          -- For non-Nat/Int types (Real, Complex, etc.), check positivity hypotheses
          -- Since 0 < d implies d ≠ 0 in any ordered semiring
          if !omegaOk then
            if ← findPositivityHyp d then
              return some .positivity

          return none
  finally
    saved.restore

/-- Nat subtraction guard prover: prove `b ≤ a`. (Uses omega, optionally grind.)
    Enriches the local context with derived facts (Subtype.property, Fin.isLt)
    and expanded conjunctions before proving, matching proveDivisorSafe?. -/
def proveNatSubGuard? (a b : Expr) (useGrind : Bool := false) : MetaM (Option ProvedBy) := do
  let saved ← Meta.saveState
  try
    withDerivedLocalFacts <| withExpandedAndHyps do
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
    withDerivedLocalFacts <| withExpandedAndHyps do
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
  | .nlinarith => "nlinarith"

end SemanticGuards
end AtpLinter
