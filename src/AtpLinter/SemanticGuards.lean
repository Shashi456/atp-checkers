/-
  Semantic Guard Prover

  Instead of syntactically pattern-matching hypothesis types,
  we build a goal and try to prove it using tactics.

  Approach:
  1. Try `assumption` (catches direct hypotheses like `h : x ≠ 0`)
  2. Try Mathlib's positivity engine for standard nonzero/nonnegative goals
  3. Try `omega` (Nat/Int linear arithmetic), via falseOrByContra pipeline
  4. Try structural nonzero/cast-transport rules and optional `grind`
  5. Side-effect free: saves/restores meta state

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
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.CharZero.Defs

open Lean Meta
open Qq

namespace AtpLinter
namespace SemanticGuards

private def maxForallCandidateTerms : Nat := 24
private def maxForallInstantiatedFacts : Nat := 16
private def maxForallDefEqAttempts : Nat := 256
private def maxForallMatchesPerBinder : Nat := 8
private def maxStructureFieldFactsPerLocal : Nat := 8
private def maxStructureFieldFactsTotal : Nat := 64

private def arrayTake {α : Type} (xs : Array α) (limit : Nat) : Array α := Id.run do
  let mut out := #[]
  for x in xs do
    if out.size >= limit then
      break
    out := out.push x
  return out

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

/-- Project proposition-valued fields from a structure-valued local. This covers
    user structures like `{ val : Nat, ne_zero : val ≠ 0 }` without opening
    typeclass instances or large implementation-detail locals. -/
private def collectPropStructureFieldFacts (h ht : Expr)
    (limit : Nat := maxStructureFieldFactsPerLocal) : MetaM (Array Expr) := do
  match ht.getAppFn with
  | .const structName _ =>
      let env ← getEnv
      if (getStructureInfo? env structName).isNone then
        return #[]
      let fields := getStructureFieldsFlattened env structName (includeSubobjectFields := false)
      let mut facts := #[]
      for fieldName in fields do
        if facts.size >= limit then
          break
        match getProjFnForField? env structName fieldName with
        | none => pure ()
        | some projFn =>
            try
              let fact ← mkAppM projFn #[h]
              let factType ← inferType fact
              if ← isProp factType then
                facts := facts.push fact
            catch _ =>
              pure ()
      return facts
  | _ => return #[]

/-- Introduce proposition-valued structure fields that are worth exposing to the
    guard prover, such as `Subtype.property` and `Fin.isLt`. -/
def withDerivedLocalFacts (k : MetaM α) : MetaM α := do
  let lctx ← getLCtx
  let (facts, _) ← lctx.foldlM (init := (([] : List Expr), 0)) fun state decl => do
    let (acc, structureFactCount) := state
    if decl.isImplementationDetail then
      return (acc, structureFactCount)
    else
      let h : Expr := mkFVar decl.fvarId
      let ht ← whnf (← inferType h)
      if ht.getAppFn.isConstOf ``Subtype then
        try
          return ((← mkAppM ``Subtype.property #[h]) :: acc, structureFactCount)
        catch _ =>
          return (acc, structureFactCount)
      else if ht.getAppFn.isConstOf ``Fin then
        try
          return ((← mkAppM ``Fin.isLt #[h]) :: acc, structureFactCount)
        catch _ =>
          return (acc, structureFactCount)
      else
        if decl.binderInfo.isInstImplicit || structureFactCount >= maxStructureFieldFactsTotal then
          return (acc, structureFactCount)
        else
          let remaining := maxStructureFieldFactsTotal - structureFactCount
          let perLocal := min maxStructureFieldFactsPerLocal remaining
          let facts ← collectPropStructureFieldFacts h ht perLocal
          let acc := facts.foldl (init := acc) fun acc fact => fact :: acc
          return (acc, structureFactCount + facts.size)
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

/-- Compare expressions without letting unification failures escape. This is
    used only inside callers that already restore Meta state around the whole
    proof attempt, so it avoids per-comparison save/restore overhead. -/
private def isDefEqNoThrow (a b : Expr) : MetaM Bool := do
  try
    isDefEq a b
  catch _ =>
    return false

/-- Compare expressions without letting unification failures escape or leak. -/
private def isDefEqRestoring (a b : Expr) : MetaM Bool := do
  let saved ← Meta.saveState
  try
    isDefEq a b
  catch _ =>
    return false
  finally
    saved.restore

/-- Collect subexpressions that are useful as candidate instantiations for local
    universal hypotheses. The target itself is included first. -/
partial def collectCandidateTerms (e : Expr) : Array Expr :=
  let rec visit (x : Expr) (seen : Array UInt64) (out : Array Expr) : Array UInt64 × Array Expr :=
    let h := x.hash
    if seen.contains h then
      (seen, out)
    else
      let seen := seen.push h
      let out := out.push x
      match x with
      | .app f a =>
          let (seen, out) := visit f seen out
          visit a seen out
      | .lam _ t b _ =>
          let (seen, out) := visit t seen out
          visit b seen out
      | .forallE _ t b _ =>
          let (seen, out) := visit t seen out
          visit b seen out
      | .letE _ t v b _ =>
          let (seen, out) := visit t seen out
          let (seen, out) := visit v seen out
          visit b seen out
      | .mdata _ b =>
          visit b seen out
      | .proj _ _ b =>
          visit b seen out
      | _ => (seen, out)
  let (_, out) := visit e #[] #[]
  out

private def collectCandidateTermsCapped (e : Expr) : Array Expr :=
  arrayTake (collectCandidateTerms e) maxForallCandidateTerms

/-- True when a forall type can be instantiated to a proposition within `fuel`
    binders. This skips ordinary function-valued locals such as `f : α → β`. -/
partial def forallCodomainIsProp (type : Expr) (fuel : Nat) : MetaM Bool := do
  if fuel == 0 then
    return false
  if type.isForall then
    forallCodomainIsProp type.bindingBody! (fuel - 1)
  else
    isProp type

/-- Instantiate a local `∀` proof with bounded candidate combinations. -/
partial def instantiateForallWithCandidatesAux (proof proofType : Expr) (candidates : Array Expr)
    (fuel : Nat) (remaining : Nat) (attempts : Nat) : MetaM (Array Expr × Nat) := do
  if fuel == 0 || remaining == 0 || attempts == 0 then
    return (#[], attempts)
  if !proofType.isForall then
    if ← isProp proofType then
      return (#[proof], attempts)
    return (#[], attempts)

  let domain := proofType.bindingDomain!
  let mut facts := #[]
  let mut attemptsLeft := attempts
  let mut matchesHere := 0
  for cand in candidates do
    if facts.size >= remaining || attemptsLeft == 0 || matchesHere >= maxForallMatchesPerBinder then
      break
    attemptsLeft := attemptsLeft - 1
    try
      let candType ← inferType cand
      if ← isDefEqRestoring candType domain then
        matchesHere := matchesHere + 1
        let proof' := mkApp proof cand
        let proofType' ← inferType proof'
        let (more, attemptsLeft') ← instantiateForallWithCandidatesAux proof' proofType' candidates
          (fuel - 1) (remaining - facts.size) attemptsLeft
        attemptsLeft := attemptsLeft'
        facts := facts ++ more
    catch _ =>
      pure ()
  return (facts, attemptsLeft)

/-- Instantiate a local `∀` proof with bounded candidate combinations. -/
partial def instantiateForallWithCandidates (proof proofType : Expr) (candidates : Array Expr)
    (fuel : Nat) (remaining : Nat) : MetaM (Array Expr) := do
  let (facts, _) ← instantiateForallWithCandidatesAux proof proofType candidates fuel remaining
    maxForallDefEqAttempts
  return facts

/-- Instantiate local `∀` hypotheses with subterms of `target`, exposing facts
    such as `h z : 1 ≤ |f z|` from `h : ∀ z, 1 ≤ |f z|`. -/
def withInstantiatedForallHyps (target : Expr) (k : MetaM α) : MetaM α := do
  let candidates := collectCandidateTermsCapped target
  let lctx ← getLCtx
  let mut facts := #[]
  for decl in lctx do
    if decl.isImplementationDetail then
      continue
    let proof := mkFVar decl.fvarId
    let proofType ← inferType proof
    if !proofType.isForall then
      continue
    if !(← forallCodomainIsProp proofType 4) then
      continue
    let remaining := maxForallInstantiatedFacts - facts.size
    if remaining == 0 then
      break
    let more ← instantiateForallWithCandidates proof proofType candidates 4 remaining
    facts := facts ++ more

  let rec go (i : Nat) : MetaM α := do
    if h : i < facts.size then
      let fact := facts[i]
      let factType ← inferType fact
      withLetDecl `_atpForallInst factType fact fun _ =>
        go (i + 1)
    else
      k
  go 0

/-- Find a local propositional fact whose type is definitionally equal to the
    goal. Unlike `assumptionCore`, this also sees let-bound derived facts. -/
private def tryExactLocalFactProof? (goal : Expr) : MetaM (Option Expr) := do
  let lctx ← getLCtx
  for decl in lctx do
    if decl.isImplementationDetail then
      continue
    let proof := mkFVar decl.fvarId
    let proofType ← inferType proof
    if !(← isProp proofType) then
      continue
    if ← isDefEqRestoring proofType goal then
      return some proof
  return none

/-- Instantiate local universal facts only far enough to see whether one becomes
    exactly the current guard goal. This avoids injecting instantiated facts
    into the whole prover context while still making `h a : f a ≠ 0` visible
    for `h : ∀ a, f a ≠ 0`. -/
private def tryForallInstantiatedProof? (goal : Expr) : MetaM (Option Expr) := do
  let candidates := collectCandidateTermsCapped goal
  let lctx ← getLCtx
  let mut remaining := maxForallInstantiatedFacts
  for decl in lctx do
    if remaining == 0 then
      break
    if decl.isImplementationDetail then
      continue
    let proof := mkFVar decl.fvarId
    let proofType ← inferType proof
    if !proofType.isForall then
      continue
    if !(← forallCodomainIsProp proofType 4) then
      continue
    let facts ← instantiateForallWithCandidates proof proofType candidates 4 remaining
    for fact in facts do
      let factType ← inferType fact
      if ← isDefEqRestoring factType goal then
        return some fact
    remaining := remaining - facts.size
  return none


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

/-- True when an expression is definitionally the literal `1`. -/
private def isOneOf (e : Expr) : MetaM Bool := do
  try
    let one ← Lean.Meta.mkNumeral (← inferType e) 1
    isDefEqNoThrow e one
  catch _ =>
    return false

/-- Return the final explicit argument of an application, if any. -/
private def lastAppArg? (e : Expr) : Option Expr :=
  e.getAppArgs.back?

/-- True for the standard Real/Complex scalar domains where abs/norm lower
    bounds prove nonzeroness. This deliberately does not trust arbitrary
    user-defined `Norm` or `abs` instances. -/
private def isStandardAbsNormDomain (ty : Expr) : MetaM Bool := do
  let ty ← whnf ty
  return ty.isConstOf ``Real || ty.isConstOf ``Complex

/-- Standard ordered scalar domains where bare positivity implies nonzeroness.
    This intentionally excludes arbitrary ordered typeclass instances. -/
private def isStandardOrderedDomain (ty : Expr) : MetaM Bool := do
  let ty ← whnf ty
  return ty.isConstOf ``Real || ty.isConstOf ``Rat

/-- True if `measure` is a known standard magnitude of `d`, such as `|d|`,
    `‖d‖`, or `Complex.normSq d`. -/
private def isStandardMagnitudeOf (measure d : Expr) : MetaM Bool := do
  if !(← isStandardAbsNormDomain (← inferType d)) then
    return false

  let measure ← instantiateMVars measure
  let fn := measure.getAppFn
  let argMatches ←
    match lastAppArg? measure with
    | some arg => isDefEqNoThrow arg d
    | none => pure false

  if argMatches && (fn.isConstOf ``abs || fn.isConstOf ``Norm.norm) then
    return true

  -- `Complex.normSq d` elaborates through `DFunLike.coe Complex.normSq d`.
  if argMatches && measure.getAppArgs.any (fun arg => arg.isConstOf ``Complex.normSq) then
    return true

  return false

/-- Recognize hypotheses that imply `d ≠ 0` via a positive standard magnitude:
    `0 < |d|`, `1 ≤ |d|`, `0 < ‖d‖`, `1 ≤ ‖d‖`, and symmetric `>`/`≥` forms. -/
private def isStandardMagnitudeLowerBoundHyp (hypType d : Expr) : MetaM Bool := do
  if hypType.isAppOfArity ``LT.lt 4 then
    let args := hypType.getAppArgs
    let lhs := args[2]!
    let rhs := args[3]!
    if !isSyntacticZero lhs then
      return false
    isStandardMagnitudeOf rhs d
  else if hypType.isAppOfArity ``GT.gt 4 then
    let args := hypType.getAppArgs
    let lhs := args[2]!
    let rhs := args[3]!
    if !isSyntacticZero rhs then
      return false
    isStandardMagnitudeOf lhs d
  else if hypType.isAppOfArity ``LE.le 4 then
    let args := hypType.getAppArgs
    let lhs := args[2]!
    let rhs := args[3]!
    return (← isOneOf lhs) && (← isStandardMagnitudeOf rhs d)
  else if hypType.isAppOfArity ``GE.ge 4 then
    let args := hypType.getAppArgs
    let lhs := args[2]!
    let rhs := args[3]!
    return (← isStandardMagnitudeOf lhs d) && (← isOneOf rhs)
  else
    return false

/-- Recognize standard-domain hypotheses such as `0 < d`, `d > 0`, `1 ≤ d`,
    and `d ≥ 1` as nonzero evidence. The caller is responsible for checking
    that `d` lives in a supported ordered domain. -/
private def isStandardPositiveBoundHyp (hypType d : Expr) : MetaM Bool := do
  if hypType.isAppOfArity ``LT.lt 4 then
    let args := hypType.getAppArgs
    let lhs := args[2]!
    let rhs := args[3]!
    return isSyntacticZero lhs && (← isDefEqNoThrow rhs d)
  else if hypType.isAppOfArity ``GT.gt 4 then
    let args := hypType.getAppArgs
    let lhs := args[2]!
    let rhs := args[3]!
    return (← isDefEqNoThrow lhs d) && isSyntacticZero rhs
  else if hypType.isAppOfArity ``LE.le 4 then
    let args := hypType.getAppArgs
    let lhs := args[2]!
    let rhs := args[3]!
    return (← isOneOf lhs) && (← isDefEqNoThrow rhs d)
  else if hypType.isAppOfArity ``GE.ge 4 then
    let args := hypType.getAppArgs
    let lhs := args[2]!
    let rhs := args[3]!
    return (← isDefEqNoThrow lhs d) && (← isOneOf rhs)
  else
    return false

/-- Search local hypotheses for standard-domain positive bounds implying `d ≠ 0`. -/
private def findStandardPositiveBoundHyp (d : Expr) : MetaM Bool := do
  if !(← isStandardOrderedDomain (← inferType d)) then
    return false

  let lctx ← getLCtx
  for decl in lctx do
    if decl.isImplementationDetail then
      continue
    let hypType ← inferType (mkFVar decl.fvarId)
    if ← isStandardPositiveBoundHyp hypType d then
      return true
  return false

/-- Standard magnitude lower-bound facts, recursively through conjunctions. -/
private partial def isStandardMagnitudeLowerBoundFactType (hypType d : Expr) : MetaM Bool := do
  if ← isStandardMagnitudeLowerBoundHyp hypType d then
    return true
  let hypType ← whnf hypType
  if hypType.isAppOfArity ``And 2 then
    let args := hypType.getAppArgs
    return (← isStandardMagnitudeLowerBoundFactType args[0]! d) ||
      (← isStandardMagnitudeLowerBoundFactType args[1]! d)
  return false

/-- Search local hypotheses for standard magnitude lower bounds implying `d ≠ 0`. -/
private def findStandardMagnitudeLowerBoundHyp (d : Expr) : MetaM Bool := do
  if !(← isStandardAbsNormDomain (← inferType d)) then
    return false

  let candidates := collectCandidateTermsCapped d
  let lctx ← getLCtx
  for decl in lctx do
    if decl.isImplementationDetail then
      continue
    let proof := mkFVar decl.fvarId
    let hypType ← inferType proof
    if ← isStandardMagnitudeLowerBoundFactType hypType d then
      return true
    if hypType.isForall && (← forallCodomainIsProp hypType 4) then
      let facts ← instantiateForallWithCandidates proof hypType candidates 4 maxForallInstantiatedFacts
      for fact in facts do
        if ← isStandardMagnitudeLowerBoundFactType (← inferType fact) d then
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

end SemanticGuards
end AtpLinter
