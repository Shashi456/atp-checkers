/-
  Guard fact discovery.

  This module owns the local facts that the guard prover is allowed to use:
  propositional locals, derived structure-field facts, conjunction expansion,
  bounded forall instantiation, and standard Real/Complex magnitude facts.
-/

import Lean
import Lean.Meta.AppBuilder
import AtpLinter.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Complex.Norm

open Lean Meta

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

/-- Collect all *propositional* local hypotheses as expressions (fvars). -/
def getLocalPropHyps : MetaM (List Expr) := do
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

/-- Expose the standard guard facts in the established order. -/
def withGuardFacts (k : MetaM α) : MetaM α :=
  withDerivedLocalFacts <| withExpandedAndHyps k

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
private partial def collectCandidateTerms (e : Expr) : Array Expr :=
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
private partial def forallCodomainIsProp (type : Expr) (fuel : Nat) : MetaM Bool := do
  if fuel == 0 then
    return false
  if type.isForall then
    forallCodomainIsProp type.bindingBody! (fuel - 1)
  else
    isProp type

/-- Instantiate a local `∀` proof with bounded candidate combinations. -/
private partial def instantiateForallWithCandidatesAux (proof proofType : Expr) (candidates : Array Expr)
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
private partial def instantiateForallWithCandidates (proof proofType : Expr) (candidates : Array Expr)
    (fuel : Nat) (remaining : Nat) : MetaM (Array Expr) := do
  let (facts, _) ← instantiateForallWithCandidatesAux proof proofType candidates fuel remaining
    maxForallDefEqAttempts
  return facts

/-- Find a local propositional fact whose type is definitionally equal to the
    goal. Unlike `assumptionCore`, this also sees let-bound derived facts. -/
def tryExactLocalFactProof? (goal : Expr) : MetaM (Option Expr) := do
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
def tryForallInstantiatedProof? (goal : Expr) : MetaM (Option Expr) := do
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
      -- Fallback to Zero.zero for types with Zero but not OfNat.
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
def findStandardPositiveBoundHyp (d : Expr) : MetaM Bool := do
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
def findStandardMagnitudeLowerBoundHyp (d : Expr) : MetaM Bool := do
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

end SemanticGuards
end AtpLinter
