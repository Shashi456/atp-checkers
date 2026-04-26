/-
  Guard local-context policy.

  This module owns binder-safe local-context construction. It intentionally does
  not import checker modules, so `AtpLinter.Basic` can re-export this public
  helper without creating an import cycle.
-/

import Lean

open Lean Meta

namespace AtpLinter

/-- Build a local context for analyzing binder j's type using "prop-full,
    data-prefix" semantics:
    - Keep all earlier binders (0..j-1)
    - Drop the current binder j
    - Drop all later NON-propositional binders (data evidence like Fin, Subtype
      values whose derived facts could circularly justify the type)
    - Keep later propositional binders UNLESS they depend on a dropped binder
      (prevents circular props like `h : x.1 < n - k` where x was dropped)

    This prevents:
    - Self-justification: `i : Fin (n - k)` using its own Fin.isLt
    - Same-type siblings: `(x y : Fin (n - k))` — y is data, dropped
    - Mixed-type witnesses: `(x : Fin (n-k)) (y : {m // m < n-k})` — y is data
    - Dependent circular props: `(x : Fin (n-k)) (h : x.1 < n-k)` — h depends on x

    While preserving:
    - Legitimate later guards: `(x : Fin (a/b)) (hb : b ≠ 0)` — hb is prop,
      independent of x -/
def mkSafeLCtxForType (fullLCtx : LocalContext) (fvars : Array Expr) (j : Nat) :
    MetaM LocalContext := do
  let mut lctx := fullLCtx
  -- Track which fvars are dropped so we can check dependency.
  let mut dropped : Array FVarId := #[fvars[j]!.fvarId!]
  -- Always drop the current binder.
  lctx := lctx.erase fvars[j]!.fvarId!
  -- Process later binders.
  for k in [j + 1 : fvars.size] do
    let fvar := fvars[k]!
    let fid := fvar.fvarId!
    let ty ← Meta.inferType fvar
    if ← Meta.isProp ty then
      -- Propositional binder: keep unless it depends on a dropped binder.
      let dependsOnDropped := dropped.any fun did => ty.containsFVar did
      if dependsOnDropped then
        lctx := lctx.erase fid
        dropped := dropped.push fid
    else
      -- Data binder: always drop, since it could produce circular derived facts.
      lctx := lctx.erase fid
      dropped := dropped.push fid
  return lctx

end AtpLinter
