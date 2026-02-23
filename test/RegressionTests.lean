/-
  Regression tests for specific bug fixes from the Consolidated Remediation Plan.
-/

import AtpLinter

-- ═══════════════════════════════════════════════════════════════════
-- Fix 3: `a - 0` should NOT be flagged as unguarded subtraction
-- ═══════════════════════════════════════════════════════════════════

/-- `a - 0` is always safe (= a) — should NOT be flagged -/
theorem sub_zero_safe (a : Nat) : a - 0 = a := by omega

#check_atp sub_zero_safe

-- ═══════════════════════════════════════════════════════════════════
-- Fix 4: `Nat.div a 0` should be ERROR not just WARNING
-- ═══════════════════════════════════════════════════════════════════

/-- Division by literal zero should be flagged as ERROR -/
def div_by_zero_nat (a : Nat) : Nat := a / 0

#check_atp div_by_zero_nat

-- ═══════════════════════════════════════════════════════════════════
-- Fix 5: Guard-proving false positives — these should NOT be flagged
-- ═══════════════════════════════════════════════════════════════════

/-- Subtraction guarded by omega-provable hypothesis -/
theorem subGuardedOmega (a b : Nat) (h : a ≥ b) : a - b + b = a := by
  omega

#check_atp subGuardedOmega

/-- Int.toNat guarded by hypothesis h : x ≥ 2, should prove 0 ≤ x -/
theorem toNatGuardedFromGeTwo (x : Int) (h : x ≥ 2) : x.toNat ≥ 0 := by
  omega

#check_atp toNatGuardedFromGeTwo

/-- Chained inequalities: a ≥ c, c ≥ b ⟹ a ≥ b (omega should handle) -/
theorem chainedIneq (a b c : Nat) (h1 : a ≥ c) (h2 : c ≥ b) : a - b ≤ a := by
  omega

#check_atp chainedIneq

-- ═══════════════════════════════════════════════════════════════════
-- Fix 6: `Classical.fake` axiom should be flagged
-- ═══════════════════════════════════════════════════════════════════

axiom Classical.fake : 1 = 2

#check_atp Classical.fake

-- ═══════════════════════════════════════════════════════════════════
-- Nat.pred pattern (documents current gap)
-- ═══════════════════════════════════════════════════════════════════

/-- Nat.pred without guard. Current linter does NOT check Nat.pred. -/
def natPredUnguarded (n : Nat) : Nat := Nat.pred n

#check_atp natPredUnguarded

-- ═══════════════════════════════════════════════════════════════════
-- Fix 7: Dedup merges semantically identical detections from
--        different syntactic forms (HDiv.hDiv vs Nat.div, etc.)
-- ═══════════════════════════════════════════════════════════════════

/-- Helper: assert that #check_atp produces exactly `expected` findings for `name` -/
syntax (name := assertFindingCount) "#assert_finding_count " ident num : command

open Lean Elab Command Meta in
@[command_elab assertFindingCount]
def elabAssertFindingCount : CommandElab := fun stx => do
  let id := stx[1]
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some expected := stx[2].isNatLit?
    | throwError "Expected a number literal"
  let findings ← liftTermElabM do
    let analysis ← AtpLinter.analyzeDecl name
    AtpLinter.toFindings analysis
  if findings.size != expected then
    throwError "Expected {expected} finding(s) for {name}, got {findings.size}"

/-- Nat division `a / b` fires both HDiv.hDiv and Nat.div on the same expression.
    Dedup should merge them into exactly ONE division finding (not two).
    IntDivTruncation adds a second finding from a separate checker → 2 total.
    With hypothesis `h : b = 0`, unsafety proof upgrades division to `proven`. -/
def dedupBugDiv (a b : Nat) (h : b = 0) : Nat := a / b

#check_atp dedupBugDiv
#assert_finding_count dedupBugDiv 2

/-- Nat modulo `a % b` fires both HMod.hMod and Nat.mod on the same expression.
    Dedup should merge them into exactly ONE modulo finding (not two). -/
def dedupBugMod (a b : Nat) (h : b = 0) : Nat := a % b

#check_atp dedupBugMod
#assert_finding_count dedupBugMod 1

/-- Division with no unsafety evidence — 1 division + 1 truncation = 2 findings. -/
def dedupBugDivMaybe (a b : Nat) : Nat := a / b

#check_atp dedupBugDivMaybe
#assert_finding_count dedupBugDivMaybe 2
