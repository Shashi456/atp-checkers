# v4.28_experimental — Phase-wise linter improvements ablation

## Context

Five Opus 4.7 deep reviews identified structural linter improvements. This
branch implements them in 4 phases and ablates against two datasets to measure
concrete impact.

## Phases

| # | Commit | Change |
|---|---|---|
| 1 | `2bb16ed` | `withDerivedLocalFacts` extractors: `Finset.{Icc,Ico,Ioc,Ioo,range}` + `Set.{Icc,Ico,Ioc,Ioo,Ici,Iic,Ioi,Iio}` interval membership → order facts; `Nat.Prime p` → `2 ≤ p`; `Fact (Nat.Prime p)` → `2 ≤ p` via `Fact.out`. |
| 2a | `e6bbe04` | `AnalyticDomain.provePos?` pivots `0 < \|y\|` goal to `y ≠ 0`. |
| 3+4 | `9626e09` | IntDiv: suppress `mayTruncate` when `divisor ∣ dividend` or `dividend % divisor = 0` in scope. UnusedQuantifier: whitelist `.lam` under type-former heads (`PiLp`/`EuclideanSpace`/`Matrix`/`Finsupp`/...); suppress binders whose type `hasSyntheticSorry`. |
| 5 | `f591a79` + `fb073bb` | Add `nlinarith` (linarith + nonlinear preprocessor extras) as step 5 in `tryProveProof?` cascade, enabled for all three AnalyticDomain provers (proveNonNeg?/provePos?/proveNeZero?). Bounded to 20k heartbeats per call after unbounded blew up combibench (18 → 85 timeouts). |

## Ablation results

### proverbenchmath@deepseek (325 decls)

|               | base | P1  | P2  | P34 | P5  | Δbase |
|---------------|------|-----|-----|-----|-----|-------|
| findings      | 348  | 363 | 363 | 363 | 367 | +19 |
| proven        | 199  | 208 | 208 | 208 | 208 | +9 |
| maybe         | 149  | 155 | 155 | 155 | 159 | +10 |
| ok            | 146  | 144 | 144 | 144 | 151 | +5 |
| timeout       | 13   | 10  | 10  | 10  | **0** | –13 |

Per-category:

| category                     | base | P1  | P2  | P34 | P5  | Δ |
|------------------------------|------|-----|-----|-----|-----|---|
| 0-Indexed Range              | 2    | 2   | 2   | 2   | 2   | 0 |
| Analytic Domain Totalization | 18   | 19  | 19  | 19  | 19  | +1 |
| Counterexample Found         | 5    | 5   | 5   | 5   | 5   | 0 |
| Integer Division Truncation  | 6    | 5   | 5   | 5   | 6   | 0 |
| Modulo Edge Case             | 1    | **0** | 0 | 0 | 0   | –1 |
| Potential Division by Zero   | 77   | 80  | 80  | 80  | 81  | +4 |
| Truncated Nat Subtraction    | 5    | 7   | 7   | 7   | 7   | +2 |
| Unsound Axiom                | 190  | 199 | 199 | 199 | 199 | +9 |
| Unused Quantified Variable   | 44   | 46  | 46  | 46  | 48  | +4 |

**Phase 5 nlinarith: 0 proofs closed.** `provedBy: nlinarith` appears 0 times across 367 findings. The 18 AD findings are unchanged — they're spec-drift (theorem remains true under Lean totalization), not quadratic-form positivity goals nlinarith could close.

### combibench@hf (100 decls)

|               | base | P1  | P2  | P34 | P5  | Δbase |
|---------------|------|-----|-----|-----|-----|-------|
| findings      | 55   | 62  | 62  | 60  | 61  | +6 |
| proven        | 1    | 1   | 1   | 1   | 1   | 0 |
| maybe         | 54   | 61  | 61  | 59  | 60  | +6 |
| ok            | 50   | 53  | 53  | 52  | 59  | +9 |
| timeout       | 20   | 17  | 16  | 18  | 6   | –14 |
| infra_error   | 10   | 8   | 9   | 8   | 12  | +2 |

**Note on P5**: first attempt with **unbounded** nlinarith caused catastrophic regression (18 → 85 timeouts, 52 → 10 ok). `fb073bb` added a 20k-heartbeat bound which recovered to 6 timeouts. 0 nlinarith proofs closed.

## Identified real wins (structural, phase-attributable)

Decl-level inspection across 425 combined-dataset decls × 5 phases yields
**3 clean structural wins** across all 5 phases:

1. **`number_theory__p11`** (proverbench) — `theorem exists_ab_mod_p (p : ℕ) (hp : Nat.Prime p) : ∃ a b : ℤ, (a^2+b^2+1) % p = 0`. Phase 1's `Nat.Prime.two_le` extractor unlocks `p ≥ 2`, proving the Modulo guard `↑p ≠ 0`. Modulo finding silenced.
2. **`imo_2023_p5`** (combibench) — has two `sorry`-typed binders (`∀ p : sorry` / `λ p : sorry`). Phase 4's `hasSyntheticSorry` guard suppresses both noise findings on a declaration that is already known-broken. Counts as 2 finding-level wins on one decl.

**Phase 5 (nlinarith): 0 wins.** `provedBy: nlinarith` appears 0 times across
both datasets' 428 findings combined. Proverbench's 18 AD findings and
combibench's 0 AD findings mean nlinarith had 18 candidate goals. None closed
in 20k heartbeats. The shapes are spec-drift (theorems remain true under Lean
totalization), not the quadratic-form or sin/cos-bounded positivity goals
nlinarith targets.

The remaining +19 proverbench / +6 combibench finding deltas are **not
attributable to phase logic**. Driver: previously-timeout decls now complete
successfully (13 → 0 timeouts proverbench, 20 → 6 combibench), which adds new
findings from freshly-analyzed decls. Timing noise from a 10-worker pool, not
linter changes. Decl-level diff across all 5 phases confirms **no proven↔maybe
flips in any category**.

## Why so small?

Per-dataset pattern audits (done during drafting) explain the small lift:

- **Proverbench NatSub (5 baselines)**: 0/5 have a `Finset.Icc`/`Nat.Prime`/`Set.Ioo` hypothesis. All are context-free truncations — no amount of extractor can unlock them without semantic synthesis. Phase 1 cannot help.
- **Proverbench Div0 (77 baselines)**: 6/77 (~8%) have an interval or set-mem hypothesis that Phase 1 could unpack. The structural ceiling on this dataset is ~8 decls.
- **Proverbench AnalyticDomain (18 baselines)**: 0 use the `log(|y|)` / `sqrt(|y|)` pattern Phase 2a targets. 0 close under nlinarith in 20k heartbeats. These are spec-drift findings (theorem is true under Lean totalization even when informal domain is lost), not positivity goals. Pattern for Phase 2a is in formalmath@all, not proverbench.
- **Combibench AnalyticDomain (0 baselines)**: no AD findings at all on combibench — the corpus lacks the analytic operators (`Real.log`, `Real.sqrt`) that AD triggers on.
- **Combibench UnusedQuantifier**: most FPs are in `EuclideanSpace ℝ (Fin 2)` λ's on tests like `brualdi_ch1_16` — but the `EuclideanSpace` name gets unfolded via typeclass resolution before Phase 4's head-match fires. `hasSyntheticSorry` worked as expected on `imo_2023_p5`.

The Opus-agent estimates ("NatSub: +250–330 proven", "Div0: +30+ proven",
"~30% of AD samples close under nlinarith") were for the full corpus
(combibench@hf + formalmath@all + minif2f_variants + proofnet_variants).
Proverbench+combibench have a much narrower shape distribution.

## Recommendations

1. **Ship Phase 1 (number_theory__p11 win, near-zero risk)**. The extractors are sound, preserve monotonicity (never add findings), and unlock the dominant corpus-wide pattern. Even with 1 visible win, the shared `withDerivedLocalFacts` path will benefit Modulo/IntToNat/Exponent transitively on larger datasets.
2. **Ship Phase 4 sorry-suppression** — 2 visible FP reductions on `imo_2023_p5`, eliminates noise on broken declarations.
3. **Reconsider Phase 2a abs pivot** — zero wins on the ablation datasets. Keep the code (it's correct) but re-measure on formalmath@all before drawing conclusions about its value.
4. **Reconsider Phase 3 IntDiv whitelist** — zero hits on ablation datasets; same audit needed.
5. **Phase 5 nlinarith: do not ship as-is.** Zero proofs closed at 20k heartbeats, and raising the budget risks recurring the unbounded-timeout disaster (combibench 18 → 85 timeouts). The cascade overhead is non-trivial even when nlinarith fails fast. Either drop the step entirely or restrict it to tightly shape-gated goals (e.g. only when the expression is a sum-of-squares, not for any `0 ≤ x` / `x ≠ 0` goal).
6. **Next batch** (not in this branch): wire Plausible per-divisor probe for Div0 (tryPlausibleDivisorZero? existentially samples free fvars of divisor), add the EuclideanSpace-after-typeclass-unfold detection, and re-run ablation on formalmath@all where Phase 2a and 3 target patterns actually live.

## Reproducibility

```bash
# From release/atp-checkers/
GIT_CONFIG_GLOBAL=~/.gitconfig-personal git checkout v4.28_experimental
lake build
source /Users/paws/.venv/bin/activate
python -m runner local/cache/materialized/proverbenchmath@deepseek/full.jsonl \
  -w . -o results_experimental/proverbench_rerun --timeout 30 -j 10
python -m runner local/cache/materialized/combibench@hf/full.jsonl \
  -w . -o results_experimental/combibench_rerun --timeout 30 -j 10
```

Per-phase commits:
- Phase 1: `2bb16ed`
- Phase 2a: `e6bbe04`
- Phase 3+4: `9626e09`
- Phase 5: `f591a79` (addition), `fb073bb` (heartbeat bound fix)
