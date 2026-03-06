# Limitations

Static analysis of Lean formalization code is fundamentally constrained.
This document explains what this tool can and cannot do, and why.

## Why a linter can't catch everything

### 1. Undecidability and Rice-style limits

Determining whether a Lean formalization correctly captures an informal mathematical statement is not something a linter can decide in general. A theorem can be type-correct, compile cleanly, and still formalize the wrong mathematics entirely.

For program-like definitions, this is closely related to Rice's theorem: any non-trivial semantic property of what a program computes is undecidable in general. For theorem statements, the practical consequence is the same: no finite static checker can decide semantic alignment with the intended informal statement in full generality.

The linter detects *syntactic patterns* that commonly indicate semantic errors (division by zero, natural subtraction underflow, vacuous hypotheses, etc.), but it cannot verify whether the formalization *means the right thing*.


### 2. Guard analysis is declaration-local and checker-specific

The semantic guard prover (`assumption` → `omega` → `grind`) reasons only from the declaration currently being analyzed and the hypotheses that the checker puts in scope.

In practice, this means:
- It can use local hypotheses already present in the declaration.
- All guard-checking checkers open the full binder telescope first (`forallTelescope`/`lambdaTelescope`), so every hypothesis in the declaration signature is simultaneously available regardless of binder order.
- It does not inline helper definitions or lemmas, follow facts across declarations or modules, or recover arbitrary semantic facts established indirectly.

If a divisor `b` is known to be non-zero only through a helper lemma proved elsewhere, the linter may still flag `a / b` as unguarded.


### 3. Prover timeout and incompleteness

The `omega` tactic handles linear arithmetic over `Nat`/`Int` completely, but
is disabled for `Real`/`Complex` types where it does not apply. The `grind`
SMT-style fallback is incomplete by nature. Some provable guard conditions
will time out or fail, producing `"maybe"` confidence instead of `"proven"`.

The prover stack is intentionally capped with tight resource limits to keep
per-problem latency reasonable (~1-3 seconds). Loosening these caps would catch
more cases but make batch runs impractical.

### 4. Pattern coverage is finite

The linter checks 13 semantic error categories (plus an infrastructure error
category for internal linter failures). Real formalization errors extend
far beyond these:

- Incorrect quantifier order (`∀ x, ∃ y` vs `∃ y, ∀ x`)
- Wrong direction of implication
- Off-by-one in combinatorial bounds
- Incorrect definitions of standard objects (e.g., redefining "graph" non-standardly)
- Misuse of Mathlib API (using the wrong version of a lemma)
- Logical tautologies that aren't vacuous (e.g., `P → P`)

The linter catches the *most common* mechanical errors seen in LLM-generated
formalizations. It does not attempt to be exhaustive.

The counterexample checker uses two backends: exhaustive enumeration over small
domains (Bool, Nat 0–4, Int ±2, Fin ≤8, max 4 binders) and a Plausible random
testing fallback for propositions beyond the enumeration boundary. The Plausible
fallback uses a fixed random seed for reproducibility.

### 5. Confidence is not ground truth

The `confidence` field (`"proven"` / `"maybe"`) reflects the linter's own
certainty about whether a flagged pattern is actually dangerous:

- `"proven"` means the prover constructively demonstrated the issue (e.g.,
  proved `divisor = 0` from context). This has very low false-positive rate
  but is not infallible — the proof operates on the *formalized* statement,
  which may itself be wrong.

- `"maybe"` means a suspicious pattern was detected but the prover could not
  confirm the issue. These have a meaningful false-positive rate.

Neither value tells you whether the finding corresponds to a real error in the
*intended* mathematical statement. That requires comparing against ground truth.

### 6. Proof terms are mostly skipped

For `Prop`-valued declarations, the linter analyzes the statement/type and intentionally skips the proof term. For non-`Prop` definitions, it does inspect the value body.

This avoids overwhelming theorem analysis with proof noise, but it also means the linter will usually not catch issues that appear only inside proofs, such as arithmetic artifacts in tactic-generated proof terms or nested uses of `sorry` inside a proof script.

### 7. Lean version coupling

The linter is built against a specific Lean toolchain and Mathlib version
(currently Lean 4 v4.24.0, Mathlib v4.24.0). Code written for different Lean
versions may:

- Use different API names (triggering compile errors, not linter findings)
- Have different default behaviors for the same operations
- Rely on Mathlib lemmas that changed semantics across versions

The runner enforces toolchain consistency and will refuse to mix results from
different versions.

## What the linter is good at

Despite these limitations, the linter reliably catches the most frequent
mechanical errors in LLM-generated Lean formalizations:

- **Natural number subtraction underflow** — the single most common error
  category in autoformalization benchmarks
- **Division/modulo by zero** — often introduced when LLMs translate "for
  all x" without excluding zero
- **Vacuous hypotheses** — contradictory assumptions that make any theorem
  trivially true
- **Literal truncation** — `1/4 = 0` in integer arithmetic, invisible in
  source code
- **Exponent truncation** — `a^(-n)` with Nat result silently totalizes
- **Cast-after-truncation** — `(a / b).toNat` compounds data loss
- **Analytic domain totalization** — `sqrt`, `log`, `inv` without domain
  guards return 0 in Mathlib
- **Unsound axioms** — `sorry`-based or user axioms asserting unproven facts
- **Unused binders** — quantified variables that never appear in the body
- **Counterexample search** — exhaustive enumeration and Plausible random
  testing to find concrete witnesses against false propositions

The first four categories account for the majority of semantic errors in
practice. The `"proven"` confidence level provides high-signal findings
that rarely require manual verification.

## Recommended workflow

For best results, use the linter as the first stage in a multi-stage pipeline:

1. **Linter pass** — fast, automated, catches mechanical errors
2. **LLM review** — compare formalization against natural-language statement
   for semantic correctness (see README for details)
3. **Human review** — final verification for critical applications
