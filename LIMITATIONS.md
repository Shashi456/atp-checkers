# Limitations

Static analysis of Lean formalization code is fundamentally constrained.
This document explains what this tool can and cannot do, and why.

## Why a linter can't catch everything

### 1. Undecidability of semantic correctness

Determining whether a Lean formalization correctly captures a natural-language
math statement is undecidable in general. The linter detects *syntactic patterns*
that commonly indicate semantic errors (division by zero, natural subtraction
underflow, vacuous hypotheses, etc.), but it cannot verify whether the
formalization *means the right thing*.

A theorem statement can be syntactically clean, type-correct, and pass all
checkers — yet still formalize the wrong problem entirely. Only human review
or LLM-assisted semantic comparison against the natural-language source can
catch these issues.

### 2. Guard analysis is local

The semantic guard prover (`assumption` → `omega` → `grind`) operates on the
local context at each binder position. It cannot:

- Follow guards through helper definitions or lemmas
- Reason about guards established by type class instances
- Track guards across module boundaries
- Resolve guards hidden behind `have`/`let` bindings in proof terms

If a divisor `b` is guaranteed non-zero by a hypothesis buried three definitions
deep, the linter will still flag `a / b` as unguarded.

### 3. Prover timeout and incompleteness

The `omega` tactic handles linear arithmetic over `Nat`/`Int` completely, but
`grind` (the SMT-style fallback) is incomplete by nature. Some provable guard
conditions will time out or fail, producing `"maybe"` confidence instead of
`"proven"`.

The prover stack is intentionally capped with tight resource limits to keep
per-problem latency reasonable (~1-3 seconds). Loosening these caps would catch
more cases but make batch runs impractical.

### 4. Pattern coverage is finite

The linter checks 13 specific error categories. Real formalization errors extend
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

### 6. Proof terms are not analyzed

The linter only inspects type signatures (theorem statements), not proof terms.
This is intentional — proof terms are enormous, auto-generated, and contain
incidental arithmetic operations that would produce thousands of false positives.

However, this means the linter cannot detect issues *within* proofs, such as
a proof that uses `sorry` deep in a tactic block (the `axiom` checker catches
top-level `sorry` declarations but not nested ones in all cases).

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
- **Division by zero** — often introduced when LLMs translate "for all x"
  without excluding zero
- **Vacuous hypotheses** — contradictory assumptions that make any theorem
  trivially true
- **Literal truncation** — `1/4 = 0` in integer arithmetic, invisible in
  source code

These categories account for the majority of semantic errors in practice.
The `"proven"` confidence level provides high-signal findings that rarely
require manual verification.

## Recommended workflow

For best results, use the linter as the first stage in a multi-stage pipeline:

1. **Linter pass** — fast, automated, catches mechanical errors
2. **LLM review** — compare formalization against natural-language statement
   for semantic correctness (see README for details)
3. **Human review** — final verification for critical applications
