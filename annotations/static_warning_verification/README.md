# static_warning_verification

`static_warning_verification` is a release bundle for evaluating whether LLMs can correctly classify static-analyzer warnings on Lean 4 formalizations as true positives or false positives. This is a 55-example binary classification benchmark for a different task: given a theorem and a specific static-checker warning, judge whether the warning is valid.

This is **not** the semantic-category benchmark (see `annotations/semantic_lean_errors/`).


## Directory Overview

This directory is meant to be self-contained for release.
It includes:

- `static_warning_verification_55.jsonl`
  - Canonical machine-facing dataset.
  - One record per line.
  - Recommended file for downstream use.
- `static_warning_verification_55.json`
  - Readable companion file.
  - Stores the same records as the JSONL, but as a pretty-printed JSON array.
- `schema.md`
  - Schema for the exported records.
- `prompt_template.md`
  - Generic and checker-specific prompt templates used for the evaluation.
  - Includes evaluation settings (temperature, max tokens, etc.).
- `README.md`
  - Dataset card and release notes.

## Task Description

A static analyzer for Lean 4 formalizations detects potential semantic issues (division by zero, truncated natural subtraction, analytic domain violations, modulo edge cases). The analyzer uses fast local tactics (`omega`, `assumption`) that are sound but incomplete: they may produce warnings for code that is actually safe, because they cannot perform multi-step implication reasoning.

The task is:

> Given a Lean 4 theorem/definition and a static-checker warning, determine whether the warning is a **true positive** (genuine issue) or a **false positive** (the guard is provable from context).

This is a binary classification task. Each example consists of:
- Lean 4 code that triggered the warning
- The warning message and its category
- A human-verified ground-truth verdict with justification

## Why False Positives Occur

The static checker uses fast, local proof tactics (`omega`, `assumption`, `grind`) that are sound but incomplete:

| Checker | What it checks | What it misses | Why |
|---------|----------------|----------------|-----|
| **Division / Analytic** | Is `0 < x` directly in hypotheses? | `1 < x` implies `0 < x` | No implication chaining (would need `linarith`, too slow) |
| **Nat Subtraction** | Can `omega` prove `a <= b`? | `n^a <= n^b` when `a <= b, n >= 1` | `omega` only handles **linear** arithmetic |
| **Modulo** | Can `omega` prove `p != 0`? | `Prime p` implies `p >= 2` | `omega` has no **domain knowledge** |

The checker deliberately chose fast lookup over slow reasoning because full reasoning (`linarith`, `polyrith`) can take 10-60 seconds per check and may not terminate on complex goals. For thousands of problems with multiple findings each, this would be prohibitive.

The LLM verification approach sends each finding to a language model with the theorem code, and the LLM does the implication reasoning that the fast checker skipped.

## Which Checkers Need LLM Verification

The static checker produces 13 categories of warnings. We selected four for LLM verification based on two criteria: they produce the most findings across benchmarks, and their proof tactics are structurally unable to resolve many valid guards.

### Selected Categories (high false-positive risk)

These four categories account for the majority of findings and have structural FP sources that fast tactics cannot address:

| Checker | Typical finding volume | FP source |
|---------|----------------------|-----------|
| **Potential Division by Zero** | Highest | Implication chains (`1 < x` -> `0 < x`) that require `linarith`, not available to the checker |
| **Analytic Domain Totalization** | High | Implication chains and `Nat.cast` positivity; same reasoning gap as division |
| **Truncated Nat Subtraction** | Moderate | Non-linear arithmetic (`n^a <= n^b`); `omega` is limited to linear reasoning |
| **Modulo Edge Case** | Moderate | Mathematical domain knowledge (`Prime p` -> `p >= 2`); `omega` has no theory of primality |

### Excluded Categories (no LLM verification needed)

The remaining checkers do not benefit from LLM verification because their findings are either mechanically proven or structurally reliable:

| Checker | Why excluded |
|---------|-------------|
| **Unsound Axiom** | Findings come with a constructive proof that the axiom introduces unsoundness. No judgment needed. |
| **Counterexample** | Findings come with a concrete witness verified by `decide` or enumeration. Mechanically certain. |
| **Integer Division Truncation** | Detected by definitional evaluation (e.g., `1 / 2 = 0` in `Nat`). Always provable, no ambiguity. |
| **Unused Variable** | Structural check on binder usage. Always provable. |
| **0-Indexed Range** | Flags a suspicious pattern (`List.range` starting at 0 vs 1) rather than proving a semantic violation. This is a finding-level signal, not a certainty-level instrument, so LLM verification would not meaningfully change its status. |

## Dataset Composition

Total: **55** labeled examples

### By Verdict

| Verdict | Count |
|---------|------:|
| `false_positive` | 34 |
| `true_positive` | 21 |

### By Category

| Category | FP | TP | Total |
|----------|---:|---:|------:|
| `modulo_edge_case` | 4 | 0 | 4 |
| `truncated_nat_subtraction` | 12 | 4 | 16 |
| `analytic_domain_totalization` | 9 | 7 | 16 |
| `potential_division_by_zero` | 9 | 10 | 19 |
| **Total** | **34** | **21** | **55** |

## Record Schema

Each row is a single warning with a human verdict.
The exported per-record fields are:

- `id`
- `category`
- `source`
- `verdict`
- `justification`
- `lean_code`
- `warning_message`

Field meanings are documented in `schema.md`.

## Prompt Overview

The included prompt file `prompt_template.md` defines checker-specific prompts.
For each example, the model receives a prompt tailored to the warning's category, containing:

- Lean 4 / Mathlib domain knowledge relevant to the category
- The theorem code
- The warning message
- Clear decision criteria mapping guard provability to verdict

All prompts expect the same structured output:

```
VERDICT: [TRUE_POSITIVE|FALSE_POSITIVE]
REASON: [one-line explanation]
```

## Experimental Reproducibility

This release includes the exact benchmark and prompt templates used for the paper's LLM warning-verification experiments.

Evaluation setup:

- benchmark: `55` labeled examples
- categories: `4` (one prompt template per category)
- temperature: `0.0`
- max tokens: `512`
- prompt file: `prompt_template.md`

### Paper-Reported Results (Table 4)

| Model | Accuracy | Precision | Recall | Cost |
|-------|--------:|---------:|------:|-----:|
| Gemini 3.0 Flash | 83.3% | 0.89 | 0.86 | $0.09 |
| GPT-5.2 | 81.8% | 0.92 | 0.83 | $0.18 |
| Claude Sonnet 4.5 | 81.5% | 0.89 | 0.81 | $0.42 |
| DeepSeek-V3 | 68.5% | 0.68 | 1.00 | $0.12 |

## Known Limitations

1. **Inconsistent verdicts for equivalent expressions**: LLMs may give different verdicts for semantically equivalent expressions across different problems, because they lack deterministic algebraic reasoning.
2. **Missing domain knowledge**: The LLM may not recognize certain Mathlib-specific patterns (e.g., `[Invertible A]` implying `det A != 0`). Checker-specific prompts mitigate this but cannot cover all patterns.
3. **No formal verification**: LLM verdicts are not formally verified. For critical applications, LLM-filtered results should be treated as preliminary.
4. **Prompt sensitivity**: Accuracy depends on prompt engineering. Changes to model versions or prompt wording may require re-evaluation.
