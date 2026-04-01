# semantic_lean_errors

`semantic_lean_errors` is a release bundle for semantic error auditing of NL → Lean 4 formalizations.
It packages a 92-problem human-labeled benchmark together with the prompt, schema, and taxonomy used for the paper's 6-category semantic-audit experiments.

## Directory Overview

This directory is meant to be self-contained for release.
It includes:

- `semantic_lean_errors.jsonl`
  - Canonical machine-facing dataset.
  - One record per line.
  - Recommended file for Hugging Face and downstream use.
- `semantic_lean_errors.json`
  - Readable companion file.
  - Stores the same records as `semantic_lean_errors.jsonl`, but as a pretty-printed JSON array.
- `ground_truth_schema.md`
  - Schema for the exported records in this release bundle.
- `error_tags.md`
  - Taxonomy definitions, boundary rules, and detail-tag guidance.
- `eval_prompts_v4_fewshot.md`
  - Few-shot prompt set used for the category-specific semantic-audit evaluation.
- `README.md`
  - Dataset card and release notes.

## Dataset Composition

The benchmark combines four source datasets:

- FormalMath: `22`
- ProofNet: `13`
- ProverBench: `23`
- CombiBench: `34`

Total:

- `92` labeled problems
- `87` error examples
- `5` clean examples

Primary-category counts:

- `problem_statement_error`: `5`
- `specification_error`: `24`
- `formalization_error`: `8`
- `domain_mismatch`: `14`
- `definition_mismatch`: `26`
- `quantifier_indexing_mismatch`: `10`
- clean examples (`error_primary = null`): `5`

Additional label structure:

- rows with non-empty `error_secondary`: `33`
- rows with non-empty `error_tags`: `87`

## Record Schema

Each row is a single NL/Lean pair with human labels.
The exported per-record fields are:

- `id`
- `source`
- `problem_nl`
- `lean_code`
- `expected_verdict`
- `error_primary`
- `error_secondary`
- `error_tags`
- `meta_tags`
- `gold_explanation`

Field meanings are documented in `ground_truth_schema.md`.

Two label views are represented:

1. Binary semantic-error detection
- Use `expected_verdict`.
- `YES` means the row contains some semantic error.
- `NO` means the row is a clean example.

2. Six-category semantic audit
- Use `error_primary`.
- In the current evaluation setup, a queried category expects `YES` iff `error_primary` equals that category, and `NO` otherwise.

## Prompt Overview

The included prompt file `eval_prompts_v4_fewshot.md` defines a 6-category evaluation setup.
For each NL/Lean pair, the model is queried once per category:

- `problem_statement_error`
- `specification_error`
- `formalization_error`
- `domain_mismatch`
- `definition_mismatch`
- `quantifier_indexing_mismatch`

Each prompt asks the model to judge one specific category and return structured JSON with:

- `Verdict`
- `Explanation`
- `DetailTags`
- `NeedsReview`

Because the prompt is category-specific, the 92 labeled problems expand to `552 = 92 × 6` category-level classifications in the paper's evaluation setup.

## Experimental Reproducibility

This release includes the exact benchmark and prompt family used for the paper's semantic-audit experiments.

Evaluation setup:

- benchmark: `92` labeled problems
- categories: `6`
- total category-level judgments: `552`
- prompt file: `eval_prompts_v4_fewshot.md`

The paper reports results for at least these model configurations on this benchmark:

- Sonnet 4.5 + Thinking
- GPT-5.2 + Thinking

### Paper-Reported Aggregate Results

These are the paper-reported numbers for the 92-problem semantic audit and should be treated as the canonical release numbers for this version of the benchmark.

| Model | Prec. | Rec. | F1 | Acc. | Cost |
|-------|------:|-----:|---:|-----:|-----:|
| Sonnet 4.5 + Thinking | 0.30 | 0.82 | 0.42 | 68.1% | $13.71 |
| GPT-5.2 + Thinking | 0.24 | 0.91 | 0.37 | 54.6% | $6.86 |

### Paper-Reported Per-Type F1

| Error Type | Sonnet 4.5 | GPT-5.2 |
|-----------|-----------:|--------:|
| Problem Statement Error | 0.29 | 0.10 |
| Specification Error | 0.51 | 0.48 |
| Formalization Error | 0.18 | 0.15 |
| Domain Mismatch | 0.33 | 0.27 |
| Definition Mismatch | 0.57 | 0.54 |
| Quantifier/Indexing | 0.39 | 0.33 |

Interpretation:

- both models have relatively high recall and lower precision
- both models perform best on `specification_error` and `definition_mismatch`
- both models struggle most on `formalization_error`

Note on reproducibility:

- this directory contains the benchmark, prompt, schema, and taxonomy
- if the exact evaluation pipeline is rerun later, small differences can arise from model/provider/version changes
- the table above reflects the paper-reported results for this release

## Normalization Policy

This release intentionally uses a single canonical code field:

- `lean_code` is the only exported statement field
- ProofNet rows are normalized from `original_lean_code` to `lean_code`
- `fixed_lean_code` and `lean_code_fixed` are omitted from this canonical release
- list-valued annotation fields are normalized to lists

This avoids ambiguous rows that contain two different Lean statements under one set of labels.
If repaired variants are needed for comparison studies, they should live in a separate paired comparison artifact.

## Taxonomy

The category taxonomy and detail-tag definitions are included in `error_tags.md`.
That file defines:

- the six primary semantic-error categories
- boundary rules between overlapping categories
- the allowed detail-tag families
- optional meta-tag conventions

## Release Cleanup Applied

Before export, four internally inconsistent rows were corrected from `expected_verdict = YES` to `expected_verdict = NO` because they were clean examples with `error_primary = null` and explanations indicating no semantic error:

- `formalmath_olymid-ref-base_5274`
- `proofnet_rudin_exercise_2_28`
- `proofnet_rudin_exercise_3_21`
- `proofnet_axler_exercise_6_16`

After this cleanup, the release contains `87` error rows and `5` clean rows.

## Recommended Use

For release and archival use:

- treat `semantic_lean_errors.jsonl` as the canonical dataset file
- keep `README.md`, `ground_truth_schema.md`, `error_tags.md`, and `eval_prompts_v4_fewshot.md` alongside it
- treat `semantic_lean_errors.json` as a readable companion artifact rather than the canonical training/eval file
