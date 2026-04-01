# semantic_lean_errors Schema

This file documents the schema of the exported `semantic_lean_errors.jsonl` and `semantic_lean_errors.json` files.
Both files contain the same records.

- `semantic_lean_errors.jsonl` stores one record per line.
- `semantic_lean_errors.json` stores the same records as a pretty-printed JSON array.

## Record Format

Each record is one labeled NL/Lean pair.

Fields:

- `id` (string)
  - Stable example identifier.
- `source` (string)
  - Source benchmark: one of `FormalMath`, `ProofNet`, `ProverBench`, `CombiBench`.
- `problem_nl` (string)
  - Natural-language problem statement.
- `lean_code` (string)
  - Canonical Lean statement being judged.
- `expected_verdict` (string)
  - Row-level binary label.
  - `YES` means the row contains a semantic error.
  - `NO` means the row is a clean example.
- `error_primary` (string or null)
  - Primary semantic error category.
  - Null for clean examples.
- `error_secondary` (array[string])
  - Optional secondary semantic categories.
- `error_tags` (array[string])
  - Detail tags refining the error type.
- `meta_tags` (array[string])
  - Optional non-prompt metadata tags.
- `gold_explanation` (string)
  - Human-written explanation of the label.

## Primary Categories

The dataset uses six primary semantic-error categories:

- `problem_statement_error`
- `specification_error`
- `formalization_error`
- `domain_mismatch`
- `definition_mismatch`
- `quantifier_indexing_mismatch`

See `error_tags.md` for category definitions, boundaries, and detail-tag guidance.

## Label Semantics

Two label views are represented in the export:

1. Binary row-level view
- Use `expected_verdict`.
- `YES` = some semantic error is present.
- `NO` = clean example.

2. Category-specific view
- Use `error_primary`.
- In the current 6-category evaluation, a category prompt expects `YES` iff `error_primary` equals the queried category; otherwise `NO`.

## Normalization Policy

This exported release is intentionally normalized:

- `lean_code` is the single canonical code field.
- ProofNet examples are normalized from `original_lean_code` to `lean_code`.
- `fixed_lean_code` and `lean_code_fixed` are not included in this release bundle.
- `error_secondary`, `error_tags`, and `meta_tags` are always lists.

## Example

```json
{
  "id": "example_id",
  "source": "FormalMath",
  "problem_nl": "...",
  "lean_code": "theorem ... := by",
  "expected_verdict": "YES",
  "error_primary": "definition_mismatch",
  "error_secondary": [],
  "error_tags": ["wrong_operator"],
  "meta_tags": [],
  "gold_explanation": "The Lean operator does not match the intended informal notion."
}
```
