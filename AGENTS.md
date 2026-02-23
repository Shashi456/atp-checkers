# AGENTS

## Purpose

This repository provides a Lean semantic-trap linter and a dataset runner.
Package name is `atp-checkers`. Lean code namespace is `AtpLinter`.

## Non-Goals

Prompt sets and prompt pipelines live outside this repository.

## First Commands

```bash
lake build
lake build AtpLinterTest
python -m runner --help
```

## Running the Linter on a Dataset

```bash
python -m runner <dataset.jsonl> --workspace . --output out --workers 4
```

## Dataset Interface

Required JSONL fields:
- `id`
- `lean_code`

Optional fields are preserved under `metadata`.

## File Ownership

- Lean core logic: `src/`
- Lean tests: `test/`
- Batch execution pipeline: `runner/`
- Dataset docs/examples: `datasets/`

## Change Policy

When editing behavior:
1. Update checker code
2. Add/adjust tests in `test/`
3. Validate runner output shape if JSON changes
4. Update `README.md` and `datasets/FORMATS.md` if user-facing contracts changed

## Current Testing Reality

Many tests are scenario/diagnostic (`#check_atp`) rather than strict assertions.
Prefer adding assertion helpers in regression files when changing behavior.

## Confidence Contract

Findings expose:
- `confidence`: `proven` | `maybe`
- `provedBy`: solver/evidence string or null

Keep this stable unless versioning the output schema.
