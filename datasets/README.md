# Datasets

This directory documents dataset formats supported by the runner.

## Canonical Internal Contract

Each JSONL row must provide:
- `id`
- `lean_code`

All other keys are preserved as metadata in output records.

## Minimal Example

See `datasets/examples/minimal.jsonl`.

## Validation Behavior

The loader reports parse errors for:
- invalid JSON
- missing `id`
- missing `lean_code`
- non-string `lean_code`

Invalid rows are skipped by default and emitted as infra errors in results.

## Next Step

As new external formats are integrated, add adapter notes and examples in `FORMATS.md`.
