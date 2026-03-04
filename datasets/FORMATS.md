# Dataset Format Support

## Supported Formats

| Format | Flag | Notes |
|--------|------|-------|
| JSONL | `--format jsonl` (default) | One JSON object per line |
| JSON array | `--format json` | File containing `[{...}, {...}]` |
| Lean directory | `--format lean` | Directory of `.lean` files, one problem per file |
| HuggingFace | `--format hf` | Any HuggingFace dataset with recognized fields |

## Schema Auto-Detection

All formats use the same field resolver. You do not need to specify which schema
your dataset uses — it is detected automatically.

### ID field (first match)

`id` → `name` → `theorem_name` → `problem_id` → auto-generated from row index

### Code field (first match)

| Priority | Field(s) | Used by |
|----------|----------|---------|
| 1 | `lean_code` | Canonical ATP-checkers format |
| 2 | `lean4_code` | MOBench (pre-joined) |
| 3 | `header` + `formal_statement` | DeepSeek-ProverBench, DeepSeek ProofNet, MOBench |
| 4 | `lean4_src_header` + `lean4_formalization` | ProofNetSharp |
| 5 | `formal_statement` (alone) | CombiBench, MiniF2F (HF) |
| 6 | `formal` (alone) | justincasher miniF2F |

### Natural language field (first match)

`natural_language` → `nl_statement` → `informal_prefix` → `natural`

## `--header-file`

Some datasets (e.g. justincasher miniF2F) contain only theorem statements with no
import headers. Use `--header-file` to prepend a Lean header to every problem:

```bash
python -m runner test.jsonl -w ./linter -o results/ --header-file headers/mathlib.lean
```

Example header file (`headers/mathlib.lean`):
```lean
import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
```

Duplicate imports are harmless — Lean 4 silently ignores them.

## CLI Examples

```bash
# Local JSONL (any recognized schema)
python -m runner dataset.jsonl -w ./linter -o results/
python -m runner proofnet.jsonl -w ./linter -o results/

# JSON array
python -m runner problems.json --format json -w ./linter -o results/

# Directory of .lean files
python -m runner ./FATE-M/ --format lean -w ./linter -o results/

# HuggingFace datasets
python -m runner AI-MO/CombiBench --format hf -w ./linter -o results/
python -m runner AI-MO/CombiBench --format hf --split test -w ./linter -o results/
python -m runner deepseek-ai/DeepSeek-ProverBench --format hf -w ./linter -o results/
python -m runner PAug/ProofNetSharp --format hf --split test -w ./linter -o results/

# Headerless dataset with import header
python -m runner test.jsonl -w ./linter -o results/ --header-file headers/mathlib.lean
python -m runner hoskinson-center/proofnet --format hf --split test -w ./linter -o results/ --header-file headers/mathlib.lean
```

## Design Rule

All loaders produce the canonical internal representation:
- `id: str`
- `lean_code: str`
- `metadata: dict`
