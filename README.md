# ATP Checkers

A Lean 4 static analysis tool that detects **semantic traps** in autoformalized
mathematics — code that compiles successfully but silently produces incorrect
results. Built for evaluating LLM-generated Lean formalizations at scale.

The linter uses **semantic guard checking**: rather than simple pattern matching,
it attempts to prove (via `assumption` → `omega` → `grind`) that safety guards
exist or that dangerous conditions hold, producing machine-verifiable confidence
levels on every finding.

## Quick Start

```bash
# Build the linter
lake build

# Run tests
lake build AtpLinterTest

# Lint a dataset (no Mathlib needed for this example)
python -m runner datasets/examples/minimal_no_mathlib.jsonl \
  --workspace . --output out --timeout 60
```

Results are written to `out/results.jsonl`.

## What It Detects

13 checkers covering the most common mechanical errors in LLM-generated formalizations:

| Checker | Detects | Method |
|---------|---------|--------|
| Nat Subtraction | `a - b` on Nat without `b ≤ a` guard | Semantic proof |
| Division by Zero | `a / b` without `b ≠ 0` guard | Semantic proof |
| Int Div Truncation | `1/4 = 0` silent truncation | Literal analysis |
| Int.toNat | `Int.toNat` without `x ≥ 0` guard | Semantic proof |
| List.range | 0-indexed ranges (off-by-one risk) | Name matching |
| Modulo by Zero | `a % b` without `b ≠ 0` guard | Semantic proof |
| Axiom | User `axiom` declarations asserting Prop | Declaration type |
| Vacuous Hypotheses | Contradictory hyps / empty domains | Prove `False` |
| Unused Binder | `∀ x, ...` where `x` is unused | AST analysis |
| Counterexample | Concrete counterexamples via `decide` | Enumeration |
| Cast After Truncation | Cast applied after truncating operation | Pattern matching |
| Exponent Truncation | Negative/zero exponent issues | Guard + literals |
| Analytic Domain | `x⁻¹`/sqrt/log without domain guard | Semantic proof |

## Input Format

JSONL file with one problem per line:

```json
{"id": "problem_1", "lean_code": "theorem foo : ...", "natural_language": "optional NL statement"}
```

**Required fields:**
- `id` — unique problem identifier (string)
- `lean_code` — Lean 4 code to analyze (string, without `import` or `#check_atp` — the runner adds these)

**Optional fields** (preserved in output under `metadata`):
- `natural_language` — natural language statement
- `source` — dataset/benchmark name
- Any other fields (benchmark-specific tags, etc.)

See `datasets/FORMATS.md` for planned format support.

## Runner CLI

```
python -m runner <dataset.jsonl> --workspace <path> --output <dir> [options]
```

### Required Arguments

| Flag | Description |
|------|-------------|
| `dataset` | Path to input JSONL file |
| `--workspace, -w` | Path to built Lean workspace (must contain `.lake` build artifacts) |
| `--output, -o` | Output directory (created if needed) |

### Options

| Flag | Default | Description |
|------|---------|-------------|
| `--timeout` | 30 | Timeout per problem in seconds |
| `--workers, -j` | 1 | Number of parallel workers |
| `--append` | off | Append to existing `results.jsonl` instead of failing |
| `--skip-existing` | off | Resume interrupted runs (skips already-processed problem IDs) |
| `--toolchain` | auto | Lean toolchain string (auto-detected from workspace) |

### Examples

```bash
# Quick smoke test (no Mathlib needed)
python -m runner datasets/examples/minimal_no_mathlib.jsonl -w . -o out --timeout 60

# Full benchmark run with parallelism
python -m runner my_benchmark.jsonl -w . -o results --workers 8 --timeout 120

# Resume an interrupted run
python -m runner my_benchmark.jsonl -w . -o results --skip-existing --append
```

## Output Format

Each line of `results.jsonl` is a JSON object:

```json
{
  "problem_id": "problem_1",
  "source": "my_benchmark",
  "status": "findings",
  "findings": [
    {
      "category": "Potential Division by Zero",
      "severity": "WARNING",
      "declaration": "myDiv",
      "message": "a / b has no guard ensuring b ≠ 0",
      "suggestion": "Add hypothesis `h : b ≠ 0` or `h : b > 0`",
      "confidence": "proven",
      "provedBy": "assumption"
    }
  ],
  "error_message": null,
  "duration_ms": 1823,
  "provenance": {
    "runner_version": "0.1.0",
    "linter_version": "0.4.0",
    "lean_toolchain": "leanprover/lean4:v4.24.0",
    "timestamp": "2026-02-23T12:42:44.125493+00:00"
  },
  "metadata": {
    "natural_language": "For all natural numbers a and b, a/b is natural."
  }
}
```

### Status Values

| Status | Meaning |
|--------|---------|
| `ok` | No findings — code passed all checks |
| `findings` | One or more issues detected |
| `compile_error` | Lean code failed to compile |
| `timeout` | Problem exceeded the time limit |
| `infra_error` | Runner infrastructure failure |

### Confidence Model

Every finding carries a `confidence` field:

| Value | Meaning |
|-------|---------|
| `"proven"` | The linter constructively proved the issue exists (e.g., proved `divisor = 0` from context). Low false-positive rate. |
| `"maybe"` | Suspicious pattern detected, but the prover could not confirm or deny the issue. Meaningful false-positive rate. |

The `provedBy` field records *how* the issue was proved (e.g., `"omega"`, `"assumption"`, `"decide"`, `"definitional"`), or `null` for `"maybe"` findings.

When a safety guard cannot be proved, the linter also attempts to prove the
**dangerous condition** (unsafety proving). For example, if `b ≠ 0` can't be
proved for `a / b`, it tries to prove `b = 0`. Success upgrades the finding
from `"maybe"` to `"proven"`.

## Using with LLMs for Deeper Review

The linter catches mechanical/structural errors but cannot determine whether a
formalization correctly captures the *intended* mathematical statement. For that,
LLM-based semantic review is a natural complement.

A typical multi-stage pipeline:

1. **Linter pass** (this tool) — fast, automated, catches division-by-zero,
   vacuous hypotheses, truncation, etc. Filter or prioritize based on
   `confidence` level.

2. **LLM review** — feed the natural-language statement and the Lean
   formalization to an LLM. Ask it to identify semantic mismatches: wrong
   quantifier structure, missing conditions, incorrect definitions, etc.
   The linter's `findings` and `confidence` annotations can be included in
   the prompt as structured evidence for the LLM to consider.

3. **Human review** — for high-stakes applications, final verification by
   a domain expert.

Prompt templates for the LLM review stage are planned for a future release.
The output JSONL format is designed to be LLM-friendly — each result is a
self-contained JSON object with the original `lean_code`, `natural_language`
metadata, and structured findings that can be directly embedded in prompts.

## Project Structure

```
atp-checkers/
├── lakefile.lean              # Build config
├── lean-toolchain             # Lean 4 v4.24.0
├── Main.lean                  # CLI entry point
├── src/AtpLinter/             # 13 checker modules + core infrastructure
├── test/                      # 7 gating + 3 demo test suites
├── runner/                    # Python JSONL batch runner
├── datasets/examples/         # Smoke test datasets
├── LIMITATIONS.md             # What the linter can and cannot do
├── llm.txt                    # Detailed implementation reference
└── AGENTS.md                  # Agent/operator instructions
```

## Building from Source

**Requirements:** Lean 4 v4.24.0, Python 3.8+

```bash
# Clone and build
git clone https://github.com/Shashi456/atp-checkers.git
cd atp-checkers
lake build                    # ~36 compile jobs

# Run gating tests (should all pass)
lake build AtpLinterTest

# Run demo tests (non-gating, diagnostic output)
lake build AtpLinterDemo
```

**Mathlib note:** The linter depends on Mathlib for type information. `lake build`
fetches and builds it automatically, which takes significant time on first run.
The `minimal_no_mathlib.jsonl` dataset works without a full Mathlib build for
quick smoke testing.

## Limitations

See [LIMITATIONS.md](LIMITATIONS.md) for a detailed discussion of what static
analysis can and cannot catch in Lean formalizations, including:

- Why guard analysis is local (can't follow definitions)
- Prover incompleteness and timeout tradeoffs
- Confidence vs ground truth
- Why proof terms are not analyzed

## CI

GitHub Actions workflow at `.github/workflows/lean.yml` runs `lake build` and
`lake build AtpLinterTest` on push.
