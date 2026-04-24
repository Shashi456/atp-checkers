# ATP Checkers

A Lean 4 static analysis tool that detects **semantic traps** in autoformalized
mathematics — code that compiles successfully but silently produces incorrect
results. Built for evaluating LLM-generated Lean formalizations at scale.

The linter uses **semantic guard checking**: rather than simple pattern matching,
it attempts to prove (via `assumption` → `omega` → `grind`) that safety guards
exist or that dangerous conditions hold, producing machine-verifiable confidence
levels on every finding.

Guard mining is polarity-aware. For example, in `x ≠ 0 ∧ 1 / x = x`, the left
conjunct safely guards the right. But in `¬ (x ≠ 0 ∧ 1 / x = x)` or
`(x ≠ 0 ∧ 1 / x = x) → True`, that same conjunct is not treated as an active
guard, so the division warning still fires. This avoids an earlier soundness
bug where conjunction mining in negative position could suppress real warnings.

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
| Counterexample | Concrete counterexamples via `decide`/Plausible | Enumeration + random testing |
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
| `dataset` | Dataset source — a file path (`jsonl`/`json`), a directory of `.lean` files (`lean`), or a HuggingFace repo ID (`hf`). Interpretation is controlled by `--format`. |
| `--workspace, -w` | Path to built Lean workspace (must contain `.lake` build artifacts) |
| `--output, -o` | Output directory (created if needed) |

### Options

| Flag | Default | Description |
|------|---------|-------------|
| `--format, -f` | `jsonl` | Dataset format: `jsonl`, `json`, `lean` (directory of `.lean` files), or `hf` (HuggingFace repo ID) |
| `--split` | auto | Split to use for HuggingFace datasets (prefers `test`, then the first available) |
| `--header-file` | — | Path to a `.lean` file whose contents are prepended to every problem (useful for project-wide imports or open namespaces) |
| `--backend` | `subprocess` | Execution backend: `subprocess` (default, resolves lean env once) or `persistent` (REPL, requires `lake build repl`) |
| `--timeout` | 30 | Timeout per problem in seconds |
| `--workers, -j` | 1 | Number of parallel workers |
| `--append` | off | Append to existing `results.jsonl` instead of failing |
| `--skip-existing` | off | Resume interrupted runs (skips already-processed problem IDs) |
| `--toolchain` | auto | Lean toolchain string (auto-detected from workspace) |

The default `subprocess` backend resolves the workspace Lean environment once
and invokes the Lean binary directly per problem, with import-bundle caching
to avoid repeated import cost. Use `--backend persistent` for REPL-based
execution (requires `lake build repl`).

> **Concurrency note:** `--workers > 1` parallelizes problems within a single
> runner process safely. Do **not** point two independent runner processes at
> the same `--output` directory — the runner does not take a filesystem lock
> on `results.jsonl`, so concurrent appenders can interleave records. Use one
> output directory per runner, or merge post-hoc.

**Extra Lean search paths:** For datasets that depend on modules outside the
workspace (e.g., a local Mathlib fork or companion repo), set the
`ATP_EXTRA_LEAN_PATHS` environment variable (colon-separated) or include
`"extra_lean_paths": ["/path/to/lib"]` in each problem's metadata.

### Examples

```bash
# Quick smoke test (no Mathlib needed)
python -m runner datasets/examples/minimal_no_mathlib.jsonl -w . -o out --timeout 60

# Full benchmark run with parallelism (persistent REPL, default)
python -m runner my_benchmark.jsonl -w . -o results -j 4 --timeout 120

# Fallback to subprocess mode (slower, no REPL needed)
python -m runner my_benchmark.jsonl -w . -o results -j 4 --backend subprocess

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
    "lean_toolchain": "leanprover/lean4:v4.28.0",
    "timestamp": "2026-02-23T12:42:44.125493+00:00"
  },
  "compile_error": false,
  "compile_error_message": null,
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
| `compile_error` | Lean code failed to compile before the linter completed |
| `timeout` | Problem exceeded the time limit |
| `infra_error` | Runner infrastructure failure |

`compile_error` is also tracked additively in each result row via:

- `compile_error`: whether Lean reported compile errors
- `compile_error_message`: captured compile diagnostics

This means a row can have `status = "findings"` and `compile_error = true`
when the linter completed and emitted findings despite compile errors elsewhere
in the file.

### Confidence Model

Every finding carries a `confidence` field:

| Value | Meaning |
|-------|---------|
| `"proven"` | The linter constructively proved the issue exists (e.g., proved `divisor = 0` from context). Low false-positive rate. |
| `"maybe"` | Suspicious pattern detected, but the prover could not confirm or deny the issue. Meaningful false-positive rate. |

The `provedBy` field records *how* the issue was proved (e.g., `"omega"`, `"assumption"`, `"decide"`, `"definitional"`, `"plausible"`), or `null` for `"maybe"` findings.

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
├── lean-toolchain             # Lean 4 v4.28.0 (source of truth)
├── Main.lean                  # CLI entry point
├── src/AtpLinter/             # 13 checker modules + core infrastructure
├── test/                      # 7 gating + 3 demo test suites
├── runner_tests/              # Python runner unit tests
├── runner/                    # Python JSONL batch runner
├── datasets/examples/         # Smoke test datasets
├── LIMITATIONS.md             # What the linter can and cannot do
└── llm.txt                    # Detailed implementation reference
```

## Building from Source

**Requirements:** Lean 4 v4.28.0 (pinned via `lean-toolchain`), Python ≥ 3.10.
The Python runner uses only the stdlib — no `pip install` needed for pure
linting; optional `ruff` for dev lint.

### One-liner bootstrap

```bash
git clone https://github.com/Shashi456/atp-checkers.git
cd atp-checkers
./install.sh                  # elan + lake exe cache get + lake build + smoke test
```

### Manual steps

```bash
# 1. Install elan (Lean version manager) if you don't have it
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  | sh -s -- -y --default-toolchain none

# 2. Clone the repo
git clone https://github.com/Shashi456/atp-checkers.git
cd atp-checkers

# 3. Fetch pre-built Mathlib oleans from the community cache (optional but saves
#    30+ minutes on first build; the fallback is building Mathlib locally)
lake exe cache get || true

# 4. Build the linter (2958 jobs including Mathlib — ~5 min with cache, ~30 min without)
lake build

# 5. Run gating tests (should all pass)
lake build AtpLinterTest

# 6. Run demo tests (non-gating, diagnostic output)
lake build AtpLinterDemo
```

**Smoke test without Mathlib** (useful to confirm the runner works before
committing to the full Mathlib build):

```bash
python -m runner datasets/examples/minimal_no_mathlib.jsonl \
  --workspace . --output /tmp/smoke --timeout 30
```

**If `lake build` fails with `incompatible header` errors** on `.olean` files,
the `.lake/packages/mathlib/.lake/build/` tree is stale (built against a
different Lean binary). Fix: `lake build Mathlib` to force a rebuild, or
`rm -rf .lake/packages/mathlib/.lake/build && lake build` for a clean slate.

## Limitations

See [LIMITATIONS.md](LIMITATIONS.md) for a detailed discussion of what static
analysis can and cannot catch in Lean formalizations, including:

- Why guard analysis is local (can't follow definitions)
- Prover incompleteness and timeout tradeoffs
- Confidence vs ground truth
- Why proof terms are not analyzed

## CI

GitHub Actions workflow at `.github/workflows/lean.yml` runs `lake build` and
`lake build AtpLinterTest`, plus Python runner unit tests, on push.

## License

MIT — see [LICENSE](LICENSE).
