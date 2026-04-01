# Record Schema

Each record represents a single static-analyzer warning paired with a human verdict.

## Fields

| Field | Type | Description |
|-------|------|-------------|
| `id` | `string` | Unique identifier for the example. Synthetic examples use descriptive slugs (`modulo_fp_1`). Real examples use the original problem ID from the source dataset (`number_theory__p11`, `formalmath_omni_theorem_3500`, etc.). |
| `category` | `string` | Which static checker produced the warning. One of the four categories listed below. |
| `source` | `string` | Provenance of the example: `synthetic` (hand-crafted), `real` (DeepSeek-ProverBench), `formalmath` (FormalMATH), or `minif2f_harmonic` (miniF2F via Harmonic port). |
| `verdict` | `string` | Human-assigned ground-truth label. `false_positive` means the warning is spurious (the guard is provable from context). `true_positive` means the warning is valid (there is a genuine issue). |
| `justification` | `string` | One-line human explanation for the verdict. |
| `lean_code` | `string` | The Lean 4 theorem or definition that triggered the warning. May be abbreviated with `...` for long declarations. |
| `warning_message` | `string` | The warning message produced by the static checker. |

## Category Values

| Category | Checker | What it flags |
|----------|---------|---------------|
| `modulo_edge_case` | Modulo Edge Case | `a % b` without a guard ensuring `b != 0` |
| `truncated_nat_subtraction` | Truncated Nat Subtraction | `a - b` on `Nat` without a guard ensuring `b <= a` |
| `analytic_domain_totalization` | Analytic Domain Totalization | `sqrt`, `log`, or `x^(-1)` without the required domain guard |
| `potential_division_by_zero` | Potential Division by Zero | `a / b` without a guard ensuring `b != 0` |

## Verdict Semantics

- `false_positive`: The static checker's warning is spurious. The required guard **is** provable from the theorem's hypotheses, type constraints, or algebraic properties, but the checker's fast local tactics (`omega`, `assumption`) could not establish it.
- `true_positive`: The warning is valid. The required guard **is not** provable from context, meaning the formalization has a genuine issue (missing hypothesis, unconstrained variable, etc.).
