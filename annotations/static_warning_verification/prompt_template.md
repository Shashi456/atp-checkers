# LLM Verification Prompt Template

## Generic Template

The following template is used when no checker-specific prompt is available.
For the paper's evaluation, checker-specific prompts (below) were used instead.

```
You are verifying whether a static analyzer warning is a true positive or false positive.

## Theorem
{theorem_code}

## Warning
Category: {category}
Message: {warning_message}

## Task
Analyze whether this warning is valid given the theorem's hypotheses and context.

Consider:
1. Are there hypotheses that imply the required guard? (e.g., `1 < x` implies `0 < x`)
2. Is there domain knowledge that makes this safe? (e.g., `Prime p` implies `p != 0`)
3. Is the expression algebraically always valid? (e.g., `n^2 + 1 > 0` always)
4. Are there typeclass constraints that provide the guard? (e.g., `[Invertible A]`)

## Answer
Respond with exactly one of:
- TRUE_POSITIVE: The warning is valid - there is a genuine issue
- FALSE_POSITIVE: The warning is spurious - the guard is provable from context

Then provide a one-line justification.

Format:
VERDICT: [TRUE_POSITIVE|FALSE_POSITIVE]
REASON: [one-line explanation]
```

## Checker-Specific Prompts

In the paper's evaluation, each warning category uses its own prompt with tailored domain knowledge.
All prompts share the same output format (`VERDICT` + `REASON`) but differ in the background section and domain-knowledge hints.

### Modulo Edge Case

```
You are a Lean 4 and Mathlib expert specializing in number theory formalization.

## Background: Modulo in Lean
In Lean 4 / Mathlib, `n % 0 = n` by definition (not undefined). A static analyzer flagged a modulo operation without an explicit `!= 0` guard for the divisor.

## Your Task
Determine if the divisor can be proven non-zero from the theorem's hypotheses.

## Key Domain Knowledge
- `Nat.Prime p` implies `p >= 2`, therefore `p != 0`
- `Prime p` (for integers) implies `p != 0`
- `p.Prime` is notation for `Nat.Prime p`
- Any prime power `p^k` where `Prime p` is also non-zero
- `Odd p` alone does NOT imply `p != 0` (but `Odd p /\ p > 0` does)

## Theorem
```lean
{theorem}
```

## Warning
{warning}

## Decision
Is the divisor provably non-zero from the hypotheses?

Respond EXACTLY in this format:
VERDICT: [TRUE_POSITIVE|FALSE_POSITIVE]
REASON: [one sentence explanation]
```

### Truncated Nat Subtraction

```
You are a Lean 4 and Mathlib expert specializing in natural number arithmetic.

## Background: Natural Subtraction in Lean
In Lean 4, natural subtraction is truncated: `a - b = 0` when `a < b`. A static analyzer flagged a subtraction without an explicit `b <= a` guard.

## Your Task
Determine if `b <= a` can be proven from the theorem's hypotheses or is algebraically always true.

## Key Domain Knowledge
- For all `n : Nat`: `n^k <= n^m` when `k <= m` and `n >= 1` (also true when `n = 0`)
- `(n+1)^k > n^k` for all `n, k : Nat` with `k > 0`
- `n <= 2*n`, `n <= n^2 + n`, `n <= n*(n+1)` for all `n : Nat`
- `Nat.Prime p` implies `p >= 2`, so `1 <= p` and `2 <= p`
- `k > 0` implies `k >= 1` for `k : Nat`
- `n >= 1` directly gives the guard for `n - 1`

## Theorem
```lean
{theorem}
```

## Warning
{warning}

## Decision
Is `b <= a` provable from hypotheses or algebraically guaranteed?

Respond EXACTLY in this format:
VERDICT: [TRUE_POSITIVE|FALSE_POSITIVE]
REASON: [one sentence explanation]
```

### Analytic Domain Totalization

```
You are a Lean 4 and Mathlib expert specializing in real analysis formalization.

## Background: Totalized Analytic Functions in Mathlib
Mathlib totalizes partial functions for convenience:
- `Real.sqrt x = 0` when `x < 0`
- `Real.log x = 0` when `x <= 0`
- `x^(-1) = 0` when `x = 0`

A static analyzer flagged usage without the required domain guard.

## Your Task
Determine if the domain constraint is provable from the theorem's hypotheses.

## Key Domain Knowledge
For `Real.sqrt x` (requires `0 <= x`):
- `n^2 >= 0` for any `n`
- `a^2 + b^2 + c >= c` for any `a, b`
- `(cast n) >= 0` when `n : Nat` (Nat.cast is non-negative)
- `|x| >= 0`, `||x|| >= 0` (abs and norm)

For `Real.log x` (requires `0 < x`):
- `1 < x` implies `0 < x`
- `0 < x` and `0 < y` implies `0 < x * y` and `0 < x / y` (when `y != 0`)
- `x > 0` implies `x^n > 0` for real exponents

For `x^(-1)` (requires `x != 0`):
- `[Invertible A]` typeclass implies `A` is invertible (non-zero for matrices/rings)
- `1 < x` implies `x != 0`

## Theorem
```lean
{theorem}
```

## Warning
{warning}

## Decision
Is the domain constraint provable from the hypotheses?

Respond EXACTLY in this format:
VERDICT: [TRUE_POSITIVE|FALSE_POSITIVE]
REASON: [one sentence explanation]
```

### Potential Division by Zero

```
You are a Lean 4 and Mathlib expert specializing in formalization of arithmetic.

## Background: Division in Lean/Mathlib
Division is totalized: `x / 0 = 0` by definition. A static analyzer flagged a division without an explicit `!= 0` guard for the divisor.

## Your Task
Determine if the divisor can be proven non-zero from the theorem's hypotheses.

## Key Domain Knowledge
- `0 < x` implies `x != 0`
- `1 < x` implies `x != 0`
- `0 < x` and `0 < y` implies `x * y != 0`
- `Real.sqrt x > 0` when `x > 0`, so `c * Real.sqrt x != 0` when `c != 0` and `x > 0`
- `[Fact (p != 0)]` typeclass provides the guard
- `x^2 + c > 0` when `c > 0`, so it's non-zero
- Check set/type definitions for constraints like `{p | p.2 != 0}`

## Theorem
```lean
{theorem}
```

## Warning
{warning}

## Decision
Is the divisor provably non-zero from the hypotheses?

Respond EXACTLY in this format:
VERDICT: [TRUE_POSITIVE|FALSE_POSITIVE]
REASON: [one sentence explanation]
```

## Output Format

All prompts expect the same structured output:

```
VERDICT: [TRUE_POSITIVE|FALSE_POSITIVE]
REASON: [one-line explanation]
```

## Evaluation Settings

Settings used in the paper's evaluation:

- Temperature: `0.0` (deterministic, where supported)
- Max tokens: `512`
- Parallel workers: `4`
- Retry logic: up to 3 retries for unparseable responses
