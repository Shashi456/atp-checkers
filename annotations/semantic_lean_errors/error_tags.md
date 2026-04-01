# Error Tag Taxonomy 

Use a small set of primary tags for prompt coverage. Detail tags refine the primary tag for analysis. Detail tags are always attached to one primary tag.

**Important**: Multi-label is expected and normal. In practice, formalization_error, definition_mismatch, domain_mismatch, and quantifier_indexing_mismatch are all subsets of "Lean statement doesn't match intent." We split them because they're diagnostically useful and promptable.

## Primary tags (error_primary)

- problem_statement_error
  - NL problem is ambiguous, ill-posed, unformalizable, or asks the wrong question.
  - Example: "Find the largest prime number."
  - Motivation: these cannot be fixed by better Lean syntax alone.
  - Common detail tags: ambiguity_or_unformalizable, wrong_question, incomplete_statement, unprovable_problem, literal_mismatch

- specification_error
  - Intended math spec is missing or incorrect (assumptions, constraints, scope).
  - Example: NL says "positive integers" but the spec omits n > 0.
  - Motivation: the math spec itself is wrong or incomplete.
  - Common detail tags: missing_hypothesis, extra_hypothesis, distinctness_missing, incomplete_spec, incorrect_spec, oversimplified_spec, base_case_missing, division_by_zero_risk, uniqueness_missing

- formalization_error
  - Lean statement does not match the intended spec (semantic mismatch).
  - Example: "sum of first n positive integers" encoded with List.range n (starts at 0).
  - Motivation: spec is right, but the Lean goal is not.
  - Common detail tags: goal_mismatch, missing_subgoal, premise_translation_error, goal_translation_error, connective_mismatch, contradictory_premises

- domain_mismatch
  - Wrong type or domain (Nat vs Int, 0..99 vs 1..100, real vs complex).
  - Example: NL over integers, Lean uses Nat.
  - Motivation: type-level mismatch changes truth or meaning.
  - Common detail tags: type_mismatch, domain_of_variables_mismatch, truncation_issue

- definition_mismatch
  - Wrong Lean concept or definition for the informal notion (misuse of concept).
  - Example: encoding absolute value as Nat subtraction.
  - Motivation: the Lean objects do not represent the intended math.
  - Common detail tags: misuse_of_concept, wrong_operator, wrong_constant, library_usage_error, incorrect_function_choice, paper_vs_lean_semantics, encoding_issue
  
- quantifier_indexing_mismatch
  - Wrong quantifiers, bounds, or indexing (scope/order/bounds off).
  - Example: forall i, exists j instead of exists j, forall i.
  - Motivation: subtle scope and bounds errors change the claim.
  - Common detail tags: quantifier_mismatch, indexing_mismatch, bound_mismatch, variable_mismatch

## Boundary Rules (disambiguating overlapping categories)

### specification_error vs formalization_error

These are the easiest to confuse. Use this rule of thumb:

- **specification_error** = the *mathematical statement* (as math) is missing/extra/wrong constraints.
  - You can explain the problem **without mentioning Lean-specific encodings**.
  - Examples: missing "distinct", missing "n > 0", wrong bound, dropped equation.
- **formalization_error** = the intended spec is clear, but the *Lean statement* mismatches due to translation/encoding of that spec.
  - Your explanation **mentions the Lean encoding choice** (range starts at 0, order of arguments, ∧ vs →, etc.).

### domain_mismatch vs definition_mismatch

- **domain_mismatch** = wrong *carrier type* (ℕ vs ℤ, Fin 100 vs {1..100}, ℝ vs ℂ, 0-indexed vs 1-indexed domain).
- **definition_mismatch** = wrong *meaning of the predicate/operator/object* even if types look plausible.
  - e.g., modeling "touching" by area intersection when it should include boundary-only contact; modeling "region" as an arbitrary set instead of a connected component; using sup metric when Euclidean intended.

If the type choice *induces* the wrong meaning, tag **both** domain_mismatch + definition_mismatch.

### quantifier_indexing_mismatch vs formalization_error

- **quantifier_indexing_mismatch** = core bug is scope/order/bounds/indexing (∀/∃ swap, off-by-one, i≤n vs i<n).
- **formalization_error** = broader mismatch (wrong goal shape, missing subgoal/witness, premise translated wrong in a non-indexing way).

## Detail tags (error_tags) with examples

### problem_statement_error detail tags
- ambiguity_or_unformalizable: "Find the largest prime number."
- wrong_question: NL asks for a number, Lean proves an unrelated property.
- incomplete_statement: missing a stated condition like "distinct" or "positive".
- unprovable_problem: NL statement is false in the stated domain.
- literal_mismatch: Lean claims specific numeric answer (e.g., IsGreatest ... 54) that contradicts the NL solution (e.g., NL proves 72).

### specification_error detail tags
- missing_hypothesis: missing x != 0 before dividing by x.
- extra_hypothesis: adds n > 0 when NL has no such constraint.
- distinctness_missing: pigeonhole statement without a != b.
- incomplete_spec: omits a required equation like x1 + x2 + x3 + x4 = 20.
- incorrect_spec: uses the wrong condition or bound from the NL.
- oversimplified_spec: drops conditions to make the problem easier.
- base_case_missing: forgets to exclude n = 0 when NL assumes n >= 1.
- division_by_zero_risk: missing guard that a denominator is nonzero (variant of missing_hypothesis).
- uniqueness_missing: NL says "the unique x" or "exactly one" but Lean uses ∃ instead of ∃!.

### formalization_error detail tags
- goal_mismatch: proves a claim about 0..n-1 instead of 1..n.
- missing_subgoal: omits existence of a witness required by the NL.
- premise_translation_error: NL premise encoded with the wrong quantifier or scope.
- goal_translation_error: encodes equality as inequality (or vice versa).
- connective_mismatch: Wrong logical connective — ∧ vs → (conjunction vs implication), ↔ vs → (biconditional vs implication), ∧ vs ∨ ("and" vs "or"), misplaced negation (¬(∃x…) vs ∃x,¬…). Example: NL says "if P then Q" but Lean encodes "P ∧ Q".
- contradictory_premises: Lean hypotheses are mutually contradictory (cannot all be satisfied). Example: StrictMono a combined with a n = a 0.

### domain_mismatch detail tags
- type_mismatch: uses Nat where Int or Real is required.
- domain_of_variables_mismatch: uses 0..99 instead of 1..100.
- truncation_issue: Nat subtraction used where negatives are needed.

### definition_mismatch detail tags
- misuse_of_concept: uses Nat subtraction to model absolute difference.
- wrong_operator: uses sum instead of product in a counting formula.
- wrong_constant: subtracts 4 instead of 1 in a transition rule.
- library_usage_error: uses the wrong Lean API for the intended notion.
- incorrect_function_choice: List.range used for a 1-indexed sum.
- paper_vs_lean_semantics: "limit" encoded without filters or topology.
- encoding_issue: Lean encoding is too weak/strong vs the intended concept.

### quantifier_indexing_mismatch detail tags
- quantifier_mismatch: forall x, exists y vs exists y, forall x.
- indexing_mismatch: off-by-one indexing in a sequence definition.
- bound_mismatch: i <= n used where i < n is required.
- variable_mismatch: compares A x y = x instead of A x y = i.

### General

## Meta tags (non-prompt, optional)

Use these as metadata for pipeline or dataset issues. They do not require separate prompts.

- answer_handling_mismatch: solution leaked, missing, wrong, or MC mismatch.
- tooling_error: syntax_error, type_error, or not validated by Lean REPL.
- prover_failure: proof search fails despite correct statement.
- autoformalization_failure: pipeline could not produce a Lean statement.
- version_drift: Lean/toolchain change invalidates prior statements.
- informalization_issue: Lean -> NL output is incorrect or misleading.
- code_style_issue: readability or style problem (not semantic).
- api_design_issue: notational or API design mismatch (non-semantic).
- unused_parameter: free variable/parameter in statement that is never used (may be harmless refactor or may change generalization).
- extra_parameter: parameter added that isn't in NL problem and changes the meaning.

## Detail tag mapping (recommended)

Detail tags refine a primary tag:

- problem_statement_error: ambiguity_or_unformalizable, wrong_question, incomplete_statement, unprovable_problem, literal_mismatch
- specification_error: missing_hypothesis, extra_hypothesis, distinctness_missing, incomplete_spec, incorrect_spec, oversimplified_spec, base_case_missing, division_by_zero_risk, uniqueness_missing
- formalization_error: goal_mismatch, missing_subgoal, premise_translation_error, goal_translation_error, connective_mismatch, contradictory_premises
- domain_mismatch: type_mismatch, domain_of_variables_mismatch, truncation_issue
- definition_mismatch: misuse_of_concept, wrong_operator, wrong_constant, library_usage_error, incorrect_function_choice, paper_vs_lean_semantics, encoding_issue
- quantifier_indexing_mismatch: quantifier_mismatch, indexing_mismatch, bound_mismatch, variable_mismatch

