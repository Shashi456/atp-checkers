# Evaluation Prompts - Few-Shot 

## System Prompt

```text
You are an expert auditor for NL → Lean 4 formalizations.

You will be given:
- Natural language problem statement (NL)
- Lean 4 code snippet (Lean). Focus on the *main theorem/definition statement* that encodes the NL. Ignore the proof (`by sorry` etc.).

Your task: For ONE specific error category (given below), decide whether the Lean statement has an error of that category relative to the NL problem.

Important rules:
- Output MUST be valid JSON (no markdown, no extra keys).
- Say NO if the formalization is correct for this category, even if some other category might make sense. 
- Say NO if there is no semantic error at all, many formalizations are actually correct!
- Only say YES if you find a clear, concrete error matching THIS category's definition.
- If you are not confident, set NeedsReview = "YES".
- DetailTags must be chosen ONLY from the allowed list for this category.

Return JSON with keys exactly:
Verdict: "YES" or "NO"
Explanation: 1–3 sentences with concrete evidence (what phrase/construct is wrong, or why it's correct).
DetailTags: array of strings (empty if Verdict = "NO")
NeedsReview: "YES" or "NO"
```

---

## Prompt 1 — problem_statement_error

```text
CATEGORY: problem_statement_error

Definition: The NL problem itself is ambiguous, ill-posed, unformalizable, or false as stated. Also includes cases where the Lean claims a specific answer contradicting the NL solution.

Allowed DetailTags: ambiguity_or_unformalizable, wrong_question, incomplete_statement, unprovable_problem, literal_mismatch, other

---

FEW-SHOT EXAMPLE (Verdict: YES — NL constraints are inconsistent)
[Natural language]
Find positive integers a, b, and c such that a + b + c = 2 and abc = 1.

[Lean]
theorem synthetic_positive_triple_impossible :
  ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 2 ∧ a * b * c = 1 := by sorry

{"Verdict": "YES", "Explanation": "Positive integers with product 1 must all equal 1, so their sum is 3, not 2. The NL problem is impossible as stated.", "DetailTags": ["unprovable_problem"], "NeedsReview": "NO"}

---

FEW-SHOT EXAMPLE (Verdict: NO — the formalization is fine for this category)
[Natural language]
Prove that the removal of an edge from a tree leaves a forest of two trees.

[Lean]
theorem brualdi_ch11_59 {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : IsTree T) (e : Sym2 V) (he : e ∈ T.edgeSet) :
    ∃ (T1 T2 : SimpleGraph V), IsTree T1 ∧ IsTree T2 ∧
      T1.edgeSet ∪ T2.edgeSet = T.edgeSet \ {e} ∧
      Disjoint T1.support T2.support := by sorry

{"Verdict": "NO", "Explanation": "The NL problem is well-posed, and the Lean statement matches it directly.", "DetailTags": [], "NeedsReview": "NO"}

---

Input:
[Natural language]
{{PROBLEM_NL}}

[Lean]
{{LEAN_CODE}}

Return JSON only.
```

---

## Prompt 2 — specification_error

```text
CATEGORY: specification_error

Definition: The mathematical specification is missing/extra/incorrect assumptions, constraints, or scope.

Allowed DetailTags: missing_hypothesis, extra_hypothesis, distinctness_missing, incomplete_spec, incorrect_spec, oversimplified_spec, base_case_missing, division_by_zero_risk, uniqueness_missing, other

Boundary: If the issue is wrong type (ℕ vs ℤ), that's domain_mismatch. If it's quantifier/indexing, that's quantifier_indexing_mismatch.

---

FEW-SHOT EXAMPLE (Verdict: YES — the stated answer is omitted from the formal spec)
[Natural language]
The unique solution to the linear equation 2 = -12 + 2r is r = 7.

[Lean]
def given_equation (r : ℝ) : Prop := (2 : ℝ) = (-12 : ℝ) + 2 * r

theorem unique_solution : ∃! r : ℝ, given_equation r := by sorry

{"Verdict": "YES", "Explanation": "The NL says not just that a unique solution exists, but specifically that the solution is r = 7. The Lean theorem only states unique existence and omits the stated witness.", "DetailTags": ["incomplete_spec"], "NeedsReview": "NO"}

---

FEW-SHOT EXAMPLE (Verdict: NO — the formalization is fine for this category)
[Natural language]
Prove that a group of even order contains an element of order 2.

[Lean]
theorem exercise_2_11_3 {G : Type*} [Group G] [Fintype G]
  (hG : Even (card G)) : ∃ x : G, orderOf x = 2 := by sorry

{"Verdict": "NO", "Explanation": "The Lean statement includes the needed finite-group setting and the even-order hypothesis, then states the intended conclusion directly. There is no missing or incorrect specification here.", "DetailTags": [], "NeedsReview": "NO"}

---

Input:
[Natural language]
{{PROBLEM_NL}}

[Lean]
{{LEAN_CODE}}

Return JSON only.
```

---

## Prompt 3 — formalization_error

```text
CATEGORY: formalization_error

Definition: The spec is clear, but the Lean encoding doesn't match due to translation choices (wrong connectives, contradictory premises, structural mismatch).

Allowed DetailTags: goal_mismatch, missing_subgoal, premise_translation_error, goal_translation_error, connective_mismatch, contradictory_premises, other

Boundary: Wrong type → domain_mismatch. Wrong concept → definition_mismatch. Indexing issues → quantifier_indexing_mismatch.

---

FEW-SHOT EXAMPLE (Verdict: YES — intended property is mistranslated)
[Natural language]
There are exactly three positive real numbers k such that the function
f(x) = ((x - 18)(x - 72)(x - 98)(x - k)) / x
attains its minimum value at exactly two positive real numbers x. The sum of these three values is 240.

[Lean]
noncomputable def f (k x : ℝ) : ℝ :=
  (x - 18) * (x - 72) * (x - 98) * (x - k) / x

def exactly_two_minima (k : ℝ) : Prop :=
  ∃ (a b : ℝ), 0 < a ∧ 0 < b ∧ a ≠ b ∧ (f k a = f k b) ∧
    (∀ (x : ℝ), 0 < x → (f k x > f k a ∨ x = b))

theorem aime_2025ii_p15 :
  ∃ (k₁ k₂ k₃ : ℝ), 0 < k₁ ∧ 0 < k₂ ∧ 0 < k₃ ∧
    k₁ ≠ k₂ ∧ k₁ ≠ k₃ ∧ k₂ ≠ k₃ ∧
    exactly_two_minima k₁ ∧ exactly_two_minima k₂ ∧ exactly_two_minima k₃ ∧
    k₁ + k₂ + k₃ = 240 := by sorry

{"Verdict": "YES", "Explanation": "The Lean encoding of 'exactly two minima' is wrong. Plugging x = a into the universal clause forces f k a > f k a or a = b, which is impossible, so the intended property has been mistranslated.", "DetailTags": ["goal_translation_error"], "NeedsReview": "NO"}

---

FEW-SHOT EXAMPLE (Verdict: NO — the formalization is fine for this category)
[Natural language]
Prove that the complement of a disconnected graph is connected.

[Lean]
theorem brualdi_ch12_34 {V : Type*} (G : SimpleGraph V) (h : ¬ G.Connected) :
    Gᶜ.Connected := by sorry

{"Verdict": "NO", "Explanation": "The Lean statement directly matches the NL claim: if a graph is disconnected, then its complement is connected. There is no translation-structure error here.", "DetailTags": [], "NeedsReview": "NO"}

---

Input:
[Natural language]
{{PROBLEM_NL}}

[Lean]
{{LEAN_CODE}}

Return JSON only.
```

---

## Prompt 4 — domain_mismatch

```text
CATEGORY: domain_mismatch

Definition: The Lean uses wrong carrier type/domain, changing meaning (ℕ vs ℤ, Fin n vs 1..n, truncating subtraction/division).

Allowed DetailTags: type_mismatch, domain_of_variables_mismatch, truncation_issue, other

Boundary: Missing constraints with correct domain → specification_error.

---

FEW-SHOT EXAMPLE (Verdict: YES — the variable domain is wrong)
[Natural language]
Prove that lim_{n→∞} (sqrt(n^2 + n) - n) = 1/2.

[Lean]
theorem exercise_3_2a :
  Tendsto (λ (n : ℝ) => (sqrt (n^2 + n) - n)) atTop (𝓝 (1 / 2)) := by sorry

{"Verdict": "YES", "Explanation": "The NL is a sequence limit with n ranging over the natural-number index. The Lean statement instead takes n : ℝ, so it changes the carrier of the variable and therefore the meaning of the limit statement.", "DetailTags": ["type_mismatch"], "NeedsReview": "NO"}

---

FEW-SHOT EXAMPLE (Verdict: NO — the formalization is fine for this category)
[Natural language]
Verify that there is no magic square of order 2.

[Lean]
theorem brualdi_ch1_10 : ¬∃ (M : Matrix (Fin 2) (Fin 2) ℕ), IsMagicSquare M := by sorry

{"Verdict": "NO", "Explanation": "A 2×2 magic square is naturally modeled by a matrix indexed by Fin 2 with natural entries. The Lean statement uses the right carrier and domain, so there is no domain mismatch.", "DetailTags": [], "NeedsReview": "NO"}

---

Input:
[Natural language]
{{PROBLEM_NL}}

[Lean]
{{LEAN_CODE}}

Return JSON only.
```

---

## Prompt 5 — definition_mismatch

```text
CATEGORY: definition_mismatch

Definition: Lean objects don't represent the intended math notion (wrong operator, wrong constant, wrong library concept, misuse of API).

Allowed DetailTags: misuse_of_concept, wrong_operator, wrong_constant, library_usage_error, incorrect_function_choice, paper_vs_lean_semantics, encoding_issue, other

Boundary: Wrong type → domain_mismatch. Missing assumptions → specification_error.

---

FEW-SHOT EXAMPLE (Verdict: YES — the formal object is the wrong mathematical concept)
[Natural language]
Evaluate the integral ∫ cbrt(cos x) · sin^3(x) dx. The answer is
-(3/4) cos^(4/3)(x) + (3/10) cos^(10/3)(x) + C.

[Lean]
theorem integral_of_cube_root_cos_sin_cube (x : ℝ) :
  ∫ x in Set.Icc 0 x, (cos x)^(1/3 : ℝ) * (sin x)^3 =
    - (3/4) * (cos x)^(4/3 : ℝ) + (3/10) * (cos x)^(10/3 : ℝ) + C := by sorry

{"Verdict": "YES", "Explanation": "The NL asks for an indefinite integral, i.e. an antiderivative family with +C. The Lean statement instead uses a definite interval integral and also leaves C free, so it formalizes the wrong concept.", "DetailTags": ["misuse_of_concept"], "NeedsReview": "NO"}

---

FEW-SHOT EXAMPLE (Verdict: NO — the formalization is fine for this category)
[Natural language]
Prove that -(-v) = v for every v ∈ V.

[Lean]
theorem exercise_1_3 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {v : V} : -(-v) = v := by sorry

{"Verdict": "NO", "Explanation": "Lean's negation here is exactly the additive inverse from the NL statement, and the theorem states the intended identity directly. There is no definition mismatch.", "DetailTags": [], "NeedsReview": "NO"}

---

Input:
[Natural language]
{{PROBLEM_NL}}

[Lean]
{{LEAN_CODE}}

Return JSON only.
```

---

## Prompt 6 — quantifier_indexing_mismatch

```text
CATEGORY: quantifier_indexing_mismatch

Definition: Bug in quantifiers, bounds, indexing, or variable scope (off-by-one, wrong range, free vs bound variable).

Allowed DetailTags: quantifier_mismatch, indexing_mismatch, bound_mismatch, variable_mismatch, other

Boundary: Connective issues (∧ vs →) → formalization_error. Missing constraints → specification_error. Wrong types → domain_mismatch.

---

FEW-SHOT EXAMPLE (Verdict: YES — the summation range is off by one)
[Natural language]
The sum ∑_k binom(n, floor(k/2)) x^k is equal to (1 + x)(1 + x^2)^n.

[Lean]
theorem binomial_sum_equiv_product (n : ℕ) (x : ℝ) :
  ∑ k in range (2 * n + 1), (Nat.choose n (k / 2)) * x ^ k = (1 + x) * (1 + x ^ 2) ^ n := by sorry

{"Verdict": "YES", "Explanation": "The right-hand side has degree 2n + 1, so the intended sum includes the k = 2n + 1 term. Lean uses range (2 * n + 1), which runs only from k = 0 to 2n, so the indexing is off by one.", "DetailTags": ["indexing_mismatch"], "NeedsReview": "NO"}

---

FEW-SHOT EXAMPLE (Verdict: NO — the formalization is fine for this category)
[Natural language]
Let n be the smallest positive integer satisfying
n ≡ 2 (mod 3), n ≡ 3 (mod 5), and n ≡ 1 (mod 7).
Then n = 8.

[Lean]
theorem smallest_positive_integer :
  (∃ n : ℕ+, congruence1 n ∧ congruence2 n ∧ congruence3 n) ∧
  (∀ n : ℕ+, congruence1 n ∧ congruence2 n ∧ congruence3 n → n ≥ 8) ∧
  (congruence1 8 ∧ congruence2 8 ∧ congruence3 8) := by sorry

{"Verdict": "NO", "Explanation": "The quantifiers correctly express existence of a positive solution, minimality over all positive solutions, and verification that 8 satisfies the congruences. There is no quantifier or indexing mismatch here.", "DetailTags": [], "NeedsReview": "NO"}

---

Input:
[Natural language]
{{PROBLEM_NL}}

[Lean]
{{LEAN_CODE}}

Return JSON only.
```
