/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Setting

/-!
# Theorem 7 of [D23]: tasks with a flat boundary

If, in a ball around a vector of means `η`, the task has exactly two answers, separated by a
hyperplane through `η`, then for Gaussian arms with known variances every fixed-budget algorithm
family has maximal difficulty ratio at least `1` to the static-proportions difficulty. This
applies to best arm identification, thresholding and positivity.

The paper writes `H_{𝒞^{sp}}` for the oracle difficulty of the class of static proportions
algorithms, equal to the static-proportions difficulty by Theorem 1, and uses a Euclidean ball;
since balls for the different norms of `α → ℝ` contain each other, the hypothesis is the same for
the ball of the sup norm used here. Lemmas 17 and 18 of the paper's proof are misprinted, and the
proof of Lemma 18 uses a value of `H^{sp}` near `η` that Lemma 17 does not give (errata E4 and E5
of `notes/paper-errata.md`).

## Main statements

* `Degenne2023Existence.one_le_iInf_maxRatio_of_hyperplane`: [D23, Theorem 7].

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning LMLExplore.Identification

open scoped ENNReal NNReal

namespace Degenne2023Existence

variable {α ℐ : Type*} [Fintype α] {mα : MeasurableSpace α} [MeasurableSingletonClass α]
  [MeasurableSpace ℐ]

/-- **Tasks with a flat boundary** [D23, Theorem 7]. Let the arm `a` of the model `μ` have the
Gaussian law of mean `μ a` and variance `v a ≠ 0`. Suppose that in the ball of center `η` and
radius `r > 0`, the admissible models are the vectors off the hyperplane through `η` orthogonal to
`u ≠ 0`, with the single correct answer `i` on one side and `j ≠ i` on the other. Then the infimum
over the fixed-budget algorithm families of the maximal difficulty ratio to the static-proportions
difficulty is at least `1`.

The paper also assumes Assumption 1, which the statement does not need. -/
theorem one_le_iInf_maxRatio_of_hyperplane {task : IdentTask α (α → ℝ) ℐ ℝ} {v : α → ℝ≥0}
    (hv : ∀ a, v a ≠ 0) (hν : ∀ μ a, task.ν μ a = gaussianReal (μ a) (v a)) {η u : α → ℝ}
    (hu : u ≠ 0) {r : ℝ} (hr : 0 < r) {i j : ℐ} (hij : i ≠ j)
    (hball : ∀ μ ∈ Metric.ball η r, (μ ∈ task.M ↔ u ⬝ᵥ (μ - η) ≠ 0) ∧
      (u ⬝ᵥ (μ - η) < 0 → task.correct μ = {i}) ∧ (0 < u ⬝ᵥ (μ - η) → task.correct μ = {j})) :
    1 ≤ ⨅ (𝒜 : ℕ → IdentAlg Unit α ℝ ℐ) (_ : IsFixedBudgetFamily 𝒜),
      task.maxRatio task.staticDifficulty 𝒜 := by
  sorry

end Degenne2023Existence
