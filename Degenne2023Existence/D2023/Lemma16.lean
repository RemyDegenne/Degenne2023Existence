/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Setting

/-!
# Lemma 16 of [D23]: no algorithm beats static proportions in Gaussian half-space identification

For Gaussian arms and the half-space task, every fixed-budget algorithm family has maximal
difficulty ratio at least `1` to the static-proportions difficulty: no adaptive algorithm has a
better rate than the static proportions oracle on every model.

## Main statements

* `Degenne2023Existence.one_le_iInf_maxRatio_halfSpaceTask_gaussian`: [D23, Lemma 16].

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning LMLExplore.Identification

open scoped ENNReal NNReal

namespace Degenne2023Existence

variable {α : Type*} [Fintype α] {mα : MeasurableSpace α} [MeasurableSingletonClass α]

/-- **No algorithm beats static proportions in Gaussian half-space identification**
[D23, Lemma 16]. For Gaussian arms with variances `v a ≠ 0` and the half-space task with normal
vector `u ≠ 0`, the infimum over the fixed-budget algorithm families of the maximal difficulty
ratio to the static-proportions difficulty is at least `1`. -/
theorem one_le_iInf_maxRatio_halfSpaceTask_gaussian (ν : (α → ℝ) → Kernel α ℝ)
    [∀ μ, IsMarkovKernel (ν μ)] {v : α → ℝ≥0} (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) {u : α → ℝ} (hu : u ≠ 0) :
    1 ≤ ⨅ (𝒜 : ℕ → IdentAlg Unit α ℝ Bool) (_ : IsFixedBudgetFamily 𝒜),
      (halfSpaceTask ν id u).maxRatio (halfSpaceTask ν id u).staticDifficulty 𝒜 := by
  sorry

end Degenne2023Existence
