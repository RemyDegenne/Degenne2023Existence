/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Lemma15
public import Degenne2023Existence.D2023.Theorem3

/-!
# Lemma 16 of [D23]: no algorithm beats static proportions in Gaussian half-space identification

For Gaussian arms and the half-space task, every fixed-budget algorithm family has maximal
difficulty ratio at least `1` to the static-proportions difficulty: no adaptive algorithm has a
better rate than the static proportions oracle on every model.

The proof applies Theorem 3 at the model `u`, over all its alternatives, with the bound
`max_w inf_{λ ∈ Alt(u)} H^{sp}(λ) ∑ a, w a KL(ν_a(u), ν_a(λ)) ≤ 1` of
`LMLExplore.Identification.iSup_iInf_staticDifficulty_mul_cost_halfSpaceTask_le_one`; a family
whose probability of error at `u` does not tend to `0` has an infinite ratio there. The paper
applies the second part of Theorem 3, which needs consistency at every model; one model suffices.

## Main statements

* `Degenne2023Existence.one_le_iInf_maxRatio_halfSpaceTask_gaussian`: [D23, Lemma 16].

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Learning LMLExplore.Identification

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
  set task := halfSpaceTask ν id u
  have hH (μ : α → ℝ) (hμ : μ ∈ task.M) : task.staticDifficulty μ =
      ENNReal.ofReal (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2 / (u ⬝ᵥ μ) ^ 2) :=
    staticDifficulty_halfSpaceTask_gaussianReal ν hv hν hu (by simpa [task] using hμ)
  have hL := sum_abs_mul_sqrt_pos hv hu
  have hu0 : u ⬝ᵥ u ≠ 0 := by simpa [dotProduct_self_eq_zero] using hu
  have huM : u ∈ task.M := by simpa [task] using hu0
  refine le_iInf₂ fun 𝒜 h𝒜 ↦ ?_
  by_cases hp : Tendsto (task.errorProb 𝒜 u) atTop (𝓝 0)
  · -- Theorem 3 at the model `u`, over its alternatives.
    have h3 := inv_iSup_asymptoticRatio_le task task.staticDifficulty h𝒜 hp
      (D := task.alternatives u) (fun μ' h ↦ h.2)
      (fun μ' h ↦ by
        have : u ⬝ᵥ μ' ≠ 0 := by simpa [task] using h.1
        rw [hH μ' h.1]
        exact (ENNReal.ofReal_pos.2 (by positivity)).ne')
      (fun μ' h ↦ by rw [hH μ' h.1]; exact ENNReal.ofReal_ne_top)
    have h1 : 1 ≤ ⨆ μ' ∈ task.alternatives u, task.asymptoticRatio task.staticDifficulty 𝒜 μ' := by
      rw [← ENNReal.inv_le_one]
      exact h3.trans (iSup_iInf_staticDifficulty_mul_cost_halfSpaceTask_le_one ν hv hν hu hu0)
    exact h1.trans (iSup₂_mono' fun μ' h ↦ ⟨μ', h.1, le_rfl⟩)
  · -- A family whose probability of error at `u` does not tend to `0` has an infinite ratio.
    have htop := task.asymptoticRatio_eq_top (H := task.staticDifficulty)
      (by rw [hH u huM]; exact ENNReal.ofReal_ne_top) hp
    rw [IdentTask.maxRatio]
    exact le_iSup₂_of_le (f := fun μ _ ↦ task.asymptoticRatio task.staticDifficulty 𝒜 μ) u huM
      (by rw [htop]; exact le_top)

end Degenne2023Existence
