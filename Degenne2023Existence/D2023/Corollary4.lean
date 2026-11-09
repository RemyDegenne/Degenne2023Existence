/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Setting

/-!
# Corollary 4 of [D23]: the lower bound from alternatives along the coordinates

If the alternatives `λ⁽ʲ⁾` to `μ` each differ from `μ` only along the arm `j`, then every algorithm
family whose probability of error at `μ` tends to `0` satisfies
`sup_j R_{H,∞}(𝒜, λ⁽ʲ⁾) ≥ ∑_j 1 / (H(λ⁽ʲ⁾) KL(ν_j(μ), ν_j(λ⁽ʲ⁾)))`.

## Main statements

* `Degenne2023Existence.sum_inv_le_iSup_asymptoticRatio`: [D23, Corollary 4].

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
-/

@[expose] public section

open MeasureTheory Filter Topology InformationTheory Learning LMLExplore.Identification

open scoped ENNReal

namespace Degenne2023Existence

variable {α Θ ℐ 𝓨 : Type*} [Finite α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {m𝓨 : MeasurableSpace 𝓨} [MeasurableSpace.CountablyGenerated 𝓨]
  {mℐ : MeasurableSpace ℐ}

/-- **The lower bound from alternatives along the coordinates** [D23, Corollary 4]. Let `𝒜` be a
fixed-budget algorithm family whose probability of error at the model `μ` tends to `0`, `s` a set
of arms and, for every arm `j ∈ s`, `λ j` a model without a common correct answer with `μ`, whose
arms other than `j` have the same laws as those of `μ`, and at which the difficulty function `H` is
positive and finite. Then
`∑_{j ∈ s} 1 / (H(λ j) KL(ν_j(μ), ν_j(λ j))) ≤ sup_{j ∈ s} R_{H,∞}(𝒜, λ j)`.

The paper takes `s` to be all the arms, but applies the corollary to the arms `2, …, K` in the
proof of Theorem 8; it assumes `lim_T p_{μ,T}(𝒜) = 0` and the finiteness of `H` as in Theorem 3. -/
theorem sum_inv_le_iSup_asymptoticRatio (task : IdentTask α Θ ℐ 𝓨) (H : Θ → ℝ≥0∞)
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} (h𝒜 : IsFixedBudgetFamily 𝒜) {μ : Θ}
    (hμ : Tendsto (task.errorProb 𝒜 μ) atTop (𝓝 0)) (s : Finset α) (μ' : α → Θ)
    (hdisj : ∀ j ∈ s, Disjoint (task.correct μ) (task.correct (μ' j)))
    (hν : ∀ j ∈ s, ∀ a ≠ j, task.ν (μ' j) a = task.ν μ a) (hH₀ : ∀ j ∈ s, H (μ' j) ≠ 0)
    (hH : ∀ j ∈ s, H (μ' j) ≠ ∞) :
    ∑ j ∈ s, (H (μ' j) * klDiv (task.ν μ j) (task.ν (μ' j) j))⁻¹ ≤
      ⨆ j ∈ s, task.asymptoticRatio H 𝒜 (μ' j) := by
  sorry

end Degenne2023Existence
