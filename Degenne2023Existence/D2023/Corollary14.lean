/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Setting

/-!
# Corollary 14 of [D23]: the liminf of the maximal difficulty ratio over all models

With `Alt_x(μ) = Alt(μ) ∩ {λ | H(λ) ≤ x}`, every consistent algorithm family satisfies
`(liminf_T sup_{λ ∈ 𝒟} R_{H,T}(𝒜, λ))⁻¹` is at most
`liminf_{x → ∞} inf_{μ ∈ 𝒟} max_{w ∈ Δ_K} inf_{λ ∈ Alt_x(μ)} H(λ) ∑ a, w a KL(ν_a(μ), ν_a(λ))`.

## Main statements

* `Degenne2023Existence.inv_liminf_iSup_difficultyRatio_le_liminf`: [D23, Corollary 14].

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
-/

@[expose] public section

open MeasureTheory Filter Topology Learning LMLExplore LMLExplore.Identification

open scoped ENNReal

namespace Degenne2023Existence

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {m𝓨 : MeasurableSpace 𝓨} [MeasurableSpace.CountablyGenerated 𝓨]
  {mℐ : MeasurableSpace ℐ}

/-- **Lower bound on the liminf of the maximal difficulty ratio** [D23, Corollary 14]. Let `𝒜` be
a consistent fixed-budget algorithm family and `H` a difficulty function that is positive on the
admissible models. With `Alt_x(μ)` the alternatives `λ` to `μ` with `H(λ) ≤ x`,
`(liminf_T sup_{λ ∈ 𝒟} R_{H,T}(𝒜, λ))⁻¹` is at most
`liminf_{x → ∞} inf_{μ ∈ 𝒟} max_{w ∈ Δ_K} inf_{λ ∈ Alt_x(μ)} H(λ) ∑ a, w a KL(ν_a(μ), ν_a(λ))`.

`H(λ) ≠ 0` is the positivity of the paper's `H : 𝒟 → ℝ⁺`. -/
theorem inv_liminf_iSup_difficultyRatio_le_liminf (task : IdentTask α Θ ℐ 𝓨) (H : Θ → ℝ≥0∞)
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} (h𝒜 : IsFixedBudgetFamily 𝒜) (hcons : task.IsConsistent 𝒜)
    (hH₀ : ∀ μ' ∈ task.M, H μ' ≠ 0) :
    (liminf (fun T ↦ ⨆ μ' ∈ task.M, task.difficultyRatio H 𝒜 μ' T) atTop)⁻¹ ≤
      liminf (fun x : ℝ ↦ ⨅ μ ∈ task.M, ⨆ w ∈ simplex α,
        ⨅ μ' ∈ {μ' | μ' ∈ task.alternatives μ ∧ H μ' ≤ ENNReal.ofReal x},
          H μ' * task.cost w μ μ') atTop := by
  sorry

end Degenne2023Existence
