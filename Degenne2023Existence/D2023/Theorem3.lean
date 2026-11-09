/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Setting

/-!
# Theorem 3 of [D23]: asymptotic lower bounds on the difficulty ratio

For a consistent algorithm family `𝒜`, a model `μ` and a set `D(μ)` of alternatives to `μ`,
`(sup_{λ ∈ D(μ)} R_{H,∞}(𝒜, λ))⁻¹ ≤ max_{w ∈ Δ_K} inf_{λ ∈ D(μ)} H(λ) ∑ a, w a KL(ν_a(μ), ν_a(λ))`,
and over all the admissible models,
`(sup_{λ ∈ 𝒟} R_{H,∞}(𝒜, λ))⁻¹` is at most
`inf_{μ ∈ 𝒟} max_{w ∈ Δ_K} inf_{λ ∈ Alt(μ)} H(λ) ∑ a, w a KL(ν_a(μ), ν_a(λ))`.
The weighted sum `∑ a, w a KL(ν_a(μ), ν_a(λ))` is the transportation cost `task.cost w μ λ`.

## Main statements

* `Degenne2023Existence.inv_iSup_asymptoticRatio_le`: [D23, Theorem 3], first inequality.
* `Degenne2023Existence.inv_maxRatio_le`: [D23, Theorem 3], second inequality.

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

/-- **Asymptotic lower bound on the difficulty ratio over a set of alternatives**
[D23, Theorem 3]. Let `𝒜` be a fixed-budget algorithm family whose probability of error at the
model `μ` tends to `0`, and `D` a set of models without a common correct answer with `μ`, on which
the difficulty function `H` is positive and finite. Then
`(sup_{λ ∈ D} R_{H,∞}(𝒜, λ))⁻¹ ≤ max_{w ∈ Δ_K} inf_{λ ∈ D} H(λ) ∑ a, w a KL(ν_a(μ), ν_a(λ))`.

The paper assumes `𝒜` consistent, `μ ∈ 𝒟` and `D ⊆ Alt(μ)`; the proof uses only the convergence
to `0` of the probability of error at `μ` and the disjointness of the correct answers. -/
theorem inv_iSup_asymptoticRatio_le (task : IdentTask α Θ ℐ 𝓨) (H : Θ → ℝ≥0∞)
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} (h𝒜 : IsFixedBudgetFamily 𝒜) {μ : Θ}
    (hμ : Tendsto (task.errorProb 𝒜 μ) atTop (𝓝 0)) {D : Set Θ}
    (hD : ∀ μ' ∈ D, Disjoint (task.correct μ) (task.correct μ')) (hH₀ : ∀ μ' ∈ D, H μ' ≠ 0)
    (hH : ∀ μ' ∈ D, H μ' ≠ ∞) :
    (⨆ μ' ∈ D, task.asymptoticRatio H 𝒜 μ')⁻¹ ≤
      ⨆ w ∈ simplex α, ⨅ μ' ∈ D, H μ' * task.cost w μ μ' := by
  sorry

/-- **Asymptotic lower bound on the maximal difficulty ratio** [D23, Theorem 3]. Let `𝒜` be a
consistent fixed-budget algorithm family and `H` a difficulty function that is positive and
finite on the admissible models. Then
`(sup_{λ ∈ 𝒟} R_{H,∞}(𝒜, λ))⁻¹` is at most
`inf_{μ ∈ 𝒟} max_{w ∈ Δ_K} inf_{λ ∈ Alt(μ)} H(λ) ∑ a, w a KL(ν_a(μ), ν_a(λ))`.
This recovers Theorem 1 of Komiyama et al. (2022). -/
theorem inv_maxRatio_le (task : IdentTask α Θ ℐ 𝓨) (H : Θ → ℝ≥0∞)
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} (h𝒜 : IsFixedBudgetFamily 𝒜) (hcons : task.IsConsistent 𝒜)
    (hH₀ : ∀ μ' ∈ task.M, H μ' ≠ 0) (hH : ∀ μ' ∈ task.M, H μ' ≠ ∞) :
    (task.maxRatio H 𝒜)⁻¹ ≤
      ⨅ μ ∈ task.M, ⨆ w ∈ simplex α, ⨅ μ' ∈ task.alternatives μ, H μ' * task.cost w μ μ' := by
  sorry

end Degenne2023Existence
