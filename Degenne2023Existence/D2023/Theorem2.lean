/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Setting

/-!
# Theorem 2 of [D23]: a non-asymptotic lower bound on the difficulty ratio

For every difficulty function `H`, every two models `μ` and `λ` without a common correct answer
and every algorithm with budget `T` with `H(λ) ≤ √T`,
`R_{H,T}(𝒜, λ)⁻¹ (1 - p_{μ,T}(𝒜)) - log 2 / √T ≤ H(λ) ∑ a, E_μ[N_{T,a} / T] KL(ν_a(μ), ν_a(λ))`.

## Main statements

* `Degenne2023Existence.inv_difficultyRatio_mul_le`: [D23, Theorem 2].

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
-/

@[expose] public section

open MeasureTheory InformationTheory Learning LMLExplore.Identification

open scoped ENNReal

namespace Degenne2023Existence

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {m𝓨 : MeasurableSpace 𝓨} [MeasurableSpace.CountablyGenerated 𝓨]
  {mℐ : MeasurableSpace ℐ}

/-- **Non-asymptotic lower bound on the difficulty ratio** [D23, Theorem 2]. Let `H` be a
difficulty function, `𝒜` an algorithm family whose algorithm `𝒜 T` stops after `T` rounds, and
`μ`, `λ` two models without a common correct answer, with `0 < H(λ) ≤ √T`. Then
`R_{H,T}(𝒜, λ)⁻¹ (1 - p_{μ,T}(𝒜)) ≤ H(λ) ∑ a, E_μ[N_{T,a} / T] KL(ν_a(μ), ν_a(λ)) + log 2 / √T`,
where `N_{T,a}` is the number of pulls of the arm `a` in the first `T` rounds.

The paper writes the term `log 2 / √T` on the left with a minus sign, which is the same in real
numbers; here the quantities are in `ℝ≥0∞`. The paper's `μ, λ ∈ 𝒟` and `i*(λ) ≠ i*(μ)` are
replaced by the disjointness of the correct answers of `μ` and `λ`, and `H(λ) ≠ 0` is the
positivity of the paper's `H : 𝒟 → ℝ⁺`. -/
theorem inv_difficultyRatio_mul_le (task : IdentTask α Θ ℐ 𝓨) (H : Θ → ℝ≥0∞)
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} {T : ℕ} (h𝒜 : IsFixedBudget (𝒜 T) T) {μ μ' : Θ}
    (hμμ' : Disjoint (task.correct μ) (task.correct μ')) (hH₀ : H μ' ≠ 0)
    (hH : H μ' ≤ ENNReal.ofReal √T) :
    (task.difficultyRatio H 𝒜 μ' T)⁻¹ * (1 - task.errorProb 𝒜 μ T) ≤
      H μ' * ∑ a, (∫⁻ ω, (pullCount IT.action a T ω : ℝ≥0∞)
          ∂(trajMeasure (𝒜 T).alg (Environment.bandit (task.ν μ)))) / T *
          klDiv (task.ν μ a) (task.ν μ' a) +
        ENNReal.ofReal (Real.log 2 / √T) := by
  sorry

end Degenne2023Existence
