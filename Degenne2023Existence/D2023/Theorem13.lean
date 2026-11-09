/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Theorem2

/-!
# Theorem 13 of [D23]: a lower bound on the liminf of the maximal difficulty ratio

For an algorithm family whose probability of error at `μ` tends to `0` and a set `D(μ)` of
alternatives to `μ` on which the difficulty function is bounded,
`(liminf_T sup_{λ ∈ D(μ)} R_{H,T}(𝒜, λ))⁻¹` is at most
`max_{w ∈ Δ_K} inf_{λ ∈ D(μ)} H(λ) ∑ a, w a KL(ν_a(μ), ν_a(λ))`.

Since `H` is bounded on `D(μ)`, Theorem 2 applies to every `λ ∈ D(μ)` at once for large budgets,
with the expected proportions of pulls at `μ`, which lie in the simplex: no subsequence is needed.

## Main statements

* `Degenne2023Existence.inv_liminf_iSup_difficultyRatio_le`: [D23, Theorem 13].

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

/-- **Lower bound on the liminf of the maximal difficulty ratio over a set of alternatives**
[D23, Theorem 13]. Let `𝒜` be a fixed-budget algorithm family whose probability of error at the
model `μ` tends to `0`, and `D` a set of models without a common correct answer with `μ`, on which
the difficulty function `H` is positive and bounded. Then
`(liminf_T sup_{λ ∈ D} R_{H,T}(𝒜, λ))⁻¹` is at most
`max_{w ∈ Δ_K} inf_{λ ∈ D} H(λ) ∑ a, w a KL(ν_a(μ), ν_a(λ))`.

The paper's `μ ∈ 𝒟` and `D ⊆ Alt(μ)` are replaced by the disjointness of the correct answers, and
`H(λ) ≠ 0` is the positivity of the paper's `H : 𝒟 → ℝ⁺`. -/
theorem inv_liminf_iSup_difficultyRatio_le (task : IdentTask α Θ ℐ 𝓨) (H : Θ → ℝ≥0∞)
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} (h𝒜 : IsFixedBudgetFamily 𝒜) {μ : Θ}
    (hμ : Tendsto (task.errorProb 𝒜 μ) atTop (𝓝 0)) {D : Set Θ}
    (hD : ∀ μ' ∈ D, Disjoint (task.correct μ) (task.correct μ')) (hH₀ : ∀ μ' ∈ D, H μ' ≠ 0)
    (hH : ⨆ μ' ∈ D, H μ' ≠ ∞) :
    (liminf (fun T ↦ ⨆ μ' ∈ D, task.difficultyRatio H 𝒜 μ' T) atTop)⁻¹ ≤
      ⨆ w ∈ simplex α, ⨅ μ' ∈ D, H μ' * task.cost w μ μ' := by
  classical
  set V := ⨆ w ∈ simplex α, ⨅ μ' ∈ D, H μ' * task.cost w μ μ'
  -- `(liminf_T sup_{λ ∈ D} R_{H,T})⁻¹ = limsup_T inf_{λ ∈ D} R_{H,T}⁻¹`.
  rw [ENNReal.inv_liminf]
  simp_rw [ENNReal.inv_iSup]
  refine ENNReal.le_of_forall_lt_one_mul_le fun c hc ↦ ?_
  rw [← ENNReal.limsup_const_mul_of_ne_top (ne_top_of_lt hc)]
  have hlim : Tendsto (fun T : ℕ ↦ V + ENNReal.ofReal (Real.log 2 / √T)) atTop (𝓝 V) := by
    simpa using tendsto_const_nhds.add tendsto_ofReal_log_two_div_sqrt
  refine (limsup_le_limsup ?_).trans_eq hlim.limsup_eq
  filter_upwards [eventually_mul_inv_difficultyRatio_le task H h𝒜 hμ hc hH] with T ⟨hw, hT⟩
  calc c * ⨅ μ' ∈ D, (task.difficultyRatio H 𝒜 μ' T)⁻¹
      ≤ ⨅ μ' ∈ D, c * (task.difficultyRatio H 𝒜 μ' T)⁻¹ :=
        le_iInf₂ fun μ' hμ' ↦ by gcongr; exact iInf₂_le μ' hμ'
    _ ≤ ⨅ μ' ∈ D, (H μ' * task.cost (expectedPullProportion (𝒜 T)
          (Environment.bandit (task.ν μ))) μ μ' + ENNReal.ofReal (Real.log 2 / √T)) :=
        iInf₂_mono fun μ' hμ' ↦ hT μ' (hD μ' hμ') (hH₀ μ' hμ')
          (le_iSup₂ (f := fun μ' _ ↦ H μ') μ' hμ')
    _ = (⨅ μ' ∈ D, H μ' * task.cost (expectedPullProportion (𝒜 T)
          (Environment.bandit (task.ν μ))) μ μ') + ENNReal.ofReal (Real.log 2 / √T) := by
        simp only [ENNReal.iInf_add]
    _ ≤ V + ENNReal.ofReal (Real.log 2 / √T) := by
        gcongr
        exact le_iSup₂ (f := fun w _ ↦ ⨅ μ' ∈ D, H μ' * task.cost w μ μ') _ hw

end Degenne2023Existence
