/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Theorem2

/-!
# Theorem 3 of [D23]: asymptotic lower bounds on the difficulty ratio

For a consistent algorithm family `𝒜`, a model `μ` and a set `D(μ)` of alternatives to `μ`,
`(sup_{λ ∈ D(μ)} R_{H,∞}(𝒜, λ))⁻¹ ≤ max_{w ∈ Δ_K} inf_{λ ∈ D(μ)} H(λ) ∑ a, w a KL(ν_a(μ), ν_a(λ))`,
and over all the admissible models,
`(sup_{λ ∈ 𝒟} R_{H,∞}(𝒜, λ))⁻¹` is at most
`inf_{μ ∈ 𝒟} max_{w ∈ Δ_K} inf_{λ ∈ Alt(μ)} H(λ) ∑ a, w a KL(ν_a(μ), ν_a(λ))`.
The weighted sum `∑ a, w a KL(ν_a(μ), ν_a(λ))` is the transportation cost `task.cost w μ λ`.

The proof takes a subsequence of budgets along which the expected proportions of pulls at `μ`
converge, to some `w₀`, and applies Theorem 2 along it. The transportation cost is continuous in
the allocation at the alternatives at finite divergences from `μ`; at the others, it is infinite
for every positive allocation. The allocation `c w₀ + (1 - c) (1/K, …, 1/K)`, for `c < 1`, handles
both cases at once.

## Main statements

* `Degenne2023Existence.inv_iSup_asymptoticRatio_le`: [D23, Theorem 3], first inequality.
* `Degenne2023Existence.inv_maxRatio_le`: [D23, Theorem 3], second inequality.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
-/

@[expose] public section

open MeasureTheory Filter Topology InformationTheory Learning LMLExplore LMLExplore.Identification

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
  classical
  -- A subsequence `ψ` of budgets along which the expected proportions `w T` converge to `w₀`.
  set w : ℕ → α → ℝ := fun T ↦ expectedPullProportion (𝒜 T) (Environment.bandit (task.ν μ))
  obtain ⟨w₀, hw₀, φ, hφ, hlim⟩ := (isCompact_simplex α).tendsto_subseq
    (x := fun n ↦ w (n + 1)) (fun n ↦ (h𝒜 _).expectedPullProportion_mem_simplex n.succ_ne_zero _)
  set ψ : ℕ → ℕ := fun n ↦ φ n + 1
  have hψ : Tendsto ψ atTop atTop := (tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop
  -- The bound at an alternative at finite divergences from `μ`, along the subsequence.
  have key (μ' : Θ) (hμ' : μ' ∈ D) (hfin : ∀ a, klDiv (task.ν μ a) (task.ν μ' a) ≠ ∞) :
      liminf (fun T ↦ (task.difficultyRatio H 𝒜 μ' T)⁻¹) atTop ≤ H μ' * task.cost w₀ μ μ' := by
    refine hψ.liminf_le_liminf_comp.trans (ENNReal.le_of_forall_lt_one_mul_le fun c hc ↦ ?_)
    have hcost : Tendsto (fun n ↦ H μ' * task.cost (w (ψ n)) μ μ' +
        ENNReal.ofReal (Real.log 2 / √(ψ n))) atTop (𝓝 (H μ' * task.cost w₀ μ μ')) := by
      rw [← add_zero (H μ' * task.cost w₀ μ μ')]
      refine Tendsto.add (ENNReal.Tendsto.const_mul ?_ (Or.inr (hH μ' hμ')))
        (tendsto_ofReal_log_two_div_sqrt.comp hψ)
      simp_rw [IdentTask.cost_def]
      refine tendsto_finsetSum _ fun a _ ↦ ENNReal.Tendsto.mul_const ?_ (Or.inr (hfin a))
      exact ENNReal.tendsto_ofReal (((continuous_apply a).tendsto w₀).comp hlim)
    calc c * liminf ((fun T ↦ (task.difficultyRatio H 𝒜 μ' T)⁻¹) ∘ ψ) atTop
        ≤ c * limsup ((fun T ↦ (task.difficultyRatio H 𝒜 μ' T)⁻¹) ∘ ψ) atTop := by
          gcongr
          exact liminf_le_limsup
      _ = limsup (fun n ↦ c * (task.difficultyRatio H 𝒜 μ' (ψ n))⁻¹) atTop :=
          (ENNReal.limsup_const_mul_of_ne_top (ne_top_of_lt hc)).symm
      _ ≤ H μ' * task.cost w₀ μ μ' := by
          refine (limsup_le_limsup ?_).trans_eq hcost.limsup_eq
          filter_upwards [hψ.eventually (eventually_mul_inv_difficultyRatio_le task H h𝒜 hμ hc
            (hH μ' hμ'))] with n hn
          exact hn.2 μ' (hD μ' hμ') (hH₀ μ' hμ') le_rfl
  -- `(sup_{λ ∈ D} R_{H,∞}(𝒜, λ))⁻¹ = inf_{λ ∈ D} liminf_T R_{H,T}(𝒜, λ)⁻¹`.
  simp_rw [ENNReal.inv_iSup, IdentTask.asymptoticRatio, ENNReal.inv_limsup]
  refine ENNReal.le_of_forall_lt_one_mul_le fun c hc ↦ ?_
  have : Nonempty α := nonempty_of_mem_simplex hw₀
  have hc1 : c.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hc.ne_top ENNReal.one_ne_top).2 hc
  -- Mix the limit proportions with the uniform allocation.
  set v : α → ℝ := c.toReal • w₀ + (1 - c.toReal) • fun _ ↦ (Fintype.card α : ℝ)⁻¹
  have hv : v ∈ simplex α := convex_simplex α hw₀ (uniform_mem_simplex α) ENNReal.toReal_nonneg
    (by linarith) (by ring)
  refine le_iSup₂_of_le (f := fun w _ ↦ ⨅ μ' ∈ D, H μ' * task.cost w μ μ') v hv ?_
  calc c * ⨅ μ' ∈ D, liminf (fun T ↦ (task.difficultyRatio H 𝒜 μ' T)⁻¹) atTop
      ≤ ⨅ μ' ∈ D, c * liminf (fun T ↦ (task.difficultyRatio H 𝒜 μ' T)⁻¹) atTop :=
        le_iInf₂ fun μ' hμ' ↦ by gcongr; exact iInf₂_le μ' hμ'
    _ ≤ ⨅ μ' ∈ D, H μ' * task.cost v μ μ' := iInf₂_mono fun μ' hμ' ↦ ?_
  by_cases hfin : ∀ a, klDiv (task.ν μ a) (task.ν μ' a) ≠ ∞
  · -- At finite divergences, `c cost(w₀, μ, λ) ≤ cost(v, μ, λ)`.
    calc c * liminf (fun T ↦ (task.difficultyRatio H 𝒜 μ' T)⁻¹) atTop
        ≤ c * (H μ' * task.cost w₀ μ μ') := by gcongr; exact key μ' hμ' hfin
      _ = H μ' * (c * task.cost w₀ μ μ') := mul_left_comm _ _ _
      _ ≤ H μ' * task.cost v μ μ' := by
          gcongr
          rw [IdentTask.cost_def, IdentTask.cost_def, Finset.mul_sum]
          refine Finset.sum_le_sum fun a _ ↦ ?_
          rw [← mul_assoc, ← ENNReal.ofReal_toReal hc.ne_top,
            ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
          gcongr
          simp only [v, Pi.add_apply, Pi.smul_apply, smul_eq_mul, le_add_iff_nonneg_right]
          exact mul_nonneg (by linarith) (by positivity)
  · -- At an infinite divergence on the arm `a`, `v a > 0` makes the cost infinite.
    push Not at hfin
    obtain ⟨a, ha⟩ := hfin
    have hva : 0 < v a := by
      simp only [v, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := (mem_simplex_iff.1 hw₀).1 a
      have : 0 < (1 - c.toReal) * (Fintype.card α : ℝ)⁻¹ := mul_pos (by linarith) (by positivity)
      positivity
    rw [task.cost_eq_top_of_klDiv_eq_top hva ha, ENNReal.mul_top (hH₀ μ' hμ')]
    exact le_top

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
  refine le_iInf₂ fun μ hμ ↦ le_trans ?_ (inv_iSup_asymptoticRatio_le task H h𝒜 (hcons μ hμ)
    (fun μ' h ↦ h.2) (fun μ' h ↦ hH₀ μ' h.1) (fun μ' h ↦ hH μ' h.1))
  rw [ENNReal.inv_le_inv, IdentTask.maxRatio]
  exact iSup₂_mono' fun μ' h ↦ ⟨μ', h.1, le_rfl⟩

end Degenne2023Existence
