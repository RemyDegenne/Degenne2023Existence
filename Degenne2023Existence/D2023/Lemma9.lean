/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Setting
public import Degenne2023Existence.ForLMLExplore.Identification.Task.BestArmTwo
public import LMLExplore.Probability.Distributions.ExponentialFamily.Bernoulli
public import TauCeti.Analysis.SpecialFunctions.Sigmoid

/-!
# Lemma 9 of [D23]: the static-proportions difficulty of two Bernoulli arms

For best arm identification with two Bernoulli arms of means `μ₀ ≠ μ₁` in `(0, 1)`,
`H^{sp}(μ)⁻¹ = kl(z, μ₀) = kl(z, μ₁)` with
`z = log ((1 - μ₁) / (1 - μ₀)) / log (μ₀ (1 - μ₁) / ((1 - μ₀) μ₁))`, the Chernoff information of
the two Bernoulli laws. The arms are `0` and `1` (the paper's `1` and `2`), and the task is best
arm identification on the Bernoulli bandits with means in `(0, 1)`.

## Main statements

* `Degenne2023Existence.inv_staticDifficulty_baiTask_bernoulli_two`: [D23, Lemma 9].

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory LMLExplore LMLExplore.Identification

open scoped ENNReal

namespace Degenne2023Existence

/-- **The static-proportions difficulty of two Bernoulli arms** [D23, Lemma 9]. For best arm
identification on the Bernoulli bandits with two arms and means in `(0, 1)`, and a vector of means
`μ` with `μ 0 ≠ μ 1`, `H^{sp}(μ)⁻¹ = kl(z, μ 0) = kl(z, μ 1)` with
`z = log ((1 - μ 1) / (1 - μ 0)) / log (μ 0 (1 - μ 1) / ((1 - μ 0) μ 1))`. -/
theorem inv_staticDifficulty_baiTask_bernoulli_two {μ : Fin 2 → ℝ}
    (hμ : ∀ a, μ a ∈ Set.Ioo 0 1) (hμ01 : μ 0 ≠ μ 1) {z : ℝ}
    (hz : z = Real.log ((1 - μ 1) / (1 - μ 0)) / Real.log (μ 0 * (1 - μ 1) / ((1 - μ 0) * μ 1))) :
    (((baiTask (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦
        Set.projIcc 0 1 zero_le_one (μ c)) id).restrict
          {μ | ∀ c, μ c ∈ Set.Ioo 0 1}).staticDifficulty μ)⁻¹ = klBer z (μ 0) ∧
      (((baiTask (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦
        Set.projIcc 0 1 zero_le_one (μ c)) id).restrict
          {μ | ∀ c, μ c ∈ Set.Ioo 0 1}).staticDifficulty μ)⁻¹ = klBer z (μ 1) := by
  -- the Bernoulli laws of means in `(0, 1)` are the exponential family of `Ber(1/2)`
  set ρ := Ber((1 : ℝ), 0, unitInterval.sigmoid 0)
  have hmeans : ρ.expFamilyMeans id = Set.Ioo 0 1 := expFamilyMeans_bernoulliMeasure_sigmoid 0
  have hT : ∀ c, ¬ id =ᵐ[ρ] fun _ ↦ c := not_ae_eq_const_bernoulliMeasure
    (by simp only [unitInterval.coe_sigmoid, Real.sigmoid_zero]; norm_num)
  have hμ' : ∀ a, μ a ∈ ρ.expFamilyMeans id := by rwa [hmeans]
  have hη : ρ.natParam id (μ 0) ≠ ρ.natParam id (μ 1) :=
    (Measure.strictMonoOn_natParam hT).injOn.ne (hμ' 0) (hμ' 1) hμ01
  have h := inv_staticDifficulty_baiTask_two
    (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦ Set.projIcc 0 1 zero_le_one (μ c)) hT
    (fun μ a ha ↦ by
      rw [hmeans] at ha
      rw [Bandits.bernoulliBandit_apply, expFamily_natParam_bernoulliMeasure_sigmoid 0 ha,
        Set.projIcc_of_mem _ (Set.Ioo_subset_Icc_self ha)]) hμ' hμ01
  simp only [hmeans] at h
  -- the natural parameter of `m` is `log (m / (1 - m))`, and `ψ(η(m)) = log (1 / (2 (1 - m)))`
  have hξ (a : Fin 2) : ρ.natParam id (μ a) = Real.log (μ a / (1 - μ a)) := by
    have h_sig := Measure.deriv_cgf_natParam (hμ' a)
    rw [deriv_cgf_bernoulliMeasure_sigmoid, zero_add] at h_sig
    rw [← Real.log_sigmoid_div_one_sub (ρ.natParam id (μ a)), h_sig]
  have hψ (a : Fin 2) : cgf id ρ (ρ.natParam id (μ a)) = Real.log (1 / (2 * (1 - μ a))) := by
    have h1 : 0 < 1 - μ a := sub_pos.2 (hμ a).2
    rw [hξ, TauCeti.Probability.cgf_id_bernoulliMeasure, unitInterval.coe_sigmoid,
      Real.sigmoid_zero, Real.exp_log (div_pos (hμ a).1 h1)]
    congr 1
    field_simp
    ring
  have hx : (cgf id ρ (ρ.natParam id (μ 0)) - cgf id ρ (ρ.natParam id (μ 1))) /
      (ρ.natParam id (μ 0) - ρ.natParam id (μ 1)) = z := by
    have h0 : 0 < 1 - μ 0 := sub_pos.2 (hμ 0).2
    have h1 : 0 < 1 - μ 1 := sub_pos.2 (hμ 1).2
    rw [hψ, hψ, hξ, hξ, ← Real.log_div (by positivity) (by positivity),
      ← Real.log_div (div_pos (hμ 0).1 h0).ne' (div_pos (hμ 1).1 h1).ne', hz]
    congr 2 <;> field_simp
  have hz_mem : z ∈ Set.Ioo 0 1 := by
    rw [← hx, ← hmeans]
    exact Measure.slope_cgf_natParam_mem_expFamilyMeans hT (hμ' 0) (hμ' 1) hμ01
  have h_kl (a : Fin 2) : klBer z (μ a) = ENNReal.ofReal (ρ.expFamilyDiv id z (μ a)) := by
    rw [expFamilyDiv_bernoulliMeasure_sigmoid 0 hz_mem (hμ a),
      klBer_eq_ofReal_klBerReal (Set.Ioo_subset_Icc_self hz_mem)
        (Set.Ioo_subset_Icc_self (hμ a)) (klBer_ne_top (hμ a))]
  refine ⟨?_, ?_⟩
  · rw [h, hx, h_kl]
  · rw [h, Measure.expFamilyDiv_slope_eq hη, hx, h_kl]

end Degenne2023Existence
