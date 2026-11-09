/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Theorem1

/-!
# Theorem 5 of [D23]: the difficulty ratio of static proportions is at most `K`

A static proportions algorithm with proportions `w ∈ Δ_K^0` has a bounded maximal difficulty ratio
to the static-proportions difficulty `H^{sp}`: `sup_{λ ∈ 𝒟} R_{H^{sp},∞}(𝒜, λ) ≤ (min_j w_j)⁻¹`. In
particular the uniform allocation has maximal difficulty ratio at most `K`.

The paper writes `H_{𝒞^{sp}}` for the oracle difficulty of the class of static proportions
algorithms, equal to `H^{sp}` by Theorem 1 (`oracleDifficulty_staticClass`). The recommendation
rule is assumed to satisfy the condition of `tendsto_errorRate_of_isStaticProportions` (erratum E1
of `notes/paper-errata.md`).

The two statements below, as frozen at the end of phase 1, are false for the same reason as those
of Theorem 1: they do not assume that the singletons of the answer type `ℐ` are measurable
(`notes/statement-corrections.md`, Theorems 1 and 5). They are blocked until the user decides. The
`_of_measurableSet` lemmas prove them when the sets of correct answers of the admissible models are
measurable.

## Main statements

* `Degenne2023Existence.maxRatio_staticDifficulty_le_of_isStaticProportions_of_measurableSet`,
  `Degenne2023Existence.maxRatio_staticDifficulty_le_card_of_measurableSet`: [D23, Theorem 5],
  when the sets of correct answers are measurable.
* `Degenne2023Existence.maxRatio_staticDifficulty_le_of_isStaticProportions`:
  [D23, Theorem 5].
* `Degenne2023Existence.maxRatio_staticDifficulty_le_card`: [D23, Theorem 5], the uniform
  allocation.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
-/

@[expose] public section

open MeasureTheory Filter Topology InformationTheory Learning LMLExplore LMLExplore.Identification

open scoped ENNReal

namespace Degenne2023Existence

variable {α ℐ : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] [MeasurableSpace ℐ] [Finite ℐ]
  {task : IdentTask α (α → ℝ) ℐ ℝ} {ρ : α → Measure ℝ}

omit [Finite ℐ] in
/-- **The difficulty ratio of static proportions** [D23, Theorem 5], when the sets of correct
answers of the admissible models are measurable. In the setting of
`tendsto_errorRate_of_isStaticProportions_of_measurableSet`, the maximal difficulty ratio of the
static proportions algorithm `𝒜` with proportions `w` to the static-proportions difficulty is
finite and at most `(min_j w_j)⁻¹`.

At a model with alternatives, the rate of `𝒜` is the inverse of the cost `L_w` of the alternatives
with the allocation `w` (Theorem 1), and `L_w ≥ (min_j w_j) L_{w'}` for every `w'` in the simplex.
At a model without alternatives, the probability of error vanishes for `T` large. -/
lemma maxRatio_staticDifficulty_le_of_isStaticProportions_of_measurableSet
    (hρ : ∀ a c, ¬ id =ᵐ[ρ a] fun _ ↦ c)
    (hρ_closure : ∀ a, ∀ᵐ x ∂(ρ a), x ∈ closure ((ρ a).expFamilyMeans id))
    (hν : ∀ μ a, μ a ∈ (ρ a).expFamilyMeans id →
      task.ν μ a = (ρ a).expFamily id ((ρ a).natParam id (μ a)))
    (hreg : IsRegular task {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id})
    (hsingle : task.IsSingleAnswer) {rec : (α → ℝ) → ℐ}
    (hrec : ∀ i, ∀ x ∈ closure {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id},
      x ∉ closure (task.alt i) → rec x = i)
    {𝒜 : ℕ → IdentAlg Unit α ℝ ℐ} {w : α → ℝ} (h𝒜 : task.IsStaticProportions rec 𝒜 w)
    (hc : ∀ μ ∈ task.M, MeasurableSet (task.correct μ)) :
    task.maxRatio task.staticDifficulty 𝒜 < ∞ ∧
      task.maxRatio task.staticDifficulty 𝒜 ≤ (⨅ a, ENNReal.ofReal (w a))⁻¹ := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure ((𝒜 0).alg.policyZero ())
  set m := ⨅ a, ENNReal.ofReal (w a) with hm
  have hm0 : m ≠ 0 := by
    obtain ⟨a, ha⟩ := exists_eq_ciInf_of_finite (f := fun a ↦ ENNReal.ofReal (w a))
    rw [hm, ← ha]
    exact (ENNReal.ofReal_pos.2 (h𝒜.1 a)).ne'
  have hle : task.maxRatio task.staticDifficulty 𝒜 ≤ m⁻¹ := by
    refine iSup₂_le fun μ hμ ↦ ?_
    obtain ⟨i, hi⟩ := task.isSingleAnswer_iff.1 hsingle μ hμ
    have hμS := hreg.M_subset hμ
    rcases (task.alternatives μ).eq_empty_or_nonempty with hemp | ⟨μ₀, hμ₀⟩
    · -- Without alternatives, the probability of error vanishes for `T` large.
      have hev : ∀ᶠ T in atTop, task.difficultyRatio task.staticDifficulty 𝒜 μ T = 0 := by
        filter_upwards [eventually_errorProb_le_of_isStaticProportions hρ_closure hν
          hreg.M_subset hrec h𝒜 hμ (hc μ hμ) hi] with T hT
        rw [← task.alternatives_eq_alt hi, hemp, closure_empty, Set.inter_empty, measure_empty,
          nonpos_iff_eq_zero] at hT
        rw [IdentTask.difficultyRatio, IdentTask.errorRate, hT, ENNReal.log_zero, EReal.neg_bot,
          EReal.toENNReal_top, ENNReal.div_top, ENNReal.zero_div]
      rw [IdentTask.asymptoticRatio, limsup_congr hev, limsup_const]
      exact zero_le
    set L := ⨅ μ' ∈ task.alternatives μ, task.cost w μ' μ
    set V := ⨆ w' ∈ simplex α, ⨅ μ' ∈ task.alternatives μ, task.cost w' μ' μ
    have hμ₀S := hreg.M_subset hμ₀.1
    -- The costs of `μ₀` are bounded, so `V` is finite.
    have hcost_le (w' : α → ℝ) (hw' : w' ∈ simplex α) :
        task.cost w' μ₀ μ ≤ ∑ a, klDiv (task.ν μ₀ a) (task.ν μ a) := by
      rw [IdentTask.cost_def]
      gcongr with a
      calc ENNReal.ofReal (w' a) * klDiv (task.ν μ₀ a) (task.ν μ a)
          ≤ 1 * klDiv (task.ν μ₀ a) (task.ν μ a) := by
            gcongr
            exact ENNReal.ofReal_le_one.2 ((simplex_subset_Icc hw').2 a)
        _ = klDiv (task.ν μ₀ a) (task.ν μ a) := one_mul _
    have hB : ∑ a, klDiv (task.ν μ₀ a) (task.ν μ a) ≠ ∞ := by
      refine ENNReal.sum_ne_top.2 fun a _ ↦ ?_
      rw [hν μ₀ a (hμ₀S a), hν μ a (hμS a), Measure.klDiv_expFamily_natParam (hμ₀S a) (hμS a)]
      exact ENNReal.ofReal_ne_top
    have hV : V ≠ ∞ := ne_top_of_le_ne_top hB
      (iSup₂_le fun w' hw' ↦ (iInf₂_le μ₀ hμ₀).trans (hcost_le w' hw'))
    -- `L_w ≥ (min_j w_j) L_{w'}` for every `w'` in the simplex.
    have hmV : m * V ≤ L := by
      rw [ENNReal.mul_iSup]
      refine iSup_le fun w' ↦ ?_
      rw [ENNReal.mul_iSup]
      refine iSup_le fun hw' ↦ le_iInf₂ fun μ' hμ' ↦ ?_
      refine (mul_le_mul_right (iInf₂_le μ' hμ') m).trans ?_
      rw [IdentTask.cost_def, IdentTask.cost_def, Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ ↦ ?_
      rw [← mul_assoc]
      refine mul_le_mul_left ?_ _
      calc m * ENNReal.ofReal (w' a) ≤ m * 1 := by
            gcongr
            exact ENNReal.ofReal_le_one.2 ((simplex_subset_Icc hw').2 a)
        _ = m := mul_one m
        _ ≤ ENNReal.ofReal (w a) := iInf_le _ a
    have hlim : Tendsto (task.difficultyRatio task.staticDifficulty 𝒜 μ) atTop
        (𝓝 (L⁻¹ * V)) := by
      have : task.difficultyRatio task.staticDifficulty 𝒜 μ =
          fun T ↦ task.errorRate 𝒜 μ T * V := by
        ext T
        rw [IdentTask.difficultyRatio, IdentTask.staticDifficulty, div_eq_mul_inv, inv_inv]
      rw [this]
      exact ENNReal.Tendsto.mul_const (tendsto_errorRate_of_isStaticProportions_of_measurableSet
        hρ hρ_closure hν hreg hsingle hrec h𝒜 hμ (hc μ hμ)) (Or.inr hV)
    rw [IdentTask.asymptoticRatio, hlim.limsup_eq]
    rcases eq_or_ne V 0 with hV0 | hV0
    · rw [hV0, mul_zero]
      exact zero_le
    calc L⁻¹ * V ≤ (m * V)⁻¹ * V := by gcongr
      _ = m⁻¹ := by
        rw [ENNReal.mul_inv (Or.inr hV) (Or.inr hV0), mul_assoc, ENNReal.inv_mul_cancel hV0 hV,
          mul_one]
  exact ⟨hle.trans_lt (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hm0)), hle⟩

omit [Finite ℐ] in
/-- **The difficulty ratio of uniform sampling** [D23, Theorem 5], when the sets of correct answers
of the admissible models are measurable. In the setting of
`maxRatio_staticDifficulty_le_of_isStaticProportions_of_measurableSet`, the static proportions
algorithm with the uniform proportions `1 / K` has maximal difficulty ratio at most `K` to the
static-proportions difficulty. -/
lemma maxRatio_staticDifficulty_le_card_of_measurableSet (hρ : ∀ a c, ¬ id =ᵐ[ρ a] fun _ ↦ c)
    (hρ_closure : ∀ a, ∀ᵐ x ∂(ρ a), x ∈ closure ((ρ a).expFamilyMeans id))
    (hν : ∀ μ a, μ a ∈ (ρ a).expFamilyMeans id →
      task.ν μ a = (ρ a).expFamily id ((ρ a).natParam id (μ a)))
    (hreg : IsRegular task {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id})
    (hsingle : task.IsSingleAnswer) {rec : (α → ℝ) → ℐ}
    (hrec : ∀ i, ∀ x ∈ closure {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id},
      x ∉ closure (task.alt i) → rec x = i)
    {𝒜 : ℕ → IdentAlg Unit α ℝ ℐ}
    (h𝒜 : task.IsStaticProportions rec 𝒜 fun _ ↦ 1 / (Fintype.card α : ℝ))
    (hc : ∀ μ ∈ task.M, MeasurableSet (task.correct μ)) :
    task.maxRatio task.staticDifficulty 𝒜 ≤ Fintype.card α := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure ((𝒜 0).alg.policyZero ())
  refine (maxRatio_staticDifficulty_le_of_isStaticProportions_of_measurableSet hρ hρ_closure hν
    hreg hsingle hrec h𝒜 hc).2.trans_eq ?_
  have hK : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [iInf_const, ENNReal.ofReal_div_of_pos hK, ENNReal.ofReal_one, ENNReal.ofReal_natCast,
    ENNReal.inv_div (Or.inl (ENNReal.natCast_ne_top _)) (Or.inl (by simp)),
    div_one]

/-- **The difficulty ratio of static proportions** [D23, Theorem 5]. With arms in exponential
families, a task satisfying Assumption 1 with a single correct answer on every admissible model,
and a static proportions algorithm `𝒜` with proportions `w` whose recommendation rule satisfies
the condition of `tendsto_errorRate_of_isStaticProportions`, the maximal difficulty ratio of `𝒜` to
the static-proportions difficulty is finite (`𝒜` belongs to the class `\overline{𝒞^{sp}}`) and at
most `(min_j w_j)⁻¹`. -/
theorem maxRatio_staticDifficulty_le_of_isStaticProportions
    (hρ : ∀ a c, ¬ id =ᵐ[ρ a] fun _ ↦ c)
    (hρ_closure : ∀ a, ∀ᵐ x ∂(ρ a), x ∈ closure ((ρ a).expFamilyMeans id))
    (hν : ∀ μ a, μ a ∈ (ρ a).expFamilyMeans id →
      task.ν μ a = (ρ a).expFamily id ((ρ a).natParam id (μ a)))
    (hreg : IsRegular task {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id})
    (hsingle : task.IsSingleAnswer) {rec : (α → ℝ) → ℐ}
    (hrec : ∀ i, ∀ x ∈ closure {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id},
      x ∉ closure (task.alt i) → rec x = i)
    {𝒜 : ℕ → IdentAlg Unit α ℝ ℐ} {w : α → ℝ} (h𝒜 : task.IsStaticProportions rec 𝒜 w) :
    task.maxRatio task.staticDifficulty 𝒜 < ∞ ∧
      task.maxRatio task.staticDifficulty 𝒜 ≤ (⨅ a, ENNReal.ofReal (w a))⁻¹ := by
  sorry

/-- **The difficulty ratio of uniform sampling** [D23, Theorem 5]. In the setting of
`maxRatio_staticDifficulty_le_of_isStaticProportions`, the static proportions algorithm with the
uniform proportions `1 / K` has maximal difficulty ratio at most `K` to the static-proportions
difficulty. -/
theorem maxRatio_staticDifficulty_le_card (hρ : ∀ a c, ¬ id =ᵐ[ρ a] fun _ ↦ c)
    (hρ_closure : ∀ a, ∀ᵐ x ∂(ρ a), x ∈ closure ((ρ a).expFamilyMeans id))
    (hν : ∀ μ a, μ a ∈ (ρ a).expFamilyMeans id →
      task.ν μ a = (ρ a).expFamily id ((ρ a).natParam id (μ a)))
    (hreg : IsRegular task {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id})
    (hsingle : task.IsSingleAnswer) {rec : (α → ℝ) → ℐ}
    (hrec : ∀ i, ∀ x ∈ closure {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id},
      x ∉ closure (task.alt i) → rec x = i)
    {𝒜 : ℕ → IdentAlg Unit α ℝ ℐ}
    (h𝒜 : task.IsStaticProportions rec 𝒜 fun _ ↦ 1 / (Fintype.card α : ℝ)) :
    task.maxRatio task.staticDifficulty 𝒜 ≤ Fintype.card α := by
  sorry

end Degenne2023Existence
