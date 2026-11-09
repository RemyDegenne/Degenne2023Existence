/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Setting
public import Degenne2023Existence.ForLMLExplore.Identification.ErrorLowerBound
public import Degenne2023Existence.ForLMLExplore.InformationTheory.KullbackLeibler.Bernoulli

/-!
# Theorem 2 of [D23]: a non-asymptotic lower bound on the difficulty ratio

For every difficulty function `H`, every two models `μ` and `λ` without a common correct answer
and every algorithm with budget `T` with `H(λ) ≤ √T`,
`R_{H,T}(𝒜, λ)⁻¹ (1 - p_{μ,T}(𝒜)) - log 2 / √T ≤ H(λ) ∑ a, E_μ[N_{T,a} / T] KL(ν_a(μ), ν_a(λ))`.

The proof applies the change of measure at the budget to the event that the output is a correct
answer of `μ`, and the bound `kl(p, q) ≥ p log (1 / q) - log 2` of the binary relative entropy.

## Main statements

* `Degenne2023Existence.inv_difficultyRatio_mul_le`: [D23, Theorem 2].
* `Degenne2023Existence.inv_difficultyRatio_mul_le_cost`: the same bound written with the
  transportation cost of the expected proportions of pulls at `μ`.
* `Degenne2023Existence.eventually_mul_inv_difficultyRatio_le`: the form in which the asymptotic
  results use it: for a family whose probability of error at `μ` tends to `0`, every `c < 1` and
  `T` large, `c R_{H,T}(𝒜, λ)⁻¹ ≤ H(λ) cost(w_T, μ, λ) + log 2 / √T` for every alternative `λ`
  with `H(λ)` bounded by a constant, where `w_T` are the expected proportions of pulls at `μ`.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
-/

@[expose] public section

open MeasureTheory Filter Topology InformationTheory Learning LMLExplore LMLExplore.Identification

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
  set P := (𝒜 T).outputMeasure (Environment.bandit (task.ν μ))
  set P' := (𝒜 T).outputMeasure (Environment.bandit (task.ν μ'))
  set S := ∑ a, (∫⁻ ω, (pullCount IT.action a T ω : ℝ≥0∞)
    ∂(trajMeasure (𝒜 T).alg (Environment.bandit (task.ν μ)))) * klDiv (task.ν μ a) (task.ν μ' a)
    with hS
  set L := (-ENNReal.log (task.errorProb 𝒜 μ' T)).toENNReal
  have hT : T ≠ 0 := by
    rintro rfl
    simp_all
  -- The event `E` that the output is a correct answer of `μ`, up to a `P`-null set.
  set E := (toMeasurable P (task.correct μ)ᶜ)ᶜ with hE_def
  have hE : MeasurableSet E := (measurableSet_toMeasurable _ _).compl
  have hPE : P E = 1 - task.errorProb 𝒜 μ T := by
    rw [hE_def, prob_compl_eq_one_sub (measurableSet_toMeasurable _ _), measure_toMeasurable]
    rfl
  have hP'E : P' E ≤ task.errorProb 𝒜 μ' T := by
    refine measure_mono ?_
    calc E ⊆ task.correct μ := by
          rw [hE_def, Set.compl_subset_comm]
          exact subset_toMeasurable _ _
      _ ⊆ (task.correct μ')ᶜ := hμμ'.subset_compl_right
  -- The change of measure and `kl(p, q) ≥ p log (1 / q) - log 2` give
  -- `(1 - p_{μ,T}) log (1 / p_{λ,T}) ≤ ∑ a, E_μ[N_{T,a}] KL(ν_a(μ), ν_a(λ)) + log 2`.
  have hkl : klBer (P.real E) (P'.real E) ≤ S :=
    (klBer_measureReal_le_klDiv hE).trans (h𝒜.klDiv_outputMeasure_le _ _)
  have hlow := ofReal_mul_neg_log_le_klBer_add_log_two (p := P.real E) (q := P'.real E)
    ⟨measureReal_nonneg, measureReal_le_one⟩ ⟨measureReal_nonneg, measureReal_le_one⟩
  rw [ofReal_measureReal, ofReal_measureReal, hPE] at hlow
  have hLE : L ≤ (-ENNReal.log (P' E)).toENNReal :=
    EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (ENNReal.log_monotone hP'E))
  have key : (1 - task.errorProb 𝒜 μ T) * L ≤ S + ENNReal.ofReal (Real.log 2) :=
    calc (1 - task.errorProb 𝒜 μ T) * L
        ≤ (1 - task.errorProb 𝒜 μ T) * (-ENNReal.log (P' E)).toENNReal := by gcongr
      _ ≤ S + ENNReal.ofReal (Real.log 2) := hlow.trans (add_le_add hkl le_rfl)
  -- Multiply by `H(λ) / T ≤ 1 / √T`.
  have hsum : H μ' * ∑ a, (∫⁻ ω, (pullCount IT.action a T ω : ℝ≥0∞)
      ∂(trajMeasure (𝒜 T).alg (Environment.bandit (task.ν μ)))) / T *
        klDiv (task.ν μ a) (task.ν μ' a) = H μ' / T * S := by
    simp_rw [hS, ENNReal.div_eq_inv_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    ring
  have hlog : H μ' / T * ENNReal.ofReal (Real.log 2) ≤ ENNReal.ofReal (Real.log 2 / √T) := by
    have hTpos : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero hT
    calc H μ' / T * ENNReal.ofReal (Real.log 2)
        ≤ ENNReal.ofReal √T / ENNReal.ofReal T * ENNReal.ofReal (Real.log 2) := by
          rw [ENNReal.ofReal_natCast]
          gcongr
      _ = ENNReal.ofReal (Real.log 2 / √T) := by
          rw [← ENNReal.ofReal_div_of_pos hTpos, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have hs : √(T : ℝ) * √T = T := Real.mul_self_sqrt hTpos.le
          rw [div_mul_eq_mul_div, div_eq_div_iff hTpos.ne' (Real.sqrt_pos.2 hTpos).ne']
          linear_combination (Real.log 2) * hs
  calc (task.difficultyRatio H 𝒜 μ' T)⁻¹ * (1 - task.errorProb 𝒜 μ T)
      = H μ' / T * ((1 - task.errorProb 𝒜 μ T) * L) := by
        rw [task.inv_difficultyRatio hH₀ (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH) hT,
          ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
        ring
    _ ≤ H μ' / T * (S + ENNReal.ofReal (Real.log 2)) := by gcongr
    _ ≤ _ := by
        rw [mul_add, hsum]
        gcongr

/-- **Theorem 2 with the expected proportions of pulls** [D23, Theorem 2]: under the hypotheses of
`inv_difficultyRatio_mul_le`,
`R_{H,T}(𝒜, λ)⁻¹ (1 - p_{μ,T}(𝒜)) ≤ H(λ) cost(w_T, μ, λ) + log 2 / √T`, where `w_T` are the
expected proportions of pulls of `𝒜 T` at `μ` and `cost(w, μ, λ) = ∑ a, w a KL(ν_a(μ), ν_a(λ))`
is the transportation cost. -/
lemma inv_difficultyRatio_mul_le_cost (task : IdentTask α Θ ℐ 𝓨) (H : Θ → ℝ≥0∞)
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} {T : ℕ} (h𝒜 : IsFixedBudget (𝒜 T) T) {μ μ' : Θ}
    (hμμ' : Disjoint (task.correct μ) (task.correct μ')) (hH₀ : H μ' ≠ 0)
    (hH : H μ' ≤ ENNReal.ofReal √T) :
    (task.difficultyRatio H 𝒜 μ' T)⁻¹ * (1 - task.errorProb 𝒜 μ T) ≤
      H μ' * task.cost (expectedPullProportion (𝒜 T) (Environment.bandit (task.ν μ))) μ μ' +
        ENNReal.ofReal (Real.log 2 / √T) := by
  have hT : T ≠ 0 := by
    rintro rfl
    simp_all
  convert inv_difficultyRatio_mul_le task H h𝒜 hμμ' hH₀ hH using 3
  rw [IdentTask.cost_def]
  congr 1 with a
  rw [h𝒜.lintegral_pullCount_div hT]

/-- The term `log 2 / √T` of Theorem 2 of [D23] tends to `0`. -/
lemma tendsto_ofReal_log_two_div_sqrt :
    Tendsto (fun T : ℕ ↦ ENNReal.ofReal (Real.log 2 / √T)) atTop (𝓝 0) := by
  rw [← ENNReal.ofReal_zero]
  exact ENNReal.tendsto_ofReal (tendsto_const_nhds.div_atTop
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))

/-- **Theorem 2 for large budgets**, the step of [D23, proof of Theorem 3] that applies Theorem 2
of [D23]; the proof of Theorem 13 of [D23] uses it too. Let `𝒜` be a fixed-budget family whose
probability of error at the model `μ` tends to `0`, and let `c < 1` and `B < ∞`. For every large
enough budget `T`, the expected proportions `w_T` of pulls of `𝒜 T` at `μ` lie in the simplex,
and every model `λ` without a common correct answer with `μ` with `0 < H(λ) ≤ B` satisfies
`c R_{H,T}(𝒜, λ)⁻¹ ≤ H(λ) cost(w_T, μ, λ) + log 2 / √T`. -/
lemma eventually_mul_inv_difficultyRatio_le (task : IdentTask α Θ ℐ 𝓨) (H : Θ → ℝ≥0∞)
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} (h𝒜 : IsFixedBudgetFamily 𝒜) {μ : Θ}
    (hμ : Tendsto (task.errorProb 𝒜 μ) atTop (𝓝 0)) {c : ℝ≥0∞} (hc : c < 1) {B : ℝ≥0∞}
    (hB : B ≠ ∞) :
    ∀ᶠ T in atTop, expectedPullProportion (𝒜 T) (Environment.bandit (task.ν μ)) ∈ simplex α ∧
      ∀ μ', Disjoint (task.correct μ) (task.correct μ') → H μ' ≠ 0 → H μ' ≤ B →
        c * (task.difficultyRatio H 𝒜 μ' T)⁻¹ ≤
          H μ' * task.cost (expectedPullProportion (𝒜 T) (Environment.bandit (task.ν μ))) μ μ' +
            ENNReal.ofReal (Real.log 2 / √T) := by
  have h1 : ∀ᶠ T in atTop, task.errorProb 𝒜 μ T < 1 - c :=
    hμ.eventually (gt_mem_nhds (tsub_pos_of_lt hc))
  have h2 : ∀ᶠ T : ℕ in atTop, B ≤ ENNReal.ofReal √T := by
    filter_upwards [eventually_ge_atTop ⌈B.toReal ^ 2⌉₊] with T hT
    rw [← ENNReal.ofReal_toReal hB]
    exact ENNReal.ofReal_le_ofReal (Real.le_sqrt_of_sq_le ((Nat.le_ceil _).trans
      (by exact_mod_cast hT)))
  filter_upwards [h1, h2, eventually_ge_atTop 1] with T hp hBT hT
  refine ⟨(h𝒜 T).expectedPullProportion_mem_simplex (by omega) _, fun μ' hμμ' hH₀ hH ↦ ?_⟩
  have hc' : c ≤ 1 - task.errorProb 𝒜 μ T :=
    ENNReal.le_sub_of_add_le_left (ne_top_of_lt hp) (lt_tsub_iff_right.1 hp).le
  calc c * (task.difficultyRatio H 𝒜 μ' T)⁻¹
      ≤ (task.difficultyRatio H 𝒜 μ' T)⁻¹ * (1 - task.errorProb 𝒜 μ T) := by
        rw [mul_comm]
        gcongr
    _ ≤ _ := inv_difficultyRatio_mul_le_cost task H (h𝒜 T) hμμ' hH₀ (hH.trans hBT)

end Degenne2023Existence
