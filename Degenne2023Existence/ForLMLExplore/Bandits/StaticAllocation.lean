/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.ForLMLExplore.Probability.LargeDeviations.Cramer
public import LeanMachineLearning.Online.Bandit.ArrayProbSpace

/-!
# Large deviations of the empirical means under static allocations

Let the arms `a` of a stochastic bandit `ν : Kernel α ℝ`, finitely many, have laws whose empirical
means satisfy the large deviation principle with good rate functions `I a`, for instance by
Cramér's theorem when their cumulant generating functions are finite near `0`. Let `alg T` be
algorithms whose numbers of pulls after `T` rounds satisfy `|N_{T,a} - T w a| ≤ k` almost surely,
for proportions `w a > 0`. Then the laws of the vectors `μ̂_T` of the empirical means after `T`
rounds satisfy the large deviation principle with speed `T` and good rate function
`x ↦ ∑ a, w a I a (x a)`.

The proof works in LML's array model (`Bandits.ArrayModel`), the stack of rewards of Section 4.6
of [LS20]: the reward of the `m`-th pull of the arm `a` is the entry `m` of the row `a` of an
array `y` with law `streamMeasure ν`, whose rows are independent i.i.d. sequences
(`streamMeasure_map_swap`). The empirical mean of the arm `a` after `T` rounds is the mean of the
first `N_{T,a}` entries of its row.

* The upper bound is uniform over the numbers of samples `n a ≥ T w a - k`
  (`exists_eventually_streamMeasure_mean_mem_le`): a closed set `F` is covered, inside a large
  box, by finitely many products of balls, on which the probability is a product of the
  probabilities of the rows, each bounded by the upper bound of its principle; outside the box,
  the exponential tightness of each row bounds it. The window of the `(2 k + 1)^K` possible
  numbers of pulls then costs a constant factor.
* The lower bound asks the mean of the first `⌈T w a - k⌉₊` entries of each row to be close to
  the target and the next `2 k + 1` entries to lie in a fixed ball
  (`exists_eventually_le_streamMeasure_forall_mean_mem`): the means after every number of pulls in
  the window are then close to the target, at the price of a constant factor.

## Main statements

* `LMLExplore.Bandits.streamMeasure_map_swap`: the rows of the reward array are independent
  i.i.d. sequences.
* `LMLExplore.Bandits.exists_eventually_streamMeasure_mean_mem_le`,
  `LMLExplore.Bandits.exists_eventually_le_streamMeasure_forall_mean_mem`: the exponential upper
  and lower bounds for the empirical means of the rows, with the numbers of samples in a window.
* `LMLExplore.Bandits.isLDP_empMean_of_abs_pullCount_sub_le`: [D23, Theorem 12] for laws whose
  empirical means satisfy a large deviation principle with a good rate function.
* `LMLExplore.Bandits.isLDP_empMean_rateFunction_of_abs_pullCount_sub_le`: [D23, Theorem 12]
  for laws whose cumulant generating function is finite near `0`, with the Cramér rate functions.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
* [LS20] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset Learning Bandits

open scoped ENNReal NNReal

namespace LMLExplore.Bandits

variable {α : Type*} {mα : MeasurableSpace α}

/-! ### The rows of the reward array -/

section Rows

/-- Under `streamMeasure ν`, the rows `i ↦ y i a` of the reward array are independent, and the row
of `a` is an i.i.d. sequence of law `ν a`. -/
lemma streamMeasure_map_swap (ν : Kernel α ℝ) [IsMarkovKernel ν] :
    (streamMeasure ν).map (fun y a i ↦ y i a) =
      Measure.infinitePi fun a ↦ Measure.infinitePi fun _ : ℕ ↦ ν a := by
  have h1 := Measure.infinitePi_map_curry_symm (fun (_ : ℕ) (a : α) ↦ ν a)
  have h2 := Measure.infinitePi_map_piCongrLeft (X := fun _ : α × ℕ ↦ ℝ)
    (fun p : α × ℕ ↦ ν p.1) (Equiv.prodComm ℕ α)
  have h3 := Measure.infinitePi_map_curry (fun (a : α) (_ : ℕ) ↦ ν a)
  have h_eq : (fun (y : ℕ → α → ℝ) a i ↦ y i a) = (MeasurableEquiv.curry α ℕ ℝ) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : α × ℕ ↦ ℝ) (Equiv.prodComm ℕ α)) ∘
      (MeasurableEquiv.curry ℕ α ℝ).symm := by
    ext y a i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rw [h_eq, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop)]
  unfold streamMeasure
  rw [h1]
  simp only [Equiv.prodComm_apply, Prod.fst_swap] at h2
  rw [h2, h3]

/-- Under `streamMeasure ν`, the row `i ↦ y i a` of the reward array is an i.i.d. sequence of law
`ν a`. -/
lemma streamMeasure_map_row (ν : Kernel α ℝ) [IsMarkovKernel ν] (a : α) :
    (streamMeasure ν).map (fun y i ↦ y i a) = Measure.infinitePi fun _ : ℕ ↦ ν a := by
  rw [show (fun (y : ℕ → α → ℝ) i ↦ y i a) = (fun z ↦ z a) ∘ (fun y a i ↦ y i a) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), streamMeasure_map_swap,
    Measure.infinitePi_map_eval]

/-- The empirical mean of the first `n` terms of an i.i.d. sequence of law `μ` has the law of the
empirical mean of `n` independent samples of `μ`. -/
lemma infinitePi_map_mean (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ ↦ μ).map (fun z ↦ (∑ i ∈ range n, z i) / (n : ℝ)) =
      (Measure.pi fun _ : Fin n ↦ μ).map fun y ↦ (∑ i, y i) / (n : ℝ) := by
  have h : iIndepFun (fun (i : Fin n) (z : ℕ → ℝ) ↦ z i) (Measure.infinitePi fun _ ↦ μ) :=
    (iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ) (X := fun _ ↦ id)
      (fun _ ↦ measurable_id)).precomp Fin.val_injective
  have h_pi : (Measure.infinitePi fun _ : ℕ ↦ μ).map (fun z (i : Fin n) ↦ z i) =
      Measure.pi fun _ : Fin n ↦ μ := by
    rw [h.map_fun_eq_pi_map (fun (i : Fin n) ↦ (measurable_pi_apply (i : ℕ)).aemeasurable)]
    congr 1
    ext1 i
    exact Measure.infinitePi_map_eval _ _
  rw [← h_pi, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext z
  simp [Fin.sum_univ_eq_sum_range (fun i ↦ z i)]

/-- The empirical mean of the first `n` terms of an i.i.d. sequence lies in `B`, and its next `m`
terms lie in `C`, with probability `P(μ̂_n ∈ B) μ(C)^m`. -/
lemma infinitePi_mean_mem_and_forall_mem (μ : Measure ℝ) [IsProbabilityMeasure μ] (n m : ℕ)
    {B C : Set ℝ} (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (Measure.infinitePi fun _ : ℕ ↦ μ) {z | (∑ i ∈ range n, z i) / (n : ℝ) ∈ B ∧
      ∀ j < m, z (n + j) ∈ C} =
      ((Measure.pi fun _ : Fin n ↦ μ).map fun y ↦ (∑ i, y i) / (n : ℝ)) B * μ C ^ m := by
  have h_ind := (iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ) (X := fun _ ↦ id)
    (fun _ ↦ measurable_id)).indepFun_finset (range n) (Ico n (n + m))
    (Finset.disjoint_left.2 fun i hi hi' ↦ by simp at hi hi'; omega) (fun _ ↦ by fun_prop)
  simp only [id] at h_ind
  have h_meas_f : Measurable fun u : {i // i ∈ range n} → ℝ ↦ (∑ i, u i) / (n : ℝ) := by
    fun_prop
  have h_set : {z : ℕ → ℝ | (∑ i ∈ range n, z i) / (n : ℝ) ∈ B ∧ ∀ j < m, z (n + j) ∈ C} =
      (fun z (i : range n) ↦ z i) ⁻¹' ((fun u ↦ (∑ i, u i) / (n : ℝ)) ⁻¹' B) ∩
        (fun z (i : Ico n (n + m)) ↦ z i) ⁻¹' (Set.univ.pi fun _ ↦ C) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, true_implies, Subtype.forall, mem_Ico]
    refine and_congr ?_ ⟨fun h i hi ↦ ?_, fun h j hj ↦ h _ ⟨by omega, by omega⟩⟩
    · rw [Finset.sum_coe_sort (range n) z]
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi.1
      exact h j (by omega)
  rw [h_set, h_ind.measure_inter_preimage_eq_mul _ _ (h_meas_f hB)
    (MeasurableSet.univ_pi fun _ ↦ hC)]
  congr 1
  · rw [← Set.preimage_comp, ← infinitePi_map_mean, Measure.map_apply (by fun_prop) hB]
    congr 1
    ext z
    simp only [Set.mem_preimage, Function.comp_apply]
    rw [Finset.sum_coe_sort (range n) z]
  · have h_pi : (fun z (i : Ico n (n + m)) ↦ z i) ⁻¹' (Set.univ.pi fun _ ↦ C) =
        ((Ico n (n + m) : Finset ℕ) : Set ℕ).pi fun _ ↦ C := by
      ext z
      simp
    rw [h_pi, Measure.infinitePi_pi _ fun _ _ ↦ hC, Finset.prod_const, Nat.card_Ico]
    congr 1
    omega

variable [Fintype α]

/-- Under `streamMeasure ν`, events on the different rows of the reward array are independent. -/
lemma streamMeasure_forall_row_mem (ν : Kernel α ℝ) [IsMarkovKernel ν]
    {E : α → Set (ℕ → ℝ)} (hE : ∀ a, MeasurableSet (E a)) :
    streamMeasure ν {y | ∀ a, (fun i ↦ y i a) ∈ E a} =
      ∏ a, (Measure.infinitePi fun _ : ℕ ↦ ν a) (E a) := by
  have h_set : {y : ℕ → α → ℝ | ∀ a, (fun i ↦ y i a) ∈ E a} =
      (fun y a i ↦ y i a) ⁻¹' ((Finset.univ : Finset α) : Set α).pi E := by
    ext y
    simp
  rw [h_set, ← Measure.map_apply (by fun_prop) (.pi (Finset.univ : Finset α).countable_toSet
    fun a _ ↦ hE a), streamMeasure_map_swap, Measure.infinitePi_pi _ fun a _ ↦ hE a]

/-- Under `streamMeasure ν`, the empirical means of the first `n a` entries of the rows `a` of the
reward array are independent, with the laws of the empirical means of `n a` independent samples
of `ν a`. -/
lemma streamMeasure_forall_mean_mem (ν : Kernel α ℝ) [IsMarkovKernel ν] (n : α → ℕ)
    {B : α → Set ℝ} (hB : ∀ a, MeasurableSet (B a)) :
    streamMeasure ν {y | ∀ a, (∑ i ∈ range (n a), y i a) / (n a : ℝ) ∈ B a} =
      ∏ a, ((Measure.pi fun _ : Fin (n a) ↦ ν a).map fun z ↦ (∑ i, z i) / (n a : ℝ)) (B a) := by
  have h := streamMeasure_forall_row_mem ν (E := fun a ↦
    (fun z : ℕ → ℝ ↦ (∑ i ∈ range (n a), z i) / (n a : ℝ)) ⁻¹' B a)
    (fun a ↦ (by fun_prop : Measurable fun z : ℕ → ℝ ↦ (∑ i ∈ range (n a), z i) / (n a : ℝ))
      (hB a))
  simp only [Set.mem_preimage] at h
  rw [h]
  congr 1
  ext1 a
  rw [← infinitePi_map_mean, Measure.map_apply (by fun_prop) (hB a)]

omit [Fintype α] in
/-- Under `streamMeasure ν`, the empirical mean of the first `m` entries of the row `a` has the law
of the empirical mean of `m` independent samples of `ν a`. -/
lemma streamMeasure_mean_mem (ν : Kernel α ℝ) [IsMarkovKernel ν] (a : α) (m : ℕ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    streamMeasure ν {y | (∑ i ∈ range m, y i a) / (m : ℝ) ∈ B} =
      ((Measure.pi fun _ : Fin m ↦ ν a).map fun z ↦ (∑ i, z i) / (m : ℝ)) B := by
  rw [← infinitePi_map_mean, ← streamMeasure_map_row,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_apply (by fun_prop) hB]
  rfl

end Rows

/-! ### Two lemmas on finitely many coordinates -/

section Aux

variable [Fintype α] {I : α → ℝ → ℝ≥0∞} {w : α → ℝ}

/-- If `r < ∑ a, w a I a (x a)` for lower semicontinuous `I a` and positive weights, there are
rates `s a ≥ 0` with `r < ∑ a, w a s a` and radii `ε a > 0` such that each `s a` is zero or below
the infimum of `I a` on the closed ball of radius `ε a` around `x a`. -/
lemma exists_rate_lt_iInf_closedBall (hI : ∀ a, LowerSemicontinuous (I a)) (hw : ∀ a, 0 < w a)
    {x : α → ℝ} {r : ℝ}
    (hr : (r : EReal) < ((∑ a, ENNReal.ofReal (w a) * I a (x a) : ℝ≥0∞) : EReal)) :
    ∃ s ε : α → ℝ, (∀ a, 0 ≤ s a) ∧ (∀ a, 0 < ε a) ∧ r < ∑ a, w a * s a ∧
      ∀ a, s a = 0 ∨ (s a : EReal) < ⨅ y ∈ Metric.closedBall (x a) (ε a), I a y := by
  have h_lsc (a : α) (u : ℝ) (hu : ENNReal.ofReal u < I a (x a)) :
      ∃ ε > 0, ENNReal.ofReal u ≤ ⨅ y ∈ Metric.closedBall (x a) ε, I a y := by
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hI a (x a) _ hu)
    refine ⟨ε / 2, by positivity, le_iInf₂ fun y hy ↦ (hball ?_).le⟩
    rw [Metric.mem_closedBall] at hy
    linarith
  suffices h : ∃ s : α → ℝ, (∀ a, 0 ≤ s a) ∧ r < ∑ a, w a * s a ∧
      ∀ a, s a = 0 ∨ ∃ u : ℝ, s a < u ∧ ENNReal.ofReal u < I a (x a) by
    obtain ⟨s, hs0, hsr, hs⟩ := h
    have h_each (a : α) : ∃ ε > 0,
        s a = 0 ∨ (s a : EReal) < ⨅ y ∈ Metric.closedBall (x a) ε, I a y := by
      rcases hs a with h0 | ⟨u, hsu, hu⟩
      · exact ⟨1, one_pos, Or.inl h0⟩
      obtain ⟨ε, hε, hε'⟩ := h_lsc a u hu
      refine ⟨ε, hε, Or.inr (lt_of_lt_of_le ?_ (EReal.coe_ennreal_le_coe_ennreal_iff.2 hε'))⟩
      rw [EReal.coe_ennreal_ofReal]
      exact EReal.coe_lt_coe_iff.2 (lt_max_of_lt_left hsu)
    choose ε hε hε' using h_each
    exact ⟨s, ε, hs0, hε, hsr, hε'⟩
  classical
  by_cases htop : ∃ a₀, I a₀ (x a₀) = ⊤
  · -- One of the rates is infinite: put all the weight on it.
    obtain ⟨a₀, ha₀⟩ := htop
    refine ⟨fun a ↦ if a = a₀ then (|r| + 1) / w a₀ else 0, fun a ↦ ?_, ?_, fun a ↦ ?_⟩
    · dsimp only
      split_ifs
      · exact div_nonneg (by positivity) (hw a₀).le
      · exact le_rfl
    · simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [mul_div_cancel₀ _ (hw a₀).ne']
      linarith [le_abs_self r]
    · by_cases ha : a = a₀
      · subst ha
        exact Or.inr ⟨(|r| + 1) / w a + 1, by simp, by rw [ha₀]; exact ENNReal.ofReal_lt_top⟩
      · exact Or.inl (by simp [ha])
  -- All the rates are finite: lower each of them by `2 η`.
  simp only [not_exists] at htop
  set t : α → ℝ := fun a ↦ (I a (x a)).toReal
  have ht0 (a : α) : 0 ≤ t a := ENNReal.toReal_nonneg
  have hJ : (∑ a, ENNReal.ofReal (w a) * I a (x a)) = ENNReal.ofReal (∑ a, w a * t a) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ mul_nonneg (hw a).le (ht0 a))]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [ENNReal.ofReal_mul (hw a).le, ENNReal.ofReal_toReal (htop a)]
  have hr' : r < ∑ a, w a * t a := by
    rw [hJ, EReal.coe_ennreal_ofReal, max_eq_left (Finset.sum_nonneg fun a _ ↦
      mul_nonneg (hw a).le (ht0 a))] at hr
    exact EReal.coe_lt_coe_iff.1 hr
  set W := ∑ a, w a
  have hW : 0 ≤ W := Finset.sum_nonneg fun a _ ↦ (hw a).le
  set η := (∑ a, w a * t a - r) / (2 * (W + 1))
  have hη : 0 < η := div_pos (by linarith) (by positivity)
  refine ⟨fun a ↦ max 0 (t a - 2 * η), fun a ↦ le_max_left _ _, ?_, fun a ↦ ?_⟩
  · calc r < ∑ a, w a * t a - 2 * η * W := by
          have : 2 * η * W = (∑ a, w a * t a - r) * (W / (W + 1)) := by
            simp only [η]
            field_simp
          rw [this]
          have h1 : W / (W + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
          nlinarith
    _ = ∑ a, w a * (t a - 2 * η) := by
          simp only [W, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun a _ ↦ by ring
    _ ≤ ∑ a, w a * max 0 (t a - 2 * η) :=
          Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left (le_max_right _ _) (hw a).le
  · rcases le_or_gt (t a - 2 * η) 0 with h | h
    · exact Or.inl (max_eq_left h)
    refine Or.inr ⟨t a - η, (max_eq_right h.le).trans_lt (by linarith), ?_⟩
    rw [ENNReal.ofReal_lt_iff_lt_toReal (by linarith) (htop a)]
    linarith

omit [Fintype α] in
/-- If a property holds eventually along `atTop` for each coordinate, then it holds for all the
`n : α → ℕ` with `T w a - k ≤ n a`, for `T` large. -/
lemma eventually_forall_of_eventually [Finite α] {Q : α → ℕ → Prop} (h : ∀ a, ∀ᶠ m in atTop, Q a m)
    (hw : ∀ a, 0 < w a) (k : ℝ) :
    ∀ᶠ T : ℕ in atTop, ∀ n : α → ℕ, (∀ a, T * w a - k ≤ n a) → ∀ a, Q a (n a) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_all.2 h)
  filter_upwards [eventually_all.2 fun a ↦ (tendsto_natCast_atTop_atTop.atTop_mul_const
    (hw a)).eventually_ge_atTop ((N : ℝ) + k)] with T hT n hn a
  exact hN (n a) (by exact_mod_cast (show (N : ℝ) ≤ n a by linarith [hT a, hn a])) a

/-- If `n a ≥ T w a - k` and `r ≤ ∑ a, w a s a` for rates `s a ≥ 0`, then
`∏ a, exp (-(n a s a)) ≤ exp (k ∑ a, s a) exp (-(T r))`. -/
lemma prod_ofReal_exp_le {s : α → ℝ} (hs : ∀ a, 0 ≤ s a) {T : ℕ} {k r : ℝ}
    (hsr : r ≤ ∑ a, w a * s a) {n : α → ℕ} (hn : ∀ a, T * w a - k ≤ n a) :
    ∏ a, ENNReal.ofReal (Real.exp (-(n a * s a))) ≤
      ENNReal.ofReal (Real.exp (k * ∑ a, s a)) * ENNReal.ofReal (Real.exp (-(T * r))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
    ← ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (Real.exp_pos _).le, ← Real.exp_sum]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have h1 : ∑ a, (T * w a - k) * s a ≤ ∑ a, (n a : ℝ) * s a :=
    Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_right (hn a) (hs a)
  have h2 : ∑ a, (T * w a - k) * s a = T * ∑ a, w a * s a - k * ∑ a, s a := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  have h3 : (T : ℝ) * r ≤ T * ∑ a, w a * s a := mul_le_mul_of_nonneg_left hsr T.cast_nonneg
  rw [Finset.sum_neg_distrib]
  linarith

omit [Fintype α] in
/-- If the mean of `n₀` numbers of sum `S` is within `δ / 2` of `x`, and `j` further numbers are
within `L` of `x`, with `2 j L < n₀ δ`, then the mean of all the `n₀ + j` numbers is within `δ`
of `x`. -/
lemma dist_mean_add_lt {n₀ j : ℕ} (hn₀ : 0 < n₀) {S x δ L : ℝ} {z : ℕ → ℝ}
    (hS : dist (S / n₀) x < δ / 2) (hz : ∀ i < j, dist (z i) x ≤ L) (hjL : 2 * (j * L) < n₀ * δ) :
    dist ((S + ∑ i ∈ range j, z i) / ((n₀ + j : ℕ) : ℝ)) x < δ := by
  have hn₀' : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  have hm : (0 : ℝ) < ((n₀ + j : ℕ) : ℝ) := by positivity
  have hS' : |S - n₀ * x| < n₀ * (δ / 2) := by
    rw [Real.dist_eq, show S / n₀ - x = (S - n₀ * x) / n₀ by field_simp, abs_div,
      abs_of_pos hn₀', div_lt_iff₀ hn₀'] at hS
    linarith
  have hsum : |∑ i ∈ range j, (z i - x)| ≤ j * L := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i hi ↦ (?_ : |z i - x| ≤ L)).trans (by simp)
    rw [← Real.dist_eq]
    exact hz i (Finset.mem_range.1 hi)
  have h_eq : (S + ∑ i ∈ range j, z i) / ((n₀ + j : ℕ) : ℝ) - x =
      ((S - n₀ * x) + ∑ i ∈ range j, (z i - x)) / ((n₀ + j : ℕ) : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
    push_cast
    ring
  rw [Real.dist_eq, h_eq, abs_div, abs_of_pos hm, div_lt_iff₀ hm]
  have hj : (n₀ : ℝ) ≤ ((n₀ + j : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right n₀ j
  have hδ : 0 < δ := by
    by_contra h
    have := dist_nonneg.trans_lt hS
    linarith
  calc |S - n₀ * x + ∑ i ∈ range j, (z i - x)|
      ≤ |S - n₀ * x| + |∑ i ∈ range j, (z i - x)| := abs_add_le _ _
    _ < n₀ * (δ / 2) + n₀ * (δ / 2) := by linarith
    _ = n₀ * δ := by ring
    _ ≤ ((n₀ + j : ℕ) : ℝ) * δ := mul_le_mul_of_nonneg_right hj hδ.le
    _ = δ * ((n₀ + j : ℕ) : ℝ) := mul_comm _ _

end Aux

/-! ### Large deviations of the empirical means of the rows -/

section Window

variable [Fintype α] {ν : Kernel α ℝ} [IsMarkovKernel ν] {I : α → ℝ → ℝ≥0∞} {w : α → ℝ}

/-- **The exponential upper bound for the rows of the reward array.** Let the laws of the empirical
means of `m` independent samples of `ν a` satisfy the large deviation principle with good rate
function `I a`, and let `w a > 0`. For a closed set `F` and `r` below the infimum of
`x ↦ ∑ a, w a I a (x a)` on `F`, there is a constant `C` such that for every large `T` and every
`n : α → ℕ` with `n a ≥ T w a - k`, the vector of the empirical means of the first `n a` entries of
the rows lies in `F` with probability at most `C exp (-(T r))`.

The bound covers the part of `F` in a large box by finitely many products of balls, on which the
probability is a product (`streamMeasure_forall_mean_mem`), and the rest by the exponential
tightness of each row. -/
lemma exists_eventually_streamMeasure_mean_mem_le
    (hP : ∀ a, IsLDP (fun m ↦ (Measure.pi fun _ : Fin m ↦ ν a).map
      fun z ↦ (∑ i, z i) / (m : ℝ)) (I a))
    (hI : ∀ a, IsGoodRateFunction (I a)) (hw : ∀ a, 0 < w a) (k : ℝ) {F : Set (α → ℝ)}
    (hF : IsClosed F) {r : ℝ}
    (hr : (r : EReal) < ((⨅ x ∈ F, ∑ a, ENNReal.ofReal (w a) * I a (x a) : ℝ≥0∞) : EReal)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ᶠ T : ℕ in atTop, ∀ n : α → ℕ, (∀ a, T * w a - k ≤ n a) →
      streamMeasure ν {y | (fun a ↦ (∑ i ∈ range (n a), y i a) / (n a : ℝ)) ∈ F} ≤
        C * ENNReal.ofReal (Real.exp (-(T * r))) := by
  rcases le_or_gt r 0 with hr0 | hr0
  · refine ⟨1, ENNReal.one_ne_top, Eventually.of_forall fun T n _ ↦ ?_⟩
    rw [one_mul]
    refine prob_le_one.trans (ENNReal.one_le_ofReal.2 (Real.one_le_exp ?_))
    nlinarith [(T.cast_nonneg : (0 : ℝ) ≤ T)]
  -- The tails of each row.
  choose M hM using fun a ↦ (hP a).exists_eventually_measure_norm_ge_le_exp (hI a) (r / w a)
  -- The rates and radii around each point of `F`.
  have hrx : ∀ x ∈ F,
      (r : EReal) < ((∑ a, ENNReal.ofReal (w a) * I a (x a) : ℝ≥0∞) : EReal) := fun x hx ↦
    hr.trans_le (EReal.coe_ennreal_le_coe_ennreal_iff.2 (iInf₂_le x hx))
  choose! s ε hs0 hε hsr hsε using fun x (hx : x ∈ F) ↦
    exists_rate_lt_iInf_closedBall (fun a ↦ (hI a).1) hw (hrx x hx)
  -- A finite cover of the part of `F` in the box.
  have hK : IsCompact (F ∩ Set.univ.pi fun a ↦ Set.Icc (-M a) (M a)) :=
    (isCompact_univ_pi fun a ↦ isCompact_Icc).inter_left hF
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover
    (fun x ↦ Set.univ.pi fun a ↦ Metric.ball (x a) (ε x a)) fun x hx ↦
      set_pi_mem_nhds Set.finite_univ fun a _ ↦ Metric.ball_mem_nhds (x a) (hε x hx.1 a)
  -- The bounds on each row, eventually.
  have h_ev (a : α) : ∀ᶠ m in atTop, (∀ x ∈ t,
      ((Measure.pi fun _ : Fin m ↦ ν a).map fun z ↦ (∑ i, z i) / (m : ℝ))
        (Metric.closedBall (x a) (ε x a)) ≤ ENNReal.ofReal (Real.exp (-(m * s x a)))) ∧
      ((Measure.pi fun _ : Fin m ↦ ν a).map fun z ↦ (∑ i, z i) / (m : ℝ)) {y | M a ≤ ‖y‖} ≤
        ENNReal.ofReal (Real.exp (-(m * (r / w a)))) := by
    refine ((eventually_all_finset t).2 fun x hx ↦ ?_).and (hM a)
    rcases hsε x (htK x hx).1 a with h0 | hlt
    · refine Eventually.of_forall fun m ↦ ?_
      rw [h0, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one]
      exact prob_le_one
    · exact (hP a).eventually_measure_le_exp Metric.isClosed_closedBall hlt
  refine ⟨∑ x ∈ t, ENNReal.ofReal (Real.exp (k * ∑ a, s x a)) +
    ∑ a, ENNReal.ofReal (Real.exp (k * (r / w a))),
    ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun _ _ ↦ ENNReal.ofReal_ne_top,
      ENNReal.sum_ne_top.2 fun _ _ ↦ ENNReal.ofReal_ne_top⟩, ?_⟩
  filter_upwards [eventually_forall_of_eventually h_ev hw k] with T hT n hn
  set m : (ℕ → α → ℝ) → α → ℝ := fun y a ↦ (∑ i ∈ range (n a), y i a) / (n a : ℝ)
  have h_sub : {y | m y ∈ F} ⊆
      (⋃ x ∈ t, {y | ∀ a, m y a ∈ Metric.closedBall (x a) (ε x a)}) ∪
        ⋃ a, {y | M a ≤ ‖m y a‖} := by
    intro y hy
    by_cases h : ∃ a, M a ≤ ‖m y a‖
    · obtain ⟨a, ha⟩ := h
      exact Or.inr (Set.mem_iUnion.2 ⟨a, ha⟩)
    simp only [not_exists, not_le] at h
    have hyK : m y ∈ F ∩ Set.univ.pi fun a ↦ Set.Icc (-M a) (M a) := by
      refine ⟨hy, fun a _ ↦ ?_⟩
      have := h a
      rw [Real.norm_eq_abs, abs_lt] at this
      exact ⟨this.1.le, this.2.le⟩
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hKt hyK)
    exact Or.inl (Set.mem_iUnion₂.2 ⟨x, hx, fun a ↦
      Metric.ball_subset_closedBall (hyx a (Set.mem_univ a))⟩)
  refine (measure_mono h_sub).trans ((measure_union_le _ _).trans ?_)
  rw [add_mul, Finset.sum_mul, Finset.sum_mul]
  gcongr ?_ + ?_
  · refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun x hx ↦ ?_)
    rw [streamMeasure_forall_mean_mem ν n fun a ↦ Metric.isClosed_closedBall.measurableSet]
    exact (Finset.prod_le_prod fun a _ ↦ (hT n hn a).1 x hx).trans
      (prod_ofReal_exp_le (hs0 x (htK x hx).1) (hsr x (htK x hx).1).le hn)
  · refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
    rw [show {y | M a ≤ ‖m y a‖} =
        {y | (∑ i ∈ range (n a), y i a) / (n a : ℝ) ∈ {z : ℝ | M a ≤ ‖z‖}} from rfl,
      streamMeasure_mean_mem ν a (n a) (isClosed_le continuous_const continuous_norm).measurableSet]
    refine (hT n hn a).2.trans ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have h1 : (T * w a - k) * (r / w a) ≤ n a * (r / w a) :=
      mul_le_mul_of_nonneg_right (hn a) (div_nonneg hr0.le (hw a).le)
    have h2 : (T * w a - k) * (r / w a) = T * r - k * (r / w a) := by
      have := (hw a).ne'
      field_simp
    linarith

/-- **The exponential lower bound for the rows of the reward array.** Let the laws of the empirical
means of `m` independent samples of `ν a` satisfy the large deviation principle with rate function
`I a`, and let `w a > 0`. For a neighbourhood `U` of `x` and `r > ∑ a, w a I a (x a)`, there is
`C > 0` such that for every large `T`, with probability at least `C exp (-(T r))`, the vectors of
the empirical means of the first `n a` entries of the rows lie in `U` for all the `n : α → ℕ` in
the window `|n a - T w a| ≤ k`.

The event asks the mean of the first `n₀ a = ⌈T w a - k⌉₊` entries of the row `a` to be close to
`x a`, which has probability about `exp (-(T w a I a (x a)))`, and the next `2 k + 1` entries to
lie in a fixed ball around `x a`, which has a positive probability independent of `T`. -/
lemma exists_eventually_le_streamMeasure_forall_mean_mem
    (hP : ∀ a, IsLDP (fun m ↦ (Measure.pi fun _ : Fin m ↦ ν a).map
      fun z ↦ (∑ i, z i) / (m : ℝ)) (I a))
    (hw : ∀ a, 0 < w a) (k : ℕ) {x : α → ℝ} {U : Set (α → ℝ)} (hU : U ∈ 𝓝 x) {r : ℝ}
    (hr : ((∑ a, ENNReal.ofReal (w a) * I a (x a) : ℝ≥0∞) : EReal) < r) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ ∀ᶠ T : ℕ in atTop, C * ENNReal.ofReal (Real.exp (-(T * r))) ≤
      streamMeasure ν {y | ∀ n : α → ℕ, (∀ a, |(n a : ℝ) - T * w a| ≤ k) →
        (fun a ↦ (∑ i ∈ range (n a), y i a) / (n a : ℝ)) ∈ U} := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
  -- The rates are finite at `x`; choose `s a > I a (x a)` with `∑ a, w a s a < r`.
  have htop (a : α) : I a (x a) ≠ ⊤ := by
    intro ha
    have h_top : (∑ a, ENNReal.ofReal (w a) * I a (x a)) = ⊤ :=
      ENNReal.sum_eq_top.2 ⟨a, Finset.mem_univ a, by
        rw [ha, ENNReal.mul_top (by simpa using hw a)]⟩
    rw [h_top] at hr
    exact absurd hr (not_lt.2 le_top)
  set t : α → ℝ := fun a ↦ (I a (x a)).toReal
  have ht0 (a : α) : 0 ≤ t a := ENNReal.toReal_nonneg
  have hr' : ∑ a, w a * t a < r := by
    have hJ : (∑ a, ENNReal.ofReal (w a) * I a (x a)) = ENNReal.ofReal (∑ a, w a * t a) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ mul_nonneg (hw a).le (ht0 a))]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [ENNReal.ofReal_mul (hw a).le, ENNReal.ofReal_toReal (htop a)]
    rw [hJ, EReal.coe_ennreal_ofReal, max_eq_left (Finset.sum_nonneg fun a _ ↦
      mul_nonneg (hw a).le (ht0 a))] at hr
    exact EReal.coe_lt_coe_iff.1 hr
  set W := ∑ a, w a
  have hW : 0 ≤ W := Finset.sum_nonneg fun a _ ↦ (hw a).le
  set η := (r - ∑ a, w a * t a) / (W + 1)
  have hη : 0 < η := div_pos (by linarith) (by positivity)
  set s : α → ℝ := fun a ↦ t a + η
  have hs0 (a : α) : 0 ≤ s a := by positivity
  have hs (a : α) : (I a (x a) : EReal) < s a := by
    rw [← EReal.coe_ennreal_toReal (htop a)]
    exact EReal.coe_lt_coe_iff.2 (by simp only [s, t]; linarith)
  have hsr : ∑ a, w a * s a ≤ r := by
    have h1 : ∑ a, w a * s a = ∑ a, w a * t a + η * W := by
      simp only [s, W, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun a _ ↦ by ring
    have h2 : η * W ≤ r - ∑ a, w a * t a := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  -- A ball of positive probability for each arm.
  have hL (a : α) : ∃ L : ℕ, ν a (Metric.closedBall (x a) L) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have h_null := measure_iUnion_null (μ := ν a) h
    rw [Metric.iUnion_closedBall_nat, measure_univ] at h_null
    exact one_ne_zero h_null
  choose L hL using hL
  -- The lower bounds of each row.
  have h_ev (a : α) : ∀ᶠ m : ℕ in atTop, ENNReal.ofReal (Real.exp (-(m * s a))) ≤
      ((Measure.pi fun _ : Fin m ↦ ν a).map fun z ↦ (∑ i, z i) / (m : ℝ))
        (Metric.ball (x a) (δ / 2)) :=
    (hP a).eventually_exp_le_measure (Metric.ball_mem_nhds _ (half_pos hδ)) (hs a)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_all.2 h_ev)
  refine ⟨∏ a, ENNReal.ofReal (Real.exp (-s a)) *
    ν a (Metric.closedBall (x a) (L a)) ^ (2 * k + 1), ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun a _ ↦ mul_ne_zero
      (by simpa using Real.exp_pos _) (pow_ne_zero _ (hL a))
  filter_upwards [eventually_all.2 fun a ↦ (tendsto_natCast_atTop_atTop.atTop_mul_const
    (hw a)).eventually_ge_atTop ((N : ℝ) + k + 1 + 4 * (2 * k + 1) * L a / δ)] with T hT
  set n₀ : α → ℕ := fun a ↦ ⌈T * w a - k⌉₊
  have hLδ (a : α) : 0 ≤ 4 * (2 * k + 1) * (L a : ℝ) / δ := by positivity
  have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
  have hn₀ (a : α) : T * w a - k ≤ n₀ a := Nat.le_ceil _
  have hn₀' (a : α) : (n₀ a : ℝ) < T * w a - k + 1 :=
    Nat.ceil_lt_add_one (by linarith [hT a, hLδ a])
  have hn₀N (a : α) : N ≤ n₀ a := by
    exact_mod_cast (show (N : ℝ) ≤ n₀ a by linarith [hn₀ a, hT a, hLδ a])
  have hn₀L (a : α) : 4 * (2 * k + 1) * (L a : ℝ) < n₀ a * δ := by
    have h1 : 4 * (2 * k + 1) * (L a : ℝ) / δ < n₀ a := by linarith [hn₀ a, hT a]
    rwa [div_lt_iff₀ hδ] at h1
  -- The event on the rows.
  set E : α → Set (ℕ → ℝ) := fun a ↦ {z | (∑ i ∈ range (n₀ a), z i) / (n₀ a : ℝ) ∈
    Metric.ball (x a) (δ / 2) ∧ ∀ j < 2 * k + 1, z (n₀ a + j) ∈ Metric.closedBall (x a) (L a)}
  have hE (a : α) : MeasurableSet (E a) := by
    have : E a = (fun z : ℕ → ℝ ↦ (∑ i ∈ range (n₀ a), z i) / (n₀ a : ℝ)) ⁻¹'
        Metric.ball (x a) (δ / 2) ∩ ⋂ j ∈ Finset.range (2 * k + 1),
          (fun z : ℕ → ℝ ↦ z (n₀ a + j)) ⁻¹' Metric.closedBall (x a) (L a) := by
      ext z
      simp [E]
    rw [this]
    exact ((by fun_prop : Measurable fun z : ℕ → ℝ ↦ (∑ i ∈ range (n₀ a), z i) / (n₀ a : ℝ))
      Metric.isOpen_ball.measurableSet).inter (Finset.measurableSet_biInter _ fun j _ ↦
        (measurable_pi_apply _) Metric.isClosed_closedBall.measurableSet)
  have h_sub : {y : ℕ → α → ℝ | ∀ a, (fun i ↦ y i a) ∈ E a} ⊆
      {y | ∀ n : α → ℕ, (∀ a, |(n a : ℝ) - T * w a| ≤ k) →
        (fun a ↦ (∑ i ∈ range (n a), y i a) / (n a : ℝ)) ∈ U} := by
    intro y hy n hn
    refine hδU ?_
    rw [ball_pi _ hδ]
    intro a _
    obtain ⟨h1, h2⟩ := hy a
    have hna := abs_le.1 (hn a)
    have hlo : n₀ a ≤ n a := Nat.ceil_le.2 (by linarith)
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hlo
    have hj2 : j ≤ 2 * k := by
      have : ((n₀ a + j : ℕ) : ℝ) ≤ n₀ a + 2 * k := by
        rw [← hj]
        linarith [hn₀ a]
      push_cast at this
      exact_mod_cast (by linarith : (j : ℝ) ≤ 2 * k)
    have hn₀pos : 0 < n₀ a := by
      have : (0 : ℝ) < n₀ a := by linarith [hn₀ a, hT a, hLδ a]
      exact_mod_cast this
    simp only [hj, Finset.sum_range_add]
    refine dist_mean_add_lt hn₀pos h1 (fun i hi ↦ h2 i (by omega)) ?_
    have : (2 : ℝ) * (j * L a) ≤ 4 * (2 * k + 1) * L a := by
      have hj' : (j : ℝ) ≤ 2 * k := by exact_mod_cast hj2
      have hL0 : (0 : ℝ) ≤ L a := Nat.cast_nonneg _
      nlinarith
    linarith [hn₀L a]
  refine le_trans ?_ (measure_mono h_sub)
  rw [streamMeasure_forall_row_mem ν hE]
  simp only [E]
  simp_rw [infinitePi_mean_mem_and_forall_mem _ _ _ Metric.isOpen_ball.measurableSet
    Metric.isClosed_closedBall.measurableSet]
  calc (∏ a, ENNReal.ofReal (Real.exp (-s a)) *
        ν a (Metric.closedBall (x a) (L a)) ^ (2 * k + 1)) *
          ENNReal.ofReal (Real.exp (-(T * r)))
      ≤ ∏ a, ENNReal.ofReal (Real.exp (-s a)) *
        ν a (Metric.closedBall (x a) (L a)) ^ (2 * k + 1) *
          ENNReal.ofReal (Real.exp (-(T * (w a * s a)))) := by
        rw [Finset.prod_mul_distrib (f := fun a ↦ ENNReal.ofReal (Real.exp (-s a)) *
          ν a (Metric.closedBall (x a) (L a)) ^ (2 * k + 1))
          (g := fun a ↦ ENNReal.ofReal (Real.exp (-(T * (w a * s a)))))]
        gcongr
        rw [← ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (Real.exp_pos _).le, ← Real.exp_sum]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
        exact neg_le_neg (mul_le_mul_of_nonneg_left hsr T.cast_nonneg)
    _ ≤ ∏ a, ((Measure.pi fun _ : Fin (n₀ a) ↦ ν a).map fun z ↦ (∑ i, z i) / (n₀ a : ℝ))
          (Metric.ball (x a) (δ / 2)) * ν a (Metric.closedBall (x a) (L a)) ^ (2 * k + 1) := by
        refine Finset.prod_le_prod fun a _ ↦ ?_
        rw [mul_right_comm]
        gcongr
        refine le_trans ?_ (hN (n₀ a) (hn₀N a) a)
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        nlinarith [hn₀' a, hs0 a, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

end Window

/-! ### Large deviations of the empirical means under static allocations -/

section Bandit

variable [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] {ν : Kernel α ℝ}
  [IsMarkovKernel ν] {I : α → ℝ → ℝ≥0∞} {w : α → ℝ}

omit [Fintype α] in
/-- The law of the vector of the empirical means after `T` rounds of a run of `alg` against the
bandit `ν` is its law in the array model. -/
lemma trajMeasure_map_empMean [Finite α] [Nonempty α] (alg : Algorithm Unit α ℝ) (T : ℕ) :
    (trajMeasure alg (Environment.bandit ν)).map (fun h a ↦ empMean IT.action IT.feedback a T h) =
      (ArrayModel.arrayMeasure ν).map fun ω a ↦
        empMean (ArrayModel.action alg) (ArrayModel.reward alg) a T ω := by
  have h_id := (IT.isAlgEnvSeq_trajMeasure alg
    (Environment.bandit ν)).identDistrib_pullCount_sumRewards
    (ArrayModel.isAlgEnvSeq_arrayMeasure alg ν)
  exact (h_id.comp (u := fun (f : ℕ → α → ℕ × ℝ) a ↦ (f T a).2 / ((f T a).1 : ℝ))
    (by fun_prop)).map_eq

omit [Fintype α] in
/-- A property of the numbers of pulls after `T` rounds that holds almost surely in a run of `alg`
against the bandit `ν` holds almost surely in the array model. -/
lemma ae_arrayMeasure_pullCount [Finite α] [Nonempty α] (alg : Algorithm Unit α ℝ) (T : ℕ)
    {p : (α → ℕ) → Prop}
    (h : ∀ᵐ h ∂(trajMeasure alg (Environment.bandit ν)), p fun a ↦ pullCount IT.action a T h) :
    ∀ᵐ ω ∂(ArrayModel.arrayMeasure ν), p fun a ↦ pullCount (ArrayModel.action alg) a T ω := by
  have h_id := (IT.isAlgEnvSeq_trajMeasure alg
    (Environment.bandit ν)).identDistrib_pullCount_sumRewards
    (ArrayModel.isAlgEnvSeq_arrayMeasure alg ν)
  exact (h_id.comp (u := fun (f : ℕ → α → ℕ × ℝ) a ↦ (f T a).1) (by fun_prop)).ae_snd
    MeasurableSet.of_discrete h

/-- **Large deviations of the empirical means under static allocations** [D23, Theorem 12], for
any laws of the arms. Let the laws of the empirical means of `m` independent samples of `ν a`
satisfy the large deviation principle with good rate function `I a`, and let `w a > 0`. If the
numbers of pulls after `T` rounds of the algorithms `alg T` satisfy `|N_{T,a} - T w a| ≤ k` almost
surely, then the laws of the vectors of the empirical means after `T` rounds satisfy the large
deviation principle with speed `T` and rate function
`x ↦ ∑ a, w a I a (x a)`.

In the array model, the empirical mean of the arm `a` is the mean of the first `N_{T,a}` entries
of its row. The upper bound is a union over the `(2 k + 1)^K` possible numbers of pulls
(`exists_eventually_streamMeasure_mean_mem_le`), and the lower bound asks the means of the rows to
be close to the target for all of them (`exists_eventually_le_streamMeasure_forall_mean_mem`). -/
lemma isLDP_empMean_of_abs_pullCount_sub_le
    (hP : ∀ a, IsLDP (fun m ↦ (Measure.pi fun _ : Fin m ↦ ν a).map
      fun z ↦ (∑ i, z i) / (m : ℝ)) (I a))
    (hI : ∀ a, IsGoodRateFunction (I a)) (hw : ∀ a, 0 < w a) (k : ℕ)
    {alg : ℕ → Algorithm Unit α ℝ}
    (h_pull : ∀ T, ∀ᵐ h ∂(trajMeasure (alg T) (Environment.bandit ν)),
      ∀ a, |(pullCount IT.action a T h : ℝ) - T * w a| ≤ k) :
    IsLDP (fun T ↦ (trajMeasure (alg T) (Environment.bandit ν)).map
        fun h a ↦ empMean IT.action IT.feedback a T h)
      fun x ↦ ∑ a, ENNReal.ofReal (w a) * I a (x a) := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure ((alg 0).policyZero ())
  simp_rw [trajMeasure_map_empMean]
  have h_ae (T : ℕ) : ∀ᵐ ω ∂(ArrayModel.arrayMeasure ν),
      ∀ a, |(pullCount (ArrayModel.action (alg T)) a T ω : ℝ) - T * w a| ≤ k :=
    ae_arrayMeasure_pullCount (alg T) T (p := fun n ↦ ∀ a, |(n a : ℝ) - T * w a| ≤ k) (h_pull T)
  have h_mean (T : ℕ) (ω : ArrayModel.ProbSpace α ℝ) (a : α) :
      empMean (ArrayModel.action (alg T)) (ArrayModel.reward (alg T)) a T ω =
        (∑ i ∈ range (pullCount (ArrayModel.action (alg T)) a T ω), ω.2 i a) /
          (pullCount (ArrayModel.action (alg T)) a T ω : ℝ) := by
    rw [empMean, ArrayModel.sumRewards_eq]
  have h_prod (S : Set (ℕ → α → ℝ)) :
      ArrayModel.arrayMeasure ν (Prod.snd ⁻¹' S) = streamMeasure ν S := by
    rw [ArrayModel.arrayMeasure, ← Set.univ_prod, Measure.prod_prod, measure_univ, one_mul]
  refine IsLDP.of_isClosed_of_mem_nhds (isGoodRateFunction_sum_mul hI hw).1
    (fun F hF ↦ ?_) (fun x U hU ↦ ?_)
  · refine limsup_log_div_le_neg_of_le_mul_exp fun r hr ↦ ?_
    obtain ⟨C, hC, hev⟩ := exists_eventually_streamMeasure_mean_mem_le hP hI hw k hF hr
    refine ⟨Fintype.card (α → Fin (2 * k + 1)) * C,
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hC, ?_⟩
    filter_upwards [hev] with T hT
    rw [Measure.map_apply (by fun_prop) hF.measurableSet]
    set n₀ : α → ℕ := fun a ↦ ⌈T * w a - k⌉₊
    have hn₀ (a : α) : T * w a - k ≤ n₀ a := Nat.le_ceil _
    calc ArrayModel.arrayMeasure ν ((fun ω a ↦
          empMean (ArrayModel.action (alg T)) (ArrayModel.reward (alg T)) a T ω) ⁻¹' F)
        ≤ ArrayModel.arrayMeasure ν (Prod.snd ⁻¹' ⋃ d : α → Fin (2 * k + 1),
          {y | (fun a ↦ (∑ i ∈ range (n₀ a + d a), y i a) / ((n₀ a + d a : ℕ) : ℝ)) ∈ F}) := by
          refine measure_mono_ae ?_
          filter_upwards [h_ae T] with ω hω hωF
          simp only [Set.mem_preimage, h_mean] at hωF
          set n := fun a ↦ pullCount (ArrayModel.action (alg T)) a T ω
          have hlo (a : α) : n₀ a ≤ n a := Nat.ceil_le.2 (by linarith [(abs_le.1 (hω a)).1])
          have hhi (a : α) : n a - n₀ a < 2 * k + 1 := by
            have h1 : (n a : ℝ) ≤ n₀ a + 2 * k := by linarith [(abs_le.1 (hω a)).2, hn₀ a]
            have h2 : n a ≤ n₀ a + 2 * k := by exact_mod_cast h1
            omega
          refine Set.mem_iUnion.2 ⟨fun a ↦ ⟨n a - n₀ a, hhi a⟩, ?_⟩
          simp only [Set.mem_ofPred_eq, Nat.add_sub_cancel' (hlo _)]
          exact hωF
    _ = streamMeasure ν (⋃ d : α → Fin (2 * k + 1),
          {y | (fun a ↦ (∑ i ∈ range (n₀ a + d a), y i a) / ((n₀ a + d a : ℕ) : ℝ)) ∈ F}) :=
        h_prod _
    _ ≤ ∑ d : α → Fin (2 * k + 1), streamMeasure ν
          {y | (fun a ↦ (∑ i ∈ range (n₀ a + d a), y i a) / ((n₀ a + d a : ℕ) : ℝ)) ∈ F} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _d : α → Fin (2 * k + 1), C * ENNReal.ofReal (Real.exp (-(T * r))) :=
        Finset.sum_le_sum fun d _ ↦ hT (fun a ↦ n₀ a + d a) fun a ↦ by
          push_cast
          linarith [hn₀ a, (d a : ℕ).cast_nonneg (α := ℝ)]
    _ = Fintype.card (α → Fin (2 * k + 1)) * C * ENNReal.ofReal (Real.exp (-(T * r))) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_assoc]
  · refine neg_le_liminf_log_div_of_mul_exp_le fun r hr ↦ ?_
    obtain ⟨C, hC, hev⟩ := exists_eventually_le_streamMeasure_forall_mean_mem hP hw k hU hr
    refine ⟨C, hC, ?_⟩
    filter_upwards [hev] with T hT
    refine hT.trans ?_
    rw [← h_prod]
    refine (measure_mono_ae ?_).trans (Measure.le_map_apply (by fun_prop) U)
    filter_upwards [h_ae T] with ω hω hS
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hS ⊢
    simp only [h_mean]
    exact hS _ hω

/-- **Cramér's theorem under static allocations** [D23, Theorem 12], for any laws of the arms
with exponential moments. If the cumulant generating function of each arm `ν a` is finite on a
neighbourhood of `0`, `w a > 0`, and the numbers of pulls after `T` rounds of the algorithms
`alg T` satisfy `|N_{T,a} - T w a| ≤ k` almost surely, then the laws of the vectors of the
empirical means after `T` rounds satisfy the large deviation principle with speed `T` and the good
rate function `x ↦ ∑ a, w a I_a(x a)`, with `I_a` the Cramér rate function of `ν a`. -/
lemma isLDP_empMean_rateFunction_of_abs_pullCount_sub_le
    (hν : ∀ a, 0 ∈ interior (integrableExpSet id (ν a))) (hw : ∀ a, 0 < w a) (k : ℕ)
    {alg : ℕ → Algorithm Unit α ℝ}
    (h_pull : ∀ T, ∀ᵐ h ∂(trajMeasure (alg T) (Environment.bandit ν)),
      ∀ a, |(pullCount IT.action a T h : ℝ) - T * w a| ≤ k) :
    IsLDP (fun T ↦ (trajMeasure (alg T) (Environment.bandit ν)).map
        fun h a ↦ empMean IT.action IT.feedback a T h)
        (fun x ↦ ∑ a, ENNReal.ofReal (w a) * rateFunction id (ν a) (x a)) ∧
      IsGoodRateFunction fun x : α → ℝ ↦
        ∑ a, ENNReal.ofReal (w a) * rateFunction id (ν a) (x a) := by
  have hI (a : α) := isGoodRateFunction_rateFunction (hν a)
  exact ⟨isLDP_empMean_of_abs_pullCount_sub_le
    (fun a ↦ isLDP_cramer (integrable_of_mem_interior_integrableExpSet (hν a))) hI hw k h_pull,
    isGoodRateFunction_sum_mul hI hw⟩

end Bandit

end LMLExplore.Bandits
