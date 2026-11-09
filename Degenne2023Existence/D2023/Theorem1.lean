/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Theorem12

/-!
# Theorem 1 of [D23]: the rate of static proportions algorithms

For arms in one-parameter exponential families and a task satisfying Assumption 1, a static
proportions algorithm with proportions `w` has rate
`lim_T h_{μ,T}(𝒜) = (inf_{λ ∈ Alt(μ)} ∑ a, w a KL(λ_a, μ_a))⁻¹` at every admissible model `μ`, and
the oracle difficulty of the class of static proportions algorithms is the static-proportions
difficulty `(max_{w ∈ Δ_K} inf_{λ ∈ Alt(μ)} ∑ a, w a KL(λ_a, μ_a))⁻¹`.

The paper extends the correct answer function `i*` arbitrarily outside `𝒟` and lets static
proportions algorithms recommend `i*(μ̂_T)`. The rate formula fails for some extensions (erratum
E1 of `notes/paper-errata.md`): with Bernoulli arms, the empirical means can be a vector of
`{0, 1}^K` that is a limit of models with a single answer, at which the extension may give another
answer. The per-algorithm statement assumes that the recommendation rule gives the answer `i` at
the vectors of means of the closure of the families that are not limits of alternatives to `i`.
The class `staticClass` contains the static proportions algorithms with every recommendation rule
correct on `𝒟`, and its oracle difficulty is not affected. The paper also uses that the empirical
means lie in the closure of the means of the families (erratum E2), an assumption here.

The two statements below, as frozen at the end of phase 1, are false: they do not assume that the
singletons of the answer type `ℐ` are measurable, and for the trivial σ-algebra on `ℐ` the
probability of error, an outer measure, is `1` for every algorithm
(`notes/statement-corrections.md`, Theorems 1 and 5). They are blocked until the user decides.
`tendsto_errorRate_of_isStaticProportions_of_measurableSet` proves the first one when the set of
correct answers of the model is measurable.

The proof of `tendsto_errorRate_of_isStaticProportions_of_measurableSet` follows the paper's: the
family errs when the empirical means are an alternative, an open set by Assumption 1, which gives
the lower bound of the large deviation principle of Theorem 12; it errs only when the empirical
means are a limit of alternatives or outside the closure of the means (the latter does not happen
for `T` large, since the samples lie in the closure of the means), which gives the upper bound by
the continuity of the rate function on the closure of the means. The closure and interior
conditions of Assumption 1 are not used.

## Main statements

* `Degenne2023Existence.tendsto_errorRate_of_isStaticProportions_of_measurableSet`:
  [D23, Theorem 1], when the set of correct answers of the model is measurable.
* `Degenne2023Existence.eventually_errorProb_le_of_isStaticProportions`: [D23, proof of Theorem 1],
  the error event within the closure of the vectors of means.
* `Degenne2023Existence.tendsto_errorRate_of_isStaticProportions`: [D23, Theorem 1].
* `Degenne2023Existence.oracleDifficulty_staticClass`: [D23, Theorem 1], the oracle difficulty
  of the class of static proportions algorithms.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
-/

@[expose] public section

open MeasureTheory Filter Topology Learning LMLExplore LMLExplore.Identification

open scoped ENNReal

namespace Degenne2023Existence

variable {α ℐ : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] [MeasurableSpace ℐ] [Finite ℐ]
  {task : IdentTask α (α → ℝ) ℐ ℝ} {ρ : α → Measure ℝ}

omit [Finite ℐ] in
/-- **The error event of a static proportions algorithm**, the upper half of the proof of
[D23, Theorem 1]. With samples in the closure of the means of the families, a recommendation rule
as in `tendsto_errorRate_of_isStaticProportions_of_measurableSet`, and an admissible model `μ`
with the single correct answer `i`, for `T` large the probability of error is at most the
probability that the empirical means are a limit of alternatives to `i` within the closure of the
vectors of means: every arm is then pulled, and its empirical mean is in the closure of its means.
-/
lemma eventually_errorProb_le_of_isStaticProportions
    (hρ_closure : ∀ a, ∀ᵐ x ∂(ρ a), x ∈ closure ((ρ a).expFamilyMeans id))
    (hν : ∀ μ a, μ a ∈ (ρ a).expFamilyMeans id →
      task.ν μ a = (ρ a).expFamily id ((ρ a).natParam id (μ a)))
    (hM : task.M ⊆ {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id}) {rec : (α → ℝ) → ℐ}
    (hrec : ∀ i, ∀ x ∈ closure {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id},
      x ∉ closure (task.alt i) → rec x = i)
    {𝒜 : ℕ → IdentAlg Unit α ℝ ℐ} {w : α → ℝ} (h𝒜 : task.IsStaticProportions rec 𝒜 w)
    {μ : α → ℝ} (hμ : μ ∈ task.M) (hμc : MeasurableSet (task.correct μ)) {i : ℐ}
    (hi : task.correct μ = {i}) :
    ∀ᶠ T : ℕ in atTop, task.errorProb 𝒜 μ T ≤
      (trajMeasure (𝒜 T).alg (Environment.bandit (task.ν μ))).map
        (fun h a ↦ empMean IT.action IT.feedback a T h)
        (closure {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id} ∩ closure (task.alt i)) := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure ((𝒜 0).alg.policyZero ())
  set S := {μ : α → ℝ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id}
  have hμS : μ ∈ S := hM hμ
  have hC : closure S = Set.univ.pi fun a ↦ closure ((ρ a).expFamilyMeans id) := by
    rw [show S = Set.univ.pi fun a ↦ (ρ a).expFamilyMeans id by ext; simp [S], closure_pi_set]
  -- For `T` large, every arm is pulled and the empirical means lie in the closure of the means.
  have hpos : ∀ᶠ T : ℕ in atTop, ∀ a, (Fintype.card α : ℝ) < T * w a :=
    eventually_all.2 fun a ↦ (tendsto_natCast_atTop_atTop.atTop_mul_const (h𝒜.1 a))
      |>.eventually_gt_atTop _
  filter_upwards [hpos] with T hT
  have hν' (a : α) : ∀ᵐ x ∂(task.ν μ a), x ∈ closure ((ρ a).expFamilyMeans id) := by
    rw [hν μ a (hμS a)]
    exact (Measure.expFamily_absolutelyContinuous (ρ a) id _).ae_le (hρ_closure a)
  have hmem := Bandits.ae_empMean_mem (fun a ↦ (Measure.convex_expFamilyMeans).closure)
    (fun a ↦ isClosed_closure.measurableSet) hν' (𝒜 T).alg T
  have h_in : (trajMeasure (𝒜 T).alg (Environment.bandit (task.ν μ)))
      ((fun h a ↦ empMean IT.action IT.feedback a T h) ⁻¹' (closure S)ᶜ) = 0 := by
    refine ae_iff.1 ?_
    filter_upwards [hmem, (h𝒜.2.2 T).2.1 μ hμ] with h hh hN
    rw [hC]
    refine fun a _ ↦ hh a fun h0 ↦ ?_
    have := (abs_le.1 (hN a)).1
    rw [h0, Nat.cast_zero] at this
    linarith [hT a]
  -- The family errs only when the empirical means are a limit of alternatives to `i`, or outside
  -- the closure of the means.
  rw [h𝒜.errorProb_eq hμc, Measure.map_apply (by fun_prop)
    (isClosed_closure.inter isClosed_closure).measurableSet]
  calc _ ≤ (trajMeasure (𝒜 T).alg (Environment.bandit (task.ν μ)))
        ((fun h a ↦ empMean IT.action IT.feedback a T h) ⁻¹' (closure S ∩ closure (task.alt i)) ∪
          (fun h a ↦ empMean IT.action IT.feedback a T h) ⁻¹' (closure S)ᶜ) := by
        refine measure_mono fun h hh ↦ ?_
        by_cases hC' : (fun a ↦ empMean IT.action IT.feedback a T h) ∈ closure S
        · refine Or.inl ⟨hC', not_not.1 fun hcl ↦ hh ?_⟩
          rw [hrec i _ hC' hcl, hi]
          rfl
        · exact Or.inr hC'
    _ ≤ _ := (measure_union_le _ _).trans (by rw [h_in, add_zero])

omit [Finite ℐ] in
/-- **The rate of a static proportions algorithm** [D23, Theorem 1], when the set of correct answers
of the model is measurable. Let the arm `a` belong to the exponential family generated by `ρ a`
with the statistic `id`, not almost everywhere constant and with samples in the closure of its
means, and let the task satisfy Assumption 1 and have a single correct answer on every admissible
model. Let `𝒜` be a static proportions algorithm with proportions `w` and a recommendation rule
`rec` that answers `i` at every vector of the closure of the vectors of means of the families that
is not a limit of alternatives to `i`. Then at every admissible model `μ` whose set of correct
answers is measurable,
`h_{μ,T}(𝒜) → (inf_{λ ∈ Alt(μ)} ∑ a, w a KL(ν_a(λ), ν_a(μ)))⁻¹`.

The proof uses neither the finiteness of the answers nor the closure and interior conditions of
Assumption 1, only that the answer sets are open. -/
lemma tendsto_errorRate_of_isStaticProportions_of_measurableSet
    (hρ : ∀ a c, ¬ id =ᵐ[ρ a] fun _ ↦ c)
    (hρ_closure : ∀ a, ∀ᵐ x ∂(ρ a), x ∈ closure ((ρ a).expFamilyMeans id))
    (hν : ∀ μ a, μ a ∈ (ρ a).expFamilyMeans id →
      task.ν μ a = (ρ a).expFamily id ((ρ a).natParam id (μ a)))
    (hreg : IsRegular task {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id})
    (hsingle : task.IsSingleAnswer) {rec : (α → ℝ) → ℐ}
    (hrec : ∀ i, ∀ x ∈ closure {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id},
      x ∉ closure (task.alt i) → rec x = i)
    {𝒜 : ℕ → IdentAlg Unit α ℝ ℐ} {w : α → ℝ} (h𝒜 : task.IsStaticProportions rec 𝒜 w)
    {μ : α → ℝ} (hμ : μ ∈ task.M) (hμc : MeasurableSet (task.correct μ)) :
    Tendsto (task.errorRate 𝒜 μ) atTop (𝓝 (⨅ μ' ∈ task.alternatives μ, task.cost w μ' μ)⁻¹) := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure ((𝒜 0).alg.policyZero ())
  rw [IdentTask.isSingleAnswer_iff] at hsingle
  obtain ⟨i, hi⟩ := hsingle μ hμ
  set S := {μ : α → ℝ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id}
  set J : (α → ℝ) → ℝ≥0∞ := fun x ↦ ∑ a, ENNReal.ofReal (w a) * (ρ a).expFamilyRate id (x a) (μ a)
  set L := ⨅ μ' ∈ task.alternatives μ, task.cost w μ' μ
  have hμS : μ ∈ S := hreg.M_subset hμ
  obtain ⟨hLDP, -⟩ := isLDP_empMean_of_isStaticProportions hν h𝒜 hμ hμS
  -- On the vectors of means, the rate function is the cost.
  have hJ (μ' : α → ℝ) (hμ' : μ' ∈ S) : J μ' = task.cost w μ' μ := by
    rw [IdentTask.cost_def]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [hν μ' a (hμ' a), hν μ a (hμS a), Measure.klDiv_expFamily_natParam (hμ' a) (hμS a),
      Measure.expFamilyRate_eq_ofReal_expFamilyDiv (hμ' a) (hμS a)]
  -- The alternatives to `μ` are the alternatives to `i`, the union of the answer sets of the
  -- other answers, which is open.
  have halt : task.alternatives μ = task.alt i := task.alternatives_eq_alt hi
  have halt_eq : task.alternatives μ = ⋃ j ∈ {j | j ≠ i}, task.answerSet j := by
    ext μ'
    rw [halt]
    simp only [IdentTask.mem_alt_iff, Set.mem_iUnion, IdentTask.mem_answerSet_iff,
      Set.mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨hμ', h⟩
      obtain ⟨j, hj⟩ := hsingle μ' hμ'
      refine ⟨j, fun hji ↦ h (hji ▸ hj ▸ rfl), hμ', hj ▸ rfl⟩
    · rintro ⟨j, hji, hμ', hj⟩
      obtain ⟨k, hk⟩ := hsingle μ' hμ'
      rw [hk, Set.mem_singleton_iff] at hj
      subst hj
      exact ⟨hμ', by rw [hk, Set.mem_singleton_iff]; exact Ne.symm hji⟩
  have hU_open : IsOpen (task.alternatives μ) := by
    rw [halt_eq]
    exact isOpen_biUnion fun j _ ↦ hreg.isOpen_answerSet j
  -- The lower bound: the family errs when the empirical means are an alternative.
  have h_lower : -(L : EReal) ≤
      liminf (fun T : ℕ ↦ ENNReal.log (task.errorProb 𝒜 μ T) / T) atTop := by
    have h1 := hLDP.neg_iInf_interior_le_liminf (task.alternatives μ)
    rw [hU_open.interior_eq] at h1
    have h2 : (⨅ x ∈ task.alternatives μ, J x) = L :=
      iInf_congr fun μ' ↦ iInf_congr fun hμ' ↦ hJ μ' (hreg.M_subset hμ'.1)
    rw [h2] at h1
    refine h1.trans (liminf_le_liminf (Eventually.of_forall fun T ↦ ?_))
    refine EReal.div_le_div_right_of_nonneg (by exact_mod_cast T.cast_nonneg)
      (ENNReal.log_monotone ?_)
    rw [h𝒜.errorProb_eq hμc, Measure.map_apply (by fun_prop) hU_open.measurableSet]
    refine measure_mono fun h hh ↦ ?_
    simp only [Set.mem_preimage] at hh
    rw [halt_eq] at hh
    obtain ⟨j, hji, hj⟩ := Set.mem_iUnion₂.1 hh
    -- At a model with answer `j`, which is not a limit of alternatives to `j`, `rec` answers `j`.
    have hdisj : Disjoint (task.answerSet j) (closure (task.alt j)) :=
      (Set.disjoint_left.2 fun x (hx : x ∈ task.answerSet j) (hx' : x ∈ task.alt j) ↦
        (task.mem_alt_iff.1 hx').2 (task.mem_answerSet_iff.1 hx).2).closure_right
        (hreg.isOpen_answerSet j)
    have hrecj : rec (fun a ↦ empMean IT.action IT.feedback a T h) = j :=
      hrec j _ (subset_closure (hreg.M_subset (task.mem_answerSet_iff.1 hj).1))
        (Set.disjoint_left.1 hdisj hj)
    change rec _ ∉ task.correct μ
    rw [hrecj, hi, Set.mem_singleton_iff]
    exact hji
  -- The upper bound: the family errs only when the empirical means are a limit of alternatives,
  -- or outside the closure of the means.
  have hC : closure S = Set.univ.pi fun a ↦ closure ((ρ a).expFamilyMeans id) := by
    rw [show S = Set.univ.pi fun a ↦ (ρ a).expFamilyMeans id by ext; simp [S], closure_pi_set]
  set F := closure S ∩ closure (task.alt i)
  have hF : IsClosed F := isClosed_closure.inter isClosed_closure
  have hJ_cont : ContinuousOn J (closure S) := by
    refine continuousOn_finsetSum _ fun a _ ↦ ?_
    refine (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_continuousOn ?_
    refine (Measure.continuousOn_expFamilyRate_left (hρ a) (hμS a)).comp
      (continuous_apply a).continuousOn fun x hx ↦ ?_
    rw [hC] at hx
    exact hx a (Set.mem_univ a)
  -- The rate function is at least `L` at the limits of alternatives, by continuity.
  have hJF : L ≤ ⨅ x ∈ F, J x := by
    refine le_iInf₂ fun x hx ↦ ?_
    have hsub : task.alternatives μ ⊆ closure S :=
      fun μ' hμ' ↦ subset_closure (hreg.M_subset hμ'.1)
    have h1 := ((hJ_cont x hx.1).mono hsub).mem_closure_image (halt ▸ hx.2)
    have h2 : J '' task.alternatives μ ⊆ Set.Ici L := by
      rintro _ ⟨μ', hμ', rfl⟩
      rw [Set.mem_Ici, hJ μ' (hreg.M_subset hμ'.1)]
      exact iInf₂_le μ' hμ'
    exact closure_minimal h2 isClosed_Ici h1
  have h_upper : limsup (fun T : ℕ ↦ ENNReal.log (task.errorProb 𝒜 μ T) / T) atTop ≤
      -(L : EReal) := by
    have h1 := hLDP.limsup_le_neg_iInf_closure F
    rw [hF.closure_eq] at h1
    refine le_trans ?_ (h1.trans (EReal.neg_le_neg_iff.2
      (EReal.coe_ennreal_le_coe_ennreal_iff.2 hJF)))
    refine limsup_le_limsup ((eventually_errorProb_le_of_isStaticProportions hρ_closure hν
      hreg.M_subset hrec h𝒜 hμ hμc hi).mono fun T hT ↦ ?_)
    exact EReal.div_le_div_right_of_nonneg (by exact_mod_cast T.cast_nonneg)
      (ENNReal.log_monotone hT)
  exact IdentTask.tendsto_errorRate_of_tendsto_log_div task
    (tendsto_of_le_liminf_of_limsup_le h_lower h_upper)

/-- **The rate of a static proportions algorithm** [D23, Theorem 1]. Let the arm `a` belong to
the exponential family generated by `ρ a` with the statistic `id`, not almost everywhere constant
and with samples in the closure of its means, and let the task satisfy Assumption 1 and have a
single correct answer on every admissible model. Let `𝒜` be a static proportions algorithm with
proportions `w` and a recommendation rule `rec` that answers `i` at every vector of the closure of
the vectors of means of the families that is not a limit of alternatives to `i`. Then at every
admissible model `μ`,
`h_{μ,T}(𝒜) → (inf_{λ ∈ Alt(μ)} ∑ a, w a KL(ν_a(λ), ν_a(μ)))⁻¹`. -/
theorem tendsto_errorRate_of_isStaticProportions (hρ : ∀ a c, ¬ id =ᵐ[ρ a] fun _ ↦ c)
    (hρ_closure : ∀ a, ∀ᵐ x ∂(ρ a), x ∈ closure ((ρ a).expFamilyMeans id))
    (hν : ∀ μ a, μ a ∈ (ρ a).expFamilyMeans id →
      task.ν μ a = (ρ a).expFamily id ((ρ a).natParam id (μ a)))
    (hreg : IsRegular task {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id})
    (hsingle : task.IsSingleAnswer) {rec : (α → ℝ) → ℐ}
    (hrec : ∀ i, ∀ x ∈ closure {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id},
      x ∉ closure (task.alt i) → rec x = i)
    {𝒜 : ℕ → IdentAlg Unit α ℝ ℐ} {w : α → ℝ} (h𝒜 : task.IsStaticProportions rec 𝒜 w)
    {μ : α → ℝ} (hμ : μ ∈ task.M) :
    Tendsto (task.errorRate 𝒜 μ) atTop (𝓝 (⨅ μ' ∈ task.alternatives μ, task.cost w μ' μ)⁻¹) := by
  sorry

/-- **The oracle difficulty of static proportions algorithms** [D23, Theorem 1]. With arms in
exponential families as in `tendsto_errorRate_of_isStaticProportions` and a task satisfying
Assumption 1 with a single correct answer on every admissible model, the oracle difficulty of the
class of static proportions algorithms at every admissible model `μ` is the static-proportions
difficulty `H^{sp}(μ) = (max_{w ∈ Δ_K} inf_{λ ∈ Alt(μ)} ∑ a, w a KL(ν_a(λ), ν_a(μ)))⁻¹`.

The paper writes the maximum over the positive proportions `Δ_K^0`; the maximum over the simplex
`Δ_K` has the same value. -/
theorem oracleDifficulty_staticClass (hρ : ∀ a c, ¬ id =ᵐ[ρ a] fun _ ↦ c)
    (hρ_closure : ∀ a, ∀ᵐ x ∂(ρ a), x ∈ closure ((ρ a).expFamilyMeans id))
    (hν : ∀ μ a, μ a ∈ (ρ a).expFamilyMeans id →
      task.ν μ a = (ρ a).expFamily id ((ρ a).natParam id (μ a)))
    (hreg : IsRegular task {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id})
    (hsingle : task.IsSingleAnswer) {μ : α → ℝ} (hμ : μ ∈ task.M) :
    task.oracleDifficulty task.staticClass μ = task.staticDifficulty μ := by
  sorry

end Degenne2023Existence
