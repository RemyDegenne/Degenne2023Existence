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

The two headline statements assume that the singletons of the answer type `ℐ` are measurable: the
paper's answers are a finite set of indices, every subset of which is an event. Without it they are
false: for the trivial σ-algebra on `ℐ` the probability of error, an outer measure, is `1` for
every algorithm (`notes/statement-corrections.md`, Theorems 1 and 5; the hypothesis was added by
the decision of 2026-11-11). `tendsto_errorRate_of_isStaticProportions_of_measurableSet` assumes
only that the set of correct answers of the model is measurable.

The proof of `tendsto_errorRate_of_isStaticProportions_of_measurableSet` follows the paper's: the
family errs when the empirical means are an alternative, an open set by Assumption 1, which gives
the lower bound of the large deviation principle of Theorem 12; it errs only when the empirical
means are a limit of alternatives or outside the closure of the means (the latter does not happen
for `T` large, since the samples lie in the closure of the means), which gives the upper bound by
the continuity of the rate function on the closure of the means. The closure and interior
conditions of Assumption 1 are not used.

The oracle difficulty of the class follows: every family of the class has a rate at least
`(inf_{λ ∈ Alt(μ)} ∑ a, w a KL(λ_a, μ_a))⁻¹` by the lower bound alone, which holds for every
recommendation rule correct on `𝒟`; for every positive `w`, the static proportions family of
cumulative tracking with the measurable recommendation rule of `exists_measurable_rec` attains it;
and the supremum over the positive proportions is the supremum over the simplex. The existence of
that rule is where the condition of Assumption 1 that the closures of the answer sets cover the
vectors of means, and the finiteness of the answers, are used.

## Main statements

* `Degenne2023Existence.exists_measurable_rec`: [D23, proof of Theorem 1], a measurable
  recommendation rule as in Theorem 1, correct on `𝒟` (`rec_mem_correct`).
* `Degenne2023Existence.neg_le_liminf_log_errorProb_of_isStaticProportions`:
  [D23, proof of Theorem 1], the lower bound on the probability of error.
* `Degenne2023Existence.tendsto_errorRate_of_isStaticProportions_of_measurableSet`:
  [D23, Theorem 1], when the set of correct answers of the model is measurable.
* `Degenne2023Existence.eventually_errorProb_le_of_isStaticProportions`: [D23, proof of Theorem 1],
  the error event within the closure of the vectors of means.
* `Degenne2023Existence.tendsto_errorRate_of_isStaticProportions`: [D23, Theorem 1].
* `Degenne2023Existence.staticDifficulty_le_oracleDifficulty_staticClass`,
  `Degenne2023Existence.oracleDifficulty_staticClass_le`: [D23, proof of Theorem 1], the two
  inequalities between the oracle difficulty of static proportions and the static-proportions
  difficulty, when the set of correct answers of the model is measurable.
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

omit [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] [MeasurableSpace ℐ] [Finite ℐ] in
/-- Under Assumption 1 with a single correct answer on the admissible models, a recommendation rule
that answers `i` at every vector of the closure of `S` that is not a limit of alternatives to `i`
is correct on the admissible models: an admissible model with answer `i` lies in the open set
`𝒟_i`, which does not meet the closure of the alternatives to `i`. -/
lemma rec_mem_correct {S : Set (α → ℝ)} (hreg : IsRegular task S)
    (hsingle : task.IsSingleAnswer) {rec : (α → ℝ) → ℐ}
    (hrec : ∀ i, ∀ x ∈ closure S, x ∉ closure (task.alt i) → rec x = i) {μ : α → ℝ}
    (hμ : μ ∈ task.M) :
    rec μ ∈ task.correct μ := by
  obtain ⟨i, hi⟩ := task.isSingleAnswer_iff.1 hsingle μ hμ
  have hμi : μ ∈ task.answerSet i :=
    task.mem_answerSet_iff.2 ⟨hμ, by rw [hi]; exact Set.mem_singleton i⟩
  have hdisj : Disjoint (task.answerSet i) (closure (task.alt i)) :=
    (task.disjoint_alt_answerSet i).symm.closure_right (hreg.isOpen_answerSet i)
  rw [hrec i μ (subset_closure (hreg.M_subset hμ)) (Set.disjoint_left.1 hdisj hμi), hi]
  exact Set.mem_singleton i

omit [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] [MeasurableSpace ℐ] in
/-- Under Assumption 1 with finitely many answers and a single correct answer on the admissible
models, at a vector of the closure of `S` at most one answer `i` is such that the vector is not a
limit of alternatives to `i`: the vector is a limit of models of some `𝒟_k`, which are
alternatives to every answer other than `k`. -/
lemma eq_of_notMem_closure_alt {S : Set (α → ℝ)} (hreg : IsRegular task S)
    (hsingle : task.IsSingleAnswer) {x : α → ℝ} (hx : x ∈ closure S) {i j : ℐ}
    (hi : x ∉ closure (task.alt i)) (hj : x ∉ closure (task.alt j)) :
    i = j := by
  have hcl : closure S ⊆ ⋃ k, closure (task.answerSet k) :=
    closure_minimal hreg.subset_iUnion_closure
      (isClosed_iUnion_of_finite fun _ ↦ isClosed_closure)
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hcl hx)
  have hsub {l : ℐ} (hl : x ∉ closure (task.alt l)) : k = l := by
    by_contra hkl
    refine hl (closure_mono (fun y hy ↦ ?_) hk)
    have hy' := task.mem_answerSet_iff.1 hy
    exact (hsingle.mem_alt_iff hy'.1 hy'.2).2 (Ne.symm hkl)
  exact (hsub hi).symm.trans (hsub hj)

omit [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] in
/-- **A measurable recommendation rule for static proportions** [D23, proof of Theorem 1]. Under
Assumption 1 with finitely many answers and a single correct answer on the admissible models,
some measurable recommendation rule answers `i` at every vector of the closure of `S` that is not
a limit of alternatives to `i`: there is at most one such answer at each vector
(`eq_of_notMem_closure_alt`), and the sets of the vectors with a given such answer are Borel. By
`rec_mem_correct`, the rule is correct on the admissible models. -/
lemma exists_measurable_rec [Countable α] [Nonempty ℐ] {S : Set (α → ℝ)} (hreg : IsRegular task S)
    (hsingle : task.IsSingleAnswer) :
    ∃ rec : (α → ℝ) → ℐ, Measurable rec ∧
      ∀ i, ∀ x ∈ closure S, x ∉ closure (task.alt i) → rec x = i := by
  classical
  set P : (α → ℝ) → ℐ → Prop := fun x i ↦ x ∈ closure S ∧ x ∉ closure (task.alt i)
  set i₀ : ℐ := Classical.arbitrary ℐ
  set rec : (α → ℝ) → ℐ := fun x ↦ if h : ∃ i, P x i then h.choose else i₀
  have hrec (i : ℐ) (x : α → ℝ) (hx : P x i) : rec x = i := by
    simp only [rec]
    split_ifs with h
    · exact eq_of_notMem_closure_alt hreg hsingle hx.1 h.choose_spec.2 hx.2
    · exact absurd ⟨i, hx⟩ h
  refine ⟨rec, measurable_to_countable' fun i ↦ ?_, fun i x hx hxi ↦ hrec i x ⟨hx, hxi⟩⟩
  have hP (j : ℐ) : MeasurableSet {x | P x j} :=
    isClosed_closure.measurableSet.inter isClosed_closure.measurableSet.compl
  have heq : rec ⁻¹' {i} = {x | P x i} ∪ ((⋃ j, {x | P x j})ᶜ ∩ {_x | i₀ = i}) := by
    ext x
    by_cases h : ∃ j, P x j
    · obtain ⟨j, hj⟩ := h
      have hx : x ∈ ⋃ j, {x | P x j} := Set.mem_iUnion.2 ⟨j, hj⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_ofPred_eq,
        Set.mem_inter_iff, Set.mem_compl_iff, hx, not_true_eq_false, false_and, or_false,
        hrec j x hj]
      exact ⟨fun hji ↦ hji ▸ hj, fun hi ↦ eq_of_notMem_closure_alt hreg hsingle hj.1 hj.2 hi.2⟩
    · have hx : x ∉ ⋃ j, {x | P x j} := by simpa using h
      have hi : ¬ P x i := fun hi ↦ h ⟨i, hi⟩
      have hx₀ : rec x = i₀ := by
        simp only [rec]
        split_ifs
        rfl
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_ofPred_eq,
        Set.mem_inter_iff, Set.mem_compl_iff, hx, hi, not_false_eq_true, true_and, false_or, hx₀]
  rw [heq]
  exact (hP i).union ((MeasurableSet.iUnion hP).compl.inter (MeasurableSet.const _))

omit [Finite ℐ] in
/-- **The lower bound on the probability of error of static proportions** [D23, proof of
Theorem 1]. Let the arm `a` belong to the exponential family generated by `ρ a` with the statistic
`id`, and let the task satisfy Assumption 1 and have a single correct answer on every admissible
model. Let `𝒜` be a static proportions algorithm with proportions `w` and a recommendation rule
correct on the admissible models. At every admissible model `μ` whose set of correct answers is
measurable, `-inf_{λ ∈ Alt(μ)} ∑ a, w a KL(ν_a(λ), ν_a(μ)) ≤ liminf_T (1 / T) log p_{μ,T}(𝒜)`:
the family errs when the empirical means are an alternative to `μ`, an open set, and the lower
bound of the large deviation principle of Theorem 12 applies.

The proof uses from Assumption 1 only that the admissible models are vectors of means of the
families and that the answer sets are open. -/
lemma neg_le_liminf_log_errorProb_of_isStaticProportions
    (hν : ∀ μ a, μ a ∈ (ρ a).expFamilyMeans id →
      task.ν μ a = (ρ a).expFamily id ((ρ a).natParam id (μ a)))
    (hreg : IsRegular task {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id})
    (hsingle : task.IsSingleAnswer) {rec : (α → ℝ) → ℐ}
    (hrec : ∀ μ ∈ task.M, rec μ ∈ task.correct μ)
    {𝒜 : ℕ → IdentAlg Unit α ℝ ℐ} {w : α → ℝ} (h𝒜 : task.IsStaticProportions rec 𝒜 w)
    {μ : α → ℝ} (hμ : μ ∈ task.M) (hμc : MeasurableSet (task.correct μ)) :
    -((⨅ μ' ∈ task.alternatives μ, task.cost w μ' μ : ℝ≥0∞) : EReal) ≤
      liminf (fun T : ℕ ↦ ENNReal.log (task.errorProb 𝒜 μ T) / T) atTop := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure ((𝒜 0).alg.policyZero ())
  obtain ⟨i, hi⟩ := task.isSingleAnswer_iff.1 hsingle μ hμ
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
  have halt_eq : task.alternatives μ = ⋃ j ∈ {j | j ≠ i}, task.answerSet j := by
    ext μ'
    rw [task.alternatives_eq_alt hi]
    simp only [IdentTask.mem_alt_iff, Set.mem_iUnion, IdentTask.mem_answerSet_iff,
      Set.mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨hμ', h⟩
      obtain ⟨j, hj⟩ := task.isSingleAnswer_iff.1 hsingle μ' hμ'
      refine ⟨j, fun hji ↦ h (hji ▸ hj ▸ rfl), hμ', hj ▸ rfl⟩
    · rintro ⟨j, hji, hμ', hj⟩
      obtain ⟨k, hk⟩ := task.isSingleAnswer_iff.1 hsingle μ' hμ'
      rw [hk, Set.mem_singleton_iff] at hj
      subst hj
      exact ⟨hμ', by rw [hk, Set.mem_singleton_iff]; exact Ne.symm hji⟩
  have hU_open : IsOpen (task.alternatives μ) := by
    rw [halt_eq]
    exact isOpen_biUnion fun j _ ↦ hreg.isOpen_answerSet j
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
  -- At a model with answer `j`, the rule answers `j`.
  have hj' := task.mem_answerSet_iff.1 hj
  have hrecj : rec (fun a ↦ empMean IT.action IT.feedback a T h) = j := by
    have := hrec _ hj'.1
    rwa [hsingle.correct_eq_singleton_of_mem hj'.1 hj'.2, Set.mem_singleton_iff] at this
  change rec _ ∉ task.correct μ
  rw [hrecj, hi, Set.mem_singleton_iff]
  exact hji

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
  obtain ⟨i, hi⟩ := task.isSingleAnswer_iff.1 hsingle μ hμ
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
  have halt : task.alternatives μ = task.alt i := task.alternatives_eq_alt hi
  -- The lower bound: the family errs when the empirical means are an alternative.
  have h_lower : -(L : EReal) ≤
      liminf (fun T : ℕ ↦ ENNReal.log (task.errorProb 𝒜 μ T) / T) atTop :=
    neg_le_liminf_log_errorProb_of_isStaticProportions hν hreg hsingle
      (fun _ hμ' ↦ rec_mem_correct hreg hsingle hrec hμ') h𝒜 hμ hμc
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

omit [Finite ℐ] in
/-- **The rate of a static proportions algorithm** [D23, Theorem 1]. Let the answers have
measurable singletons, let the arm `a` belong to the exponential family generated by `ρ a` with
the statistic `id`, not almost everywhere constant and with samples in the closure of its means,
and let the task satisfy Assumption 1 and have a single correct answer on every admissible model.
Let `𝒜` be a static proportions algorithm with proportions `w` and a recommendation rule `rec`
that answers `i` at every vector of the closure of the vectors of means of the families that is
not a limit of alternatives to `i`. Then at every admissible model `μ`,
`h_{μ,T}(𝒜) → (inf_{λ ∈ Alt(μ)} ∑ a, w a KL(ν_a(λ), ν_a(μ)))⁻¹`.

The statement as frozen at the end of phase 1 assumed finitely many answers, which the proof does
not use. -/
theorem tendsto_errorRate_of_isStaticProportions [MeasurableSingletonClass ℐ]
    (hρ : ∀ a c, ¬ id =ᵐ[ρ a] fun _ ↦ c)
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
  obtain ⟨i, hi⟩ := task.isSingleAnswer_iff.1 hsingle μ hμ
  exact tendsto_errorRate_of_isStaticProportions_of_measurableSet hρ hρ_closure hν hreg hsingle
    hrec h𝒜 hμ (hi ▸ measurableSet_singleton i)

omit [Finite ℐ] in
/-- **The oracle difficulty of static proportions is at least the static-proportions difficulty**
[D23, proof of Theorem 1]. With arms in exponential families and a task as in
`neg_le_liminf_log_errorProb_of_isStaticProportions`, at every admissible model `μ` whose set of
correct answers is measurable, `H^{sp}(μ) ≤ H_{𝒞^{sp}}(μ)`: every family of the class has
proportions `w` in the simplex, and its rate is at least
`(inf_{λ ∈ Alt(μ)} ∑ a, w a KL(ν_a(λ), ν_a(μ)))⁻¹` by the lower bound on its probability of
error. -/
lemma staticDifficulty_le_oracleDifficulty_staticClass
    (hν : ∀ μ a, μ a ∈ (ρ a).expFamilyMeans id →
      task.ν μ a = (ρ a).expFamily id ((ρ a).natParam id (μ a)))
    (hreg : IsRegular task {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id})
    (hsingle : task.IsSingleAnswer) {μ : α → ℝ} (hμ : μ ∈ task.M)
    (hμc : MeasurableSet (task.correct μ)) :
    task.staticDifficulty μ ≤ task.oracleDifficulty task.staticClass μ := by
  refine le_iInf₂ fun 𝒜 ⟨rec, hrec, w, h𝒜⟩ ↦ ?_
  have hw : w ∈ simplex α := mem_simplex_iff.2 ⟨fun a ↦ (h𝒜.1 a).le, h𝒜.2.1⟩
  calc task.staticDifficulty μ ≤ (⨅ μ' ∈ task.alternatives μ, task.cost w μ' μ)⁻¹ :=
        ENNReal.inv_le_inv.2 (le_iSup₂ (f := fun w (_ : w ∈ simplex α) ↦
          ⨅ μ' ∈ task.alternatives μ, task.cost w μ' μ) w hw)
    _ ≤ liminf (task.errorRate 𝒜 μ) atTop :=
        task.inv_le_liminf_errorRate_of_neg_le_liminf
          (neg_le_liminf_log_errorProb_of_isStaticProportions hν hreg hsingle hrec h𝒜 hμ hμc)
    _ ≤ limsup (task.errorRate 𝒜 μ) atTop := liminf_le_limsup

/-- **The oracle difficulty of static proportions is at most the static-proportions difficulty**
[D23, proof of Theorem 1]. With arms in exponential families as in
`tendsto_errorRate_of_isStaticProportions`, a task with finitely many answers satisfying
Assumption 1 with a single correct answer on every admissible model, at every admissible model `μ`
whose set of correct answers is measurable, `H_{𝒞^{sp}}(μ) ≤ H^{sp}(μ)`: for positive proportions
`w`, a static proportions family with proportions `w` and the recommendation rule of
`exists_measurable_rec` (`IdentTask.exists_isStaticProportions`) has rate
`(inf_{λ ∈ Alt(μ)} ∑ a, w a KL(ν_a(λ), ν_a(μ)))⁻¹` by Theorem 1, and the supremum over the
positive proportions is the supremum over the simplex (`IdentTask.iSup_pos_iInf_cost_eq`). -/
lemma oracleDifficulty_staticClass_le
    (hρ : ∀ a c, ¬ id =ᵐ[ρ a] fun _ ↦ c)
    (hρ_closure : ∀ a, ∀ᵐ x ∂(ρ a), x ∈ closure ((ρ a).expFamilyMeans id))
    (hν : ∀ μ a, μ a ∈ (ρ a).expFamilyMeans id →
      task.ν μ a = (ρ a).expFamily id ((ρ a).natParam id (μ a)))
    (hreg : IsRegular task {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id})
    (hsingle : task.IsSingleAnswer) {μ : α → ℝ} (hμ : μ ∈ task.M)
    (hμc : MeasurableSet (task.correct μ)) :
    task.oracleDifficulty task.staticClass μ ≤ task.staticDifficulty μ := by
  obtain ⟨i, -⟩ := task.isSingleAnswer_iff.1 hsingle μ hμ
  have : Nonempty ℐ := ⟨i⟩
  obtain ⟨rec, hrec_meas, hrec⟩ := exists_measurable_rec hreg hsingle
  rw [IdentTask.staticDifficulty, ← task.iSup_pos_iInf_cost_eq, ENNReal.inv_iSup]
  refine le_iInf fun w ↦ ?_
  rw [ENNReal.inv_iSup]
  refine le_iInf fun hw ↦ ?_
  rw [ENNReal.inv_iSup]
  refine le_iInf fun hpos ↦ ?_
  obtain ⟨𝒜, h𝒜⟩ := task.exists_isStaticProportions hrec_meas hpos (mem_simplex_iff.1 hw).2
  calc task.oracleDifficulty task.staticClass μ ≤ limsup (task.errorRate 𝒜 μ) atTop :=
        iInf₂_le 𝒜 ⟨rec, fun _ hμ' ↦ rec_mem_correct hreg hsingle hrec hμ', w, h𝒜⟩
    _ = _ := (tendsto_errorRate_of_isStaticProportions_of_measurableSet hρ hρ_closure hν hreg
        hsingle hrec h𝒜 hμ hμc).limsup_eq

/-- **The oracle difficulty of static proportions algorithms** [D23, Theorem 1]. With answers with
measurable singletons, arms in exponential families as in
`tendsto_errorRate_of_isStaticProportions` and a task satisfying Assumption 1 with a single correct
answer on every admissible model, the oracle difficulty of the class of static proportions
algorithms at every admissible model `μ` is the static-proportions difficulty
`H^{sp}(μ) = (max_{w ∈ Δ_K} inf_{λ ∈ Alt(μ)} ∑ a, w a KL(ν_a(λ), ν_a(μ)))⁻¹`.

The paper writes the maximum over the positive proportions `Δ_K^0`; the maximum over the simplex
`Δ_K` has the same value. The proof does not use the condition of Assumption 1 that each answer set
is the interior of its closure. -/
theorem oracleDifficulty_staticClass [MeasurableSingletonClass ℐ]
    (hρ : ∀ a c, ¬ id =ᵐ[ρ a] fun _ ↦ c)
    (hρ_closure : ∀ a, ∀ᵐ x ∂(ρ a), x ∈ closure ((ρ a).expFamilyMeans id))
    (hν : ∀ μ a, μ a ∈ (ρ a).expFamilyMeans id →
      task.ν μ a = (ρ a).expFamily id ((ρ a).natParam id (μ a)))
    (hreg : IsRegular task {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id})
    (hsingle : task.IsSingleAnswer) {μ : α → ℝ} (hμ : μ ∈ task.M) :
    task.oracleDifficulty task.staticClass μ = task.staticDifficulty μ := by
  obtain ⟨i, hi⟩ := task.isSingleAnswer_iff.1 hsingle μ hμ
  have hμc : MeasurableSet (task.correct μ) := hi ▸ measurableSet_singleton i
  exact le_antisymm (oracleDifficulty_staticClass_le hρ hρ_closure hν hreg hsingle hμ hμc)
    (staticDifficulty_le_oracleDifficulty_staticClass hν hreg hsingle hμ hμc)

end Degenne2023Existence
