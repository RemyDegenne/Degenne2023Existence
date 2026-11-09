/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Identification.FixedBudget
public import LMLExplore.Identification.Task.TransportationCost
public import LeanMachineLearning.SequentialLearning.SumRewards
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# The complexity of fixed-budget identification

A *fixed-budget algorithm family* `𝒜` is a sequence of identification algorithms, `𝒜 T` with
budget `T` for every `T : ℕ`. Its probability of error `p_{θ,T}(𝒜)` on the model `θ` of a task
decreases exponentially in `T` for good families, and its rate is measured by
`h_{θ,T}(𝒜) = T / log (1 / p_{θ,T}(𝒜))`, so that `p_{θ,T}(𝒜) = exp (-T / h_{θ,T}(𝒜))`. For a
class `𝒞` of families (a set of families), the *oracle difficulty* `H_𝒞(θ)` is the best asymptotic
rate `inf_{𝒜 ∈ 𝒞} limsup_T h_{θ,T}(𝒜)` at `θ`, and the class *admits a complexity* if a single
family of the class attains it at every admissible model. Against a difficulty function
`H : Θ → ℝ≥0∞`, the *difficulty ratio* `R_{H,T}(𝒜, θ) = h_{θ,T}(𝒜) / H(θ)` compares the family to
the baseline `H`; its `limsup` is `R_{H,∞}(𝒜, θ)` and its supremum over the admissible models is
the *maximal difficulty ratio* of `𝒜`.

The *static proportions* families sample the arms with fixed proportions `w`, up to a bounded
number of pulls, and recommend the empirical correct answer. The oracle difficulty of their class
is the inverse of `max_{w ∈ Δ_K} inf_{λ ∈ Alt(θ)} ∑ a, w a KL(ν_a(λ), ν_a(θ))`, the
*static-proportions difficulty*, in which the alternative comes first in the divergence, unlike in
the transportation costs of fixed-confidence identification.

The quantities `h`, `H` and `R` are `ℝ≥0∞`-valued: `h = 0` when `p = 0` and `h = ∞` when `p = 1`
and `T > 0`.

## Main definitions

In the namespace `LMLExplore.Identification`:

* `IsFixedBudgetFamily 𝒜`: `𝒜 T` stops after `T` rounds, for every budget `T`.
* `IdentTask.alternatives task θ`: the admissible models without a common correct answer with `θ`.
* `IdentTask.errorProb task 𝒜 θ T`: the probability of error `p_{θ,T}(𝒜)`.
* `IdentTask.errorRate task 𝒜 θ T`: the rate `h_{θ,T}(𝒜) = T / log (1 / p_{θ,T}(𝒜))`.
* `IdentTask.oracleDifficulty task 𝒞 θ`: the oracle difficulty `H_𝒞(θ)` of the class `𝒞`.
* `IdentTask.AdmitsComplexity task 𝒞`: the class `𝒞` admits a complexity.
* `IdentTask.difficultyRatio task H 𝒜 θ T`, `IdentTask.asymptoticRatio task H 𝒜 θ`,
  `IdentTask.maxRatio task H 𝒜`: the difficulty ratios `R_{H,T}(𝒜, θ)`, `R_{H,∞}(𝒜, θ)` and the
  maximal difficulty ratio `sup_{θ ∈ M} R_{H,∞}(𝒜, θ)`.
* `IdentTask.IsConsistent task 𝒜`: `p_{θ,T}(𝒜) → 0` at every admissible model.
* `IdentTask.IsStaticProportions task rec 𝒜 w`: `𝒜` samples with the proportions `w` and
  recommends `rec` of the empirical means; `IdentTask.staticClass task` is the class of these
  families.
* `IdentTask.staticDifficulty task θ`: the static-proportions difficulty.

## Main statements

* `IdentTask.inv_difficultyRatio`: `R_{H,T}(𝒜, θ)⁻¹ = H(θ) log (1 / p_{θ,T}(𝒜)) / T`.
* `IdentTask.asymptoticRatio_eq_top`: a family whose probability of error at `θ` does not tend
  to `0` has an infinite asymptotic difficulty ratio at `θ`, for `H(θ) < ∞`.
* `IdentTask.tendsto_errorRate_of_tendsto_log_div`: `(1 / T) log p_{θ,T}(𝒜) → -c` gives
  `h_{θ,T}(𝒜) → c⁻¹`.
* `IdentTask.IsStaticProportions.errorProb_eq`: the probability of error of a static proportions
  family is the probability that the recommendation of the empirical means is not correct.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023.
-/

@[expose] public section

open MeasureTheory Filter Topology Learning

open scoped ENNReal

namespace LMLExplore.Identification

variable {α Θ ℐ 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  [MeasurableSpace ℐ]

/-- The family of identification algorithms `𝒜` is a *fixed-budget family*: for every budget `T`,
the algorithm `𝒜 T` stops after exactly `T` rounds. -/
def IsFixedBudgetFamily (𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ) : Prop := ∀ T, IsFixedBudget (𝒜 T) T

namespace IdentTask

variable (task : IdentTask α Θ ℐ 𝓨)

/-- The alternatives to the model `θ`: the admissible models that have no correct answer in common
with `θ`. For a single-answer task and an admissible model `θ` with answer `i`, they are the
alternatives `task.alt i` to `i`. -/
def alternatives (θ : Θ) : Set Θ :=
  {θ' | θ' ∈ task.M ∧ Disjoint (task.correct θ) (task.correct θ')}

omit [MeasurableSpace ℐ] in
/-- The alternatives to `θ` in the task restricted to `S` are the alternatives in `S`. -/
@[simp]
lemma alternatives_restrict (S : Set Θ) (θ : Θ) :
    (task.restrict S).alternatives θ = task.alternatives θ ∩ S := by
  ext θ'
  simp only [alternatives, M_restrict, correct_restrict, Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

omit [MeasurableSpace ℐ] in
/-- For a model `θ` with the single correct answer `i`, the alternatives to `θ` are the
alternatives to `i`. -/
lemma alternatives_eq_alt {θ : Θ} {i : ℐ} (hi : task.correct θ = {i}) :
    task.alternatives θ = task.alt i := by
  ext θ'
  simp [alternatives, mem_alt_iff, hi]

/-- The probability of error `p_{θ,T}(𝒜)` of the family `𝒜` with budget `T` on the model `θ`: the
probability that the output of `𝒜 T` in the bandit of `θ` is not a correct answer of `θ`. -/
noncomputable def errorProb (𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ) (θ : Θ) (T : ℕ) : ℝ≥0∞ :=
  (𝒜 T).outputMeasure (Environment.bandit (task.ν θ)) (task.correct θ)ᶜ

/-- The rate `h_{θ,T}(𝒜) = T / log (1 / p_{θ,T}(𝒜))` of the family `𝒜` with budget `T` on the
model `θ`, so that `p_{θ,T}(𝒜) = exp (-T / h_{θ,T}(𝒜))`. It is `0` if `p_{θ,T}(𝒜) = 0` and `∞` if
`p_{θ,T}(𝒜) = 1` and `T > 0`. -/
noncomputable def errorRate (𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ) (θ : Θ) (T : ℕ) : ℝ≥0∞ :=
  T / (-ENNReal.log (task.errorProb 𝒜 θ T)).toENNReal

/-- The oracle difficulty `H_𝒞(θ) = inf_{𝒜 ∈ 𝒞} limsup_{T → ∞} h_{θ,T}(𝒜)` of the class `𝒞` of
algorithm families at the model `θ`: the asymptotic rate at `θ` of the family of the class that is
best at `θ`. -/
noncomputable def oracleDifficulty (𝒞 : Set (ℕ → IdentAlg Unit α 𝓨 ℐ)) (θ : Θ) : ℝ≥0∞ :=
  ⨅ 𝒜 ∈ 𝒞, limsup (task.errorRate 𝒜 θ) atTop

/-- The class `𝒞` of algorithm families *admits a complexity*: a single family of the class
attains the oracle difficulty of the class at every admissible model. -/
def AdmitsComplexity (𝒞 : Set (ℕ → IdentAlg Unit α 𝓨 ℐ)) : Prop :=
  ∃ 𝒜 ∈ 𝒞, ∀ θ ∈ task.M, limsup (task.errorRate 𝒜 θ) atTop ≤ task.oracleDifficulty 𝒞 θ

/-- The difficulty ratio `R_{H,T}(𝒜, θ) = h_{θ,T}(𝒜) / H(θ)` of the family `𝒜` with budget `T` to
the difficulty function `H` at the model `θ`. It is larger than `1` if the probability of error is
larger than `exp (-T / H(θ))`. -/
noncomputable def difficultyRatio (H : Θ → ℝ≥0∞) (𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ) (θ : Θ) (T : ℕ) :
    ℝ≥0∞ :=
  task.errorRate 𝒜 θ T / H θ

/-- The asymptotic difficulty ratio `R_{H,∞}(𝒜, θ) = limsup_{T → ∞} R_{H,T}(𝒜, θ)`. -/
noncomputable def asymptoticRatio (H : Θ → ℝ≥0∞) (𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ) (θ : Θ) :
    ℝ≥0∞ :=
  limsup (task.difficultyRatio H 𝒜 θ) atTop

/-- The maximal difficulty ratio `sup_{θ ∈ M} R_{H,∞}(𝒜, θ)` of the family `𝒜` to the difficulty
function `H`, over the admissible models. -/
noncomputable def maxRatio (H : Θ → ℝ≥0∞) (𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ) : ℝ≥0∞ :=
  ⨆ θ ∈ task.M, task.asymptoticRatio H 𝒜 θ

/-- The family `𝒜` is *consistent*: its probability of error tends to `0` at every admissible
model. -/
def IsConsistent (𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ) : Prop :=
  ∀ θ ∈ task.M, Tendsto (task.errorProb 𝒜 θ) atTop (𝓝 0)

/-- For a difficulty `H θ` positive and finite and a budget `T ≠ 0`, the inverse of the difficulty
ratio is `R_{H,T}(𝒜, θ)⁻¹ = H(θ) log (1 / p_{θ,T}(𝒜)) / T`. -/
lemma inv_difficultyRatio {H : Θ → ℝ≥0∞} {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} {θ : Θ} {T : ℕ}
    (hH₀ : H θ ≠ 0) (hH : H θ ≠ ∞) (hT : T ≠ 0) :
    (task.difficultyRatio H 𝒜 θ T)⁻¹ =
      H θ * ((-ENNReal.log (task.errorProb 𝒜 θ T)).toENNReal / T) := by
  rw [difficultyRatio, errorRate, ENNReal.inv_div (Or.inl hH) (Or.inl hH₀),
    ENNReal.div_eq_inv_mul, ENNReal.inv_div (Or.inr (ENNReal.natCast_ne_top T))
      (Or.inr (by exact_mod_cast hT)), mul_comm]

/-- If the probability of error at `θ` does not tend to `0` and the difficulty `H θ` is finite,
the asymptotic difficulty ratio at `θ` is infinite: along the budgets `T` with
`p_{θ,T}(𝒜) > ε`, the rate `h_{θ,T}(𝒜)` is at least `T / log (1 / ε)`. -/
lemma asymptoticRatio_eq_top {H : Θ → ℝ≥0∞} {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} {θ : Θ}
    (hH : H θ ≠ ∞) (hp : ¬ Tendsto (task.errorProb 𝒜 θ) atTop (𝓝 0)) :
    task.asymptoticRatio H 𝒜 θ = ∞ := by
  obtain ⟨ε, hε, hfreq⟩ : ∃ ε > 0, ∃ᶠ T in atTop, ε < task.errorProb 𝒜 θ T := by
    simpa [ENNReal.tendsto_nhds_zero, Filter.not_eventually, Filter.frequently_atTop] using hp
  set L := (-ENNReal.log ε).toENNReal
  have hL : L ≠ ∞ := by
    simp only [L, ne_eq, EReal.toENNReal_eq_top_iff, EReal.neg_eq_top_iff]
    simpa using hε.ne'
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  have hev : ∀ᶠ T : ℕ in atTop, (r : ℝ≥0∞) * H θ * L < T :=
    ENNReal.tendsto_nat_nhds_top.eventually (eventually_gt_nhds
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hH.lt_top) hL.lt_top))
  refine le_limsup_of_frequently_le ((hfreq.and_eventually hev).mono fun T ⟨hT, hrT⟩ ↦ ?_)
    (by isBoundedDefault)
  rw [difficultyRatio, errorRate]
  have h1 : (T : ℝ≥0∞) / L ≤ T / (-ENNReal.log (task.errorProb 𝒜 θ T)).toENNReal := by
    gcongr
    exact EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (ENNReal.log_le_log hT.le))
  refine le_trans ?_ (ENNReal.div_le_div_right h1 _)
  have hT0 : (T : ℝ≥0∞) ≠ 0 := (zero_le.trans_lt hrT).ne'
  rw [ENNReal.le_div_iff_mul_le (Or.inr (by simp [ENNReal.div_eq_zero_iff, hT0, hL]))
      (Or.inl hH), ENNReal.le_div_iff_mul_le (Or.inr hT0) (Or.inl hL)]
  exact hrT.le

omit [MeasurableSpace ℐ] in
/-- Dividing by a positive integer commutes with the positive part `EReal → ℝ≥0∞`. -/
private lemma toENNReal_div_natCast (x : EReal) {n : ℕ} (hn : n ≠ 0) :
    (x / n).toENNReal = x.toENNReal / n := by
  have hn' : (0 : EReal) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  induction x using EReal.rec with
  | bot => simp [EReal.bot_div_of_pos_ne_top hn' (EReal.natCast_ne_top n)]
  | top =>
    rw [EReal.top_div_of_pos_ne_top hn' (EReal.natCast_ne_top n), EReal.toENNReal_top,
      ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top n)]
  | coe x =>
    have hn'' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [← EReal.coe_natCast, ← EReal.coe_div, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _),
      EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe, EReal.toReal_coe,
      ENNReal.ofReal_div_of_pos hn'', ENNReal.ofReal_natCast]

/-- **The rate from the exponent of the probability of error.** If
`(1 / T) log p_{θ,T}(𝒜) → -c` for some `c ∈ [0, ∞]`, then `h_{θ,T}(𝒜) → c⁻¹`: for `T > 0`,
`h_{θ,T}(𝒜)` is the inverse of the positive part of `-(1 / T) log p_{θ,T}(𝒜)`, and inversion is
continuous on `[0, ∞]`. -/
lemma tendsto_errorRate_of_tendsto_log_div {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} {θ : Θ} {c : ℝ≥0∞}
    (h : Tendsto (fun T : ℕ ↦ ENNReal.log (task.errorProb 𝒜 θ T) / T) atTop
      (𝓝 (-(c : EReal)))) :
    Tendsto (task.errorRate 𝒜 θ) atTop (𝓝 c⁻¹) := by
  have h1 : Tendsto (fun T : ℕ ↦ (-(ENNReal.log (task.errorProb 𝒜 θ T) / T)).toENNReal) atTop
      (𝓝 c) := by
    have := ((EReal.continuous_toENNReal.comp continuous_neg).tendsto _).comp h
    simpa [Function.comp_def, EReal.toENNReal_coe] using this
  refine (tendsto_inv_iff.2 h1).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with T hT
  have hneg (x : EReal) : -(x / T) = -x / T := by
    rw [div_eq_mul_inv, div_eq_mul_inv, EReal.neg_mul]
  rw [errorRate, hneg, toENNReal_div_natCast _ hT, ENNReal.inv_div (Or.inl
    (ENNReal.natCast_ne_top T)) (Or.inl (by exact_mod_cast hT))]

section StaticProportions

variable [Fintype α]

/-- The static-proportions difficulty
`H^{sp}(θ) = (max_{w ∈ Δ_K} inf_{λ ∈ Alt(θ)} ∑ a, w a KL(ν_a(λ), ν_a(θ)))⁻¹` of the model `θ`,
with the alternative first in the divergence. It is the oracle difficulty of the class of static
proportions algorithms for tasks with arms in exponential families [D23, Theorem 1]. -/
noncomputable def staticDifficulty (θ : Θ) : ℝ≥0∞ :=
  (⨆ w ∈ simplex α, ⨅ θ' ∈ task.alternatives θ, task.cost w θ' θ)⁻¹

variable [DecidableEq α] (task : IdentTask α (α → ℝ) ℐ ℝ)

/-- The family `𝒜` is a *static proportions* family with proportions `w` and recommendation rule
`rec`, for a task on the vectors of means `μ : α → ℝ` with real observations: the proportions are
positive and sum to `1`, and for every budget `T`, `𝒜 T` stops after `T` rounds, on every
admissible model its numbers of pulls satisfy `|N_{T,a} - T w a| ≤ K` almost surely, with `K` the
number of arms, and it recommends `rec μ̂_T` for the vector `μ̂_T` of the empirical means. -/
def IsStaticProportions (rec : (α → ℝ) → ℐ) (𝒜 : ℕ → IdentAlg Unit α ℝ ℐ) (w : α → ℝ) : Prop :=
  (∀ a, 0 < w a) ∧ ∑ a, w a = 1 ∧ ∀ T, IsFixedBudget (𝒜 T) T ∧
    (∀ μ ∈ task.M, ∀ᵐ h ∂(trajMeasure (𝒜 T).alg (Environment.bandit (task.ν μ))),
      ∀ a, |(pullCount IT.action a T h : ℝ) - T * w a| ≤ Fintype.card α) ∧
    ∀ h : Hist Unit α ℝ T, outputAt (𝒜 T) T h = Measure.dirac (rec (empMean' T h))

/-- The class `𝒞^{sp}` of static proportions families: the static proportions families with some
positive proportions and some recommendation rule that is correct on the admissible models. -/
def staticClass : Set (ℕ → IdentAlg Unit α ℝ ℐ) :=
  {𝒜 | ∃ rec : (α → ℝ) → ℐ, (∀ μ ∈ task.M, rec μ ∈ task.correct μ) ∧
    ∃ w, task.IsStaticProportions rec 𝒜 w}

variable {task}

/-- The probability of error of a static proportions family at `θ`, when the set of correct
answers of `θ` is measurable: the probability that the recommendation `rec μ̂_T` of the vector of
the empirical means after `T` rounds is not a correct answer of `θ`. The recommendation rule need
not be measurable: the output kernel makes its composition with the empirical means measurable.

If the set of correct answers is not measurable, the probability of error is an outer measure,
which can be `1` for every algorithm: for the trivial σ-algebra on two answers. -/
lemma IsStaticProportions.errorProb_eq {rec : (α → ℝ) → ℐ} {𝒜 : ℕ → IdentAlg Unit α ℝ ℐ}
    {w : α → ℝ} (h𝒜 : task.IsStaticProportions rec 𝒜 w) {θ : α → ℝ}
    (hθ : MeasurableSet (task.correct θ)) (T : ℕ) :
    task.errorProb 𝒜 θ T = trajMeasure (𝒜 T).alg (Environment.bandit (task.ν θ))
      {h | rec (fun a ↦ empMean IT.action IT.feedback a T h) ∉ task.correct θ} := by
  set E := {h : ℕ → Round Unit α ℝ |
    rec (fun a ↦ empMean IT.action IT.feedback a T h) ∉ task.correct θ}
  have hf : Measurable fun h ↦ outputAt (𝒜 T) T (IT.hist T h) (task.correct θ)ᶜ :=
    (ProbabilityTheory.Kernel.measurable_coe _ hθ.compl).comp (IT.measurable_hist T)
  -- The output rule gives the error probability `1` on `E` and `0` outside.
  have heq : (fun h ↦ outputAt (𝒜 T) T (IT.hist T h) (task.correct θ)ᶜ) = E.indicator 1 := by
    ext h
    have hmean : empMean' T (IT.hist T h) = fun a ↦ empMean IT.action IT.feedback a T h := by
      ext a
      rw [empMean_eq_empMean' (O := IT.obs), IT.history_obs_action_feedback]
    rw [(h𝒜.2.2 T).2.2, Measure.dirac_apply' _ hθ.compl, hmean]
    by_cases hE : h ∈ E
    · rw [Set.indicator_of_mem hE, Set.indicator_of_mem (show _ ∈ (task.correct θ)ᶜ from hE),
        Pi.one_apply, Pi.one_apply]
    · rw [Set.indicator_of_notMem hE,
        Set.indicator_of_notMem (show _ ∉ (task.correct θ)ᶜ from hE)]
  have hE : MeasurableSet E := by
    have : E = (fun h ↦ outputAt (𝒜 T) T (IT.hist T h) (task.correct θ)ᶜ) ⁻¹' {1} := by
      rw [heq]
      ext h
      by_cases hh : h ∈ E <;> simp [hh]
    rw [this]
    exact hf (measurableSet_singleton 1)
  rw [errorProb, (h𝒜.2.2 T).1.outputMeasure_eq, Measure.bind_apply hθ.compl
    (ProbabilityTheory.Kernel.aemeasurable _), lintegral_map
    (ProbabilityTheory.Kernel.measurable_coe _ hθ.compl) (IT.measurable_hist T), heq,
    lintegral_indicator_one hE]

end StaticProportions

end IdentTask

end LMLExplore.Identification
