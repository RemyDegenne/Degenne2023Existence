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

end StaticProportions

end IdentTask

end LMLExplore.Identification
