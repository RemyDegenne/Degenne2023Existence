/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Setting

/-!
# Theorem 5 of [D23]: the difficulty ratio of static proportions is at most `K`

A static proportions algorithm with proportions `w ∈ Δ_K^0` has a bounded maximal difficulty ratio
to the static-proportions difficulty `H^{sp}`: `sup_{λ ∈ 𝒟} R_{H^{sp},∞}(𝒜, λ) ≤ (min_j w_j)⁻¹`. In
particular the uniform allocation has maximal difficulty ratio at most `K`.

The paper writes `H_{𝒞^{sp}}` for the oracle difficulty of the class of static proportions
algorithms, equal to `H^{sp}` by Theorem 1 (`oracleDifficulty_staticClass`). The recommendation
rule is assumed to satisfy the condition of `tendsto_errorRate_of_isStaticProportions` (erratum E1
of `notes/paper-errata.md`).

## Main statements

* `Degenne2023Existence.maxRatio_staticDifficulty_le_of_isStaticProportions`:
  [D23, Theorem 5].
* `Degenne2023Existence.maxRatio_staticDifficulty_le_card`: [D23, Theorem 5], the uniform
  allocation.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
-/

@[expose] public section

open MeasureTheory Learning LMLExplore LMLExplore.Identification

open scoped ENNReal

namespace Degenne2023Existence

variable {α ℐ : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] [MeasurableSpace ℐ] [Finite ℐ]
  {task : IdentTask α (α → ℝ) ℐ ℝ} {ρ : α → Measure ℝ}

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
