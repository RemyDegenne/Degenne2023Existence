/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Setting

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

open MeasureTheory LMLExplore LMLExplore.Identification

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
  sorry

end Degenne2023Existence
