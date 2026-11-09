/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Setting

/-!
# Theorem 10 of [D23]: no complexity in best arm identification with two Bernoulli arms

For best arm identification with two Bernoulli arms and every class `𝒞` of algorithm families
containing the static proportions algorithms, the infimum over the fixed-budget algorithm families
of the maximal difficulty ratio to the oracle difficulty of `𝒞` is larger than `1`: no single
algorithm attains the best possible rate everywhere. The proof applies Corollary 4 at
`μ(x) = (x (1 + x), x)` with the alternatives `(x / 2, x)` and `(x (1 + x), 1 / 2)`, whose bound
tends to about `1.22` as `x → 0`.

## Main statements

* `Degenne2023Existence.one_lt_iInf_maxRatio_baiTask_bernoulli_two`: [D23, Theorem 10].

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
-/

@[expose] public section

open MeasureTheory Learning LMLExplore LMLExplore.Identification

open scoped ENNReal

namespace Degenne2023Existence

/-- **No complexity in best arm identification with two Bernoulli arms** [D23, Theorem 10]. For
best arm identification on the Bernoulli bandits with two arms and means in `(0, 1)`, and a class
`𝒞` of algorithm families containing the static proportions algorithms, the infimum over the
fixed-budget algorithm families of the maximal difficulty ratio to the oracle difficulty of `𝒞` is
larger than `1`. -/
theorem one_lt_iInf_maxRatio_baiTask_bernoulli_two
    (𝒞 : Set (ℕ → IdentAlg Unit (Fin 2) ℝ (Fin 2)))
    (h𝒞 : ((baiTask (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦
        Set.projIcc 0 1 zero_le_one (μ c)) id).restrict
          {μ | ∀ c, μ c ∈ Set.Ioo 0 1}).staticClass ⊆ 𝒞) :
    1 < ⨅ (𝒜 : ℕ → IdentAlg Unit (Fin 2) ℝ (Fin 2)) (_ : IsFixedBudgetFamily 𝒜),
      ((baiTask (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦
        Set.projIcc 0 1 zero_le_one (μ c)) id).restrict {μ | ∀ c, μ c ∈ Set.Ioo 0 1}).maxRatio
        (((baiTask (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦
          Set.projIcc 0 1 zero_le_one (μ c)) id).restrict
            {μ | ∀ c, μ c ∈ Set.Ioo 0 1}).oracleDifficulty 𝒞) 𝒜 := by
  sorry

end Degenne2023Existence
