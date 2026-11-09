/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Setting

/-!
# Theorem 8 of [D23]: no complexity in Gaussian best arm identification for many arms

For best arm identification with Gaussian arms of variance `1` and every class `𝒞` of algorithm
families containing the static proportions algorithms, every fixed-budget algorithm family has
maximal difficulty ratio at least `(3 / 80) log K` to the oracle difficulty of `𝒞`. For `K` large
enough, no such class admits a complexity.

The last inequality of the paper's proof, `(log (K + 1) - log 2) / 8 ≥ (3 / 40) log K`, fails for
`K = 2`, where the bound still holds (erratum E6 of `notes/paper-errata.md`).

## Main statements

* `Degenne2023Existence.ofReal_mul_log_le_iInf_maxRatio_baiTask_gaussian`:
  [D23, Theorem 8].

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
-/

@[expose] public section

open MeasureTheory Learning LMLExplore LMLExplore.Identification

open scoped ENNReal

namespace Degenne2023Existence

variable {α : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α]

/-- **No complexity in Gaussian best arm identification for many arms** [D23, Theorem 8]. For
best arm identification with Gaussian arms of variance `1` and a class `𝒞` of algorithm families
containing the static proportions algorithms, the infimum over the fixed-budget algorithm
families of the maximal difficulty ratio to the oracle difficulty of `𝒞` is at least
`(3 / 80) log K`, with `K` the number of arms. -/
theorem ofReal_mul_log_le_iInf_maxRatio_baiTask_gaussian (𝒞 : Set (ℕ → IdentAlg Unit α ℝ α))
    (h𝒞 : (baiTask (Bandits.gaussianBandit · 1) id).staticClass ⊆ 𝒞) :
    ENNReal.ofReal (3 / 80 * Real.log (Fintype.card α)) ≤
      ⨅ (𝒜 : ℕ → IdentAlg Unit α ℝ α) (_ : IsFixedBudgetFamily 𝒜),
        (baiTask (Bandits.gaussianBandit · 1) id).maxRatio
          ((baiTask (Bandits.gaussianBandit · 1) id).oracleDifficulty 𝒞) 𝒜 := by
  sorry

end Degenne2023Existence
