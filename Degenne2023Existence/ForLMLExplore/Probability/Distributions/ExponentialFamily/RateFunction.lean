/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Probability.Distributions.ExponentialFamily.RateFunction

/-!
# Sub-Gaussian members of an exponential family

Let `ρ` be a measure on a measurable space `𝓧` and `T : 𝓧 → ℝ` a statistic, with divergence
`d(x, μ)` in the mean parametrization of their exponential family. If the statistic is
`c`-sub-Gaussian around its mean `μ` under the member of mean `μ`, then
`d(x, μ) ≥ (x - μ)² / (2 c)` at every mean `x` of the family: the divergence `d(·, μ)` is the
Cramér rate function of `T` under that member
(`LMLExplore.rateFunction_expFamily_natParam`), which is at least quadratic
(`ProbabilityTheory.HasSubgaussianMGF.ofReal_sq_div_le_rateFunction`). This complements
LMLExplore's `MeasureTheory.Measure.sq_div_le_expFamilyDiv`, which assumes a bound on the variances
of the members between `x` and `μ`.

## Main statements

* `MeasureTheory.Measure.sq_div_le_expFamilyDiv_of_hasSubgaussianMGF`: if `T - μ` is
  `c`-sub-Gaussian under the member of mean `μ`, then `(x - μ)² / (2 c) ≤ d(x, μ)` for every mean
  `x` of the family.
-/

@[expose] public section

open ProbabilityTheory LMLExplore

open scoped NNReal

namespace MeasureTheory.Measure

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {x μ : ℝ}

/-- **Sub-Gaussian comparison.** If the statistic `T` is `c`-sub-Gaussian around its mean `μ` under
the member of mean `μ` of the exponential family, then `(x - μ)² / (2 c) ≤ d(x, μ)` for every mean
`x` of the family. -/
lemma sq_div_le_expFamilyDiv_of_hasSubgaussianMGF [NeZero ρ] (hx : x ∈ ρ.expFamilyMeans T)
    (hμ : μ ∈ ρ.expFamilyMeans T) {c : ℝ≥0}
    (h : HasSubgaussianMGF (fun ω ↦ T ω - μ) c (ρ.expFamily T (ρ.natParam T μ))) :
    (x - μ) ^ 2 / (2 * c) ≤ ρ.expFamilyDiv T x μ := by
  have hη := natParam_mem_interior_integrableExpSet hμ
  have := isProbabilityMeasure_expFamily (ρ := ρ) (T := T) (interior_subset hη)
  have h_mean := integral_expFamily_natParam hμ
  have h' : HasSubgaussianMGF (fun ω ↦ T ω - ∫ y, T y ∂(ρ.expFamily T (ρ.natParam T μ))) c
      (ρ.expFamily T (ρ.natParam T μ)) := by
    rwa [h_mean]
  have h_le := h'.ofReal_sq_div_le_rateFunction x
  rw [h_mean, rateFunction_expFamily_natParam hx hμ] at h_le
  exact (ENNReal.ofReal_le_ofReal_iff (expFamilyDiv_nonneg hx hμ)).1 h_le

end MeasureTheory.Measure
