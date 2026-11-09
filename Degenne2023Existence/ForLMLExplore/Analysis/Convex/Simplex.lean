/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Analysis.Convex.Simplex

/-!
# The maximin of weighted coordinates over the simplex

For weights `c j ∈ [0, ∞]` on a finite set `s` of coordinates, every `w` of the simplex has
`min_{j ∈ s} c j w j ≤ (∑_{j ∈ s} (c j)⁻¹)⁻¹`, since `∑_{j ∈ s} w j ≤ 1`. The bound is attained by
the vector proportional to `c⁻¹` on `s` when the weights are positive and finite
(`LMLExplore.iInf_ofReal_inv_div_sum_inv_mul` for `s` the whole type).

## Main statements

* `LMLExplore.iSup_iInf_mul_ofReal_le`:
  `sup_{w ∈ Δ} min_{j ∈ s} c j w j ≤ (∑_{j ∈ s} (c j)⁻¹)⁻¹` in `ℝ≥0∞`.
-/

@[expose] public section

open scoped ENNReal

namespace LMLExplore

variable {α : Type*} [Fintype α]

/-- **Maximin of weighted coordinates over the simplex**: for weights `c j ∈ [0, ∞]` on a finite
set `s` of coordinates, `sup_{w ∈ Δ} min_{j ∈ s} c j w j ≤ (∑_{j ∈ s} (c j)⁻¹)⁻¹`, in `ℝ≥0∞`. -/
lemma iSup_iInf_mul_ofReal_le (s : Finset α) (c : α → ℝ≥0∞) :
    ⨆ w ∈ simplex α, ⨅ j ∈ s, c j * ENNReal.ofReal (w j) ≤ (∑ j ∈ s, (c j)⁻¹)⁻¹ := by
  refine iSup₂_le fun w hw ↦ ENNReal.le_inv_iff_mul_le.2 ?_
  rw [mem_simplex_iff] at hw
  rw [Finset.mul_sum]
  calc ∑ j ∈ s, (⨅ j ∈ s, c j * ENNReal.ofReal (w j)) * (c j)⁻¹
      ≤ ∑ j ∈ s, ENNReal.ofReal (w j) := Finset.sum_le_sum fun j hj ↦
        calc (⨅ j ∈ s, c j * ENNReal.ofReal (w j)) * (c j)⁻¹
            ≤ c j * ENNReal.ofReal (w j) * (c j)⁻¹ := by gcongr; exact iInf₂_le j hj
          _ = ENNReal.ofReal (w j) * (c j * (c j)⁻¹) := by ring
          _ ≤ ENNReal.ofReal (w j) * 1 := by gcongr; exact ENNReal.mul_inv_le_one _
          _ = ENNReal.ofReal (w j) := mul_one _
    _ ≤ ∑ j, ENNReal.ofReal (w j) := Finset.sum_le_sum_of_subset (Finset.subset_univ s)
    _ = 1 := by rw [← ENNReal.ofReal_sum_of_nonneg fun j _ ↦ hw.1 j, hw.2, ENNReal.ofReal_one]

end LMLExplore
