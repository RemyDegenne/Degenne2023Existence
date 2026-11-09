/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Probability.Distributions.ExponentialFamily.Mean

/-!
# The divergence of an exponential family in its first argument

Let `ρ` be a measure on a measurable space `𝓧` and `T : 𝓧 → ℝ` a statistic, with log-partition
function `ψ = cgf T ρ`, natural parameters `η(μ)` and divergence
`d(x, μ) = ψ(η(μ)) - ψ(η(x)) - x (η(μ) - η(x))` in the mean parametrization
(`MeasureTheory.Measure.expFamilyDiv`). LMLExplore's `Mean.lean` studies the weighted divergences
`z ↦ ∑ i, w i d(μ i, z)`, minimized at the weighted mean of the `μ i`. This file studies the
weighted divergences with the free mean first, `z ↦ ∑ i, w i d(z, μ i)`, which appear when the
alternative comes first, as in the error exponents of static allocations in fixed-budget
identification. They are minimized at the mean whose natural parameter is the weighted mean of the
natural parameters `η(μ i)`, by the compensation identity
`∑ i, w i d(z, μ i) = ∑ i, w i d(x, μ i) + (∑ i, w i) d(z, x)`.

For two distinct means `μ₀` and `μ₁`, the slope `x* = (ψ(η(μ₀)) - ψ(η(μ₁))) / (η(μ₀) - η(μ₁))` of
`ψ` is a mean of the family, with natural parameter strictly between `η(μ₀)` and `η(μ₁)`, at the
same divergence from both, `d(x*, μ₀) = d(x*, μ₁)`: this is the Chernoff information of the two
members, the value of `max_{t ∈ [0, 1]} min_z (t d(z, μ₀) + (1 - t) d(z, μ₁))`.

## Main statements

* `MeasureTheory.Measure.expFamilyDiv_le_expFamilyDiv_left_of_mem_uIcc`: `d(γ, μ) ≤ d(x, μ)` for
  a mean `γ` between `μ` and a mean `x`.
* `MeasureTheory.Measure.exists_expFamilyDiv_le_and_expFamilyDiv_le`: for means with
  `(y₀ - y₁) (μ₀ - μ₁) ≤ 0`, some mean `z` has `d(z, μ₀) ≤ d(y₀, μ₀)` and `d(z, μ₁) ≤ d(y₁, μ₁)`.
* `MeasureTheory.Measure.sum_mul_expFamilyDiv_left_eq`: the compensation identity
  `∑ i, w i d(z, μ i) = ∑ i, w i d(x, μ i) + (∑ i, w i) d(z, x)` for `(∑ i, w i) η(x) =
  ∑ i, w i η(μ i)`.
* `MeasureTheory.Measure.sum_mul_expFamilyDiv_left_le`: such an `x` minimizes
  `z ↦ ∑ i, w i d(z, μ i)` over the means of the family, for nonnegative weights.
* `MeasureTheory.Measure.mul_expFamilyDiv_add_mul_expFamilyDiv_left_le`: the two-point case, at
  the mean `ψ'(w₀ η(μ₀) + w₁ η(μ₁))`.
* `MeasureTheory.Measure.exists_mem_uIoo_deriv_cgf_eq_slope`: the slope `x*` is the mean of a
  natural parameter strictly between `η(μ₀)` and `η(μ₁)`.
* `MeasureTheory.Measure.expFamilyDiv_slope_eq`: `d(x*, μ₀) = d(x*, μ₁)`.
* `MeasureTheory.Measure.slope_cgf_natParam_eq_sub`,
  `MeasureTheory.Measure.slope_cgf_natParam_eq_add`: `x* = μ₀ - d(μ₀, μ₁) / (η(μ₀) - η(μ₁))
  = μ₁ + d(μ₁, μ₀) / (η(μ₀) - η(μ₁))`.

## References

* H. Chernoff, *A measure of asymptotic efficiency for tests of a hypothesis based on the sum of
  observations*, Annals of Mathematical Statistics 23, 1952.
* T. M. Cover and J. A. Thomas, *Elements of Information Theory*, Wiley, 2006, Section 11.9.
-/

@[expose] public section

open ProbabilityTheory Set

namespace MeasureTheory.Measure

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {x μ μ₀ μ₁ : ℝ}

/-! ### Monotonicity in the first argument -/

/-- The divergence to `μ` grows as the first argument moves away from `μ`: for means `γ` and `x`
of the family with `γ` between `μ` and `x`, `d(γ, μ) ≤ d(x, μ)`. -/
lemma expFamilyDiv_le_expFamilyDiv_left_of_mem_uIcc (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) {γ : ℝ}
    (hμ : μ ∈ ρ.expFamilyMeans T) (hγ : γ ∈ ρ.expFamilyMeans T) (hx : x ∈ ρ.expFamilyMeans T)
    (h : γ ∈ uIcc μ x) :
    ρ.expFamilyDiv T γ μ ≤ ρ.expFamilyDiv T x μ := by
  rcases le_total μ x with hμx | hxμ
  · rw [uIcc_of_le hμx] at h
    exact (strictMonoOn_expFamilyDiv_left hT hμ).monotoneOn ⟨hγ, h.1⟩ ⟨hx, hμx⟩ h.2
  · rw [uIcc_of_ge hxμ] at h
    exact (strictAntiOn_expFamilyDiv_left hT hμ).antitoneOn ⟨hx, hxμ⟩ ⟨hγ, h.2⟩ h.1

/-- For means `y₀, y₁, μ₀, μ₁` of the family ordered in opposite ways, `(y₀ - y₁) (μ₀ - μ₁) ≤ 0`,
some mean `z` is at most as far from `μ₀` as `y₀` and from `μ₁` as `y₁`:
`d(z, μ₀) ≤ d(y₀, μ₀)` and `d(z, μ₁) ≤ d(y₁, μ₁)`. The intervals between `y₀` and `μ₀` and between
`y₁` and `μ₁` meet. -/
lemma exists_expFamilyDiv_le_and_expFamilyDiv_le (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) {y₀ y₁ : ℝ}
    (hy₀ : y₀ ∈ ρ.expFamilyMeans T) (hy₁ : y₁ ∈ ρ.expFamilyMeans T)
    (hμ₀ : μ₀ ∈ ρ.expFamilyMeans T) (hμ₁ : μ₁ ∈ ρ.expFamilyMeans T)
    (h : (y₀ - y₁) * (μ₀ - μ₁) ≤ 0) :
    ∃ z ∈ ρ.expFamilyMeans T, ρ.expFamilyDiv T z μ₀ ≤ ρ.expFamilyDiv T y₀ μ₀ ∧
      ρ.expFamilyDiv T z μ₁ ≤ ρ.expFamilyDiv T y₁ μ₁ := by
  -- `z = max (min y₀ μ₀) (min y₁ μ₁)` lies in both intervals
  set z := max (min y₀ μ₀) (min y₁ μ₁)
  have h_cross : min y₁ μ₁ ≤ max y₀ μ₀ ∧ min y₀ μ₀ ≤ max y₁ μ₁ := by
    rcases mul_nonpos_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨(min_le_left _ _).trans (le_max_of_le_left (by linarith)),
        (min_le_right _ _).trans (le_max_of_le_right (by linarith))⟩
    · exact ⟨(min_le_right _ _).trans (le_max_of_le_right (by linarith)),
        (min_le_left _ _).trans (le_max_of_le_left (by linarith))⟩
  have hz₀ : z ∈ uIcc μ₀ y₀ := by
    rw [uIcc_comm]
    exact ⟨le_max_left _ _, max_le min_le_max h_cross.1⟩
  have hz₁ : z ∈ uIcc μ₁ y₁ := by
    rw [uIcc_comm]
    exact ⟨le_max_right _ _, max_le h_cross.2 min_le_max⟩
  have hz : z ∈ ρ.expFamilyMeans T :=
    (convex_expFamilyMeans.ordConnected.uIcc_subset hμ₀ hy₀) hz₀
  exact ⟨z, hz, expFamilyDiv_le_expFamilyDiv_left_of_mem_uIcc hT hμ₀ hz hy₀ hz₀,
    expFamilyDiv_le_expFamilyDiv_left_of_mem_uIcc hT hμ₁ hz hy₁ hz₁⟩

/-! ### Weighted divergences with the free mean first -/

/-- **Compensation identity**, with the free mean first. If the natural parameter of `x` is the
mean of the natural parameters of the `μ i`, `i ∈ s`, weighted by `w`, that is
`(∑ i ∈ s, w i) η(x) = ∑ i ∈ s, w i η(μ i)`, then for every `z`,
`∑ i ∈ s, w i d(z, μ i) = ∑ i ∈ s, w i d(x, μ i) + (∑ i ∈ s, w i) d(z, x)`. -/
lemma sum_mul_expFamilyDiv_left_eq {ι : Type*} (s : Finset ι) (w μ : ι → ℝ) {x : ℝ}
    (hx : (∑ i ∈ s, w i) * ρ.natParam T x = ∑ i ∈ s, w i * ρ.natParam T (μ i)) (z : ℝ) :
    ∑ i ∈ s, w i * ρ.expFamilyDiv T z (μ i) =
      ∑ i ∈ s, w i * ρ.expFamilyDiv T x (μ i) + (∑ i ∈ s, w i) * ρ.expFamilyDiv T z x := by
  have h (i : ι) : w i * ρ.expFamilyDiv T z (μ i) = w i * ρ.expFamilyDiv T x (μ i) +
      w i * (cgf T ρ (ρ.natParam T x) - cgf T ρ (ρ.natParam T z) + z * ρ.natParam T z -
        x * ρ.natParam T x) + (x - z) * (w i * ρ.natParam T (μ i)) := by
    simp only [expFamilyDiv_def]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ h i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, ← hx, expFamilyDiv_def]
  ring

/-- The mean `x` whose natural parameter is the mean of the natural parameters of the `μ i`,
`i ∈ s`, weighted by nonnegative weights `w`, minimizes `z ↦ ∑ i ∈ s, w i d(z, μ i)` over the
means of the family. -/
lemma sum_mul_expFamilyDiv_left_le {ι : Type*} (s : Finset ι) {w μ : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) {z : ℝ}
    (hx : (∑ i ∈ s, w i) * ρ.natParam T x = ∑ i ∈ s, w i * ρ.natParam T (μ i))
    (hx_mem : x ∈ ρ.expFamilyMeans T) (hz : z ∈ ρ.expFamilyMeans T) :
    ∑ i ∈ s, w i * ρ.expFamilyDiv T x (μ i) ≤ ∑ i ∈ s, w i * ρ.expFamilyDiv T z (μ i) := by
  rw [sum_mul_expFamilyDiv_left_eq s w μ hx z]
  exact le_add_of_nonneg_right (mul_nonneg (Finset.sum_nonneg hw) (expFamilyDiv_nonneg hz hx_mem))

/-- For weights `w₀, w₁ ≥ 0` with `w₀ + w₁ = 1`, the combination `w₀ η(μ₀) + w₁ η(μ₁)` of the
natural parameters of two means of the family is in the interior of the natural parameters. -/
lemma mul_natParam_add_mul_natParam_mem_interior {w₀ w₁ : ℝ} (hμ₀ : μ₀ ∈ ρ.expFamilyMeans T)
    (hμ₁ : μ₁ ∈ ρ.expFamilyMeans T) (hw₀ : 0 ≤ w₀) (hw₁ : 0 ≤ w₁) (hw : w₀ + w₁ = 1) :
    w₀ * ρ.natParam T μ₀ + w₁ * ρ.natParam T μ₁ ∈ interior (integrableExpSet T ρ) :=
  convex_integrableExpSet.interior (natParam_mem_interior_integrableExpSet hμ₀)
    (natParam_mem_interior_integrableExpSet hμ₁) hw₀ hw₁ hw

/-- **The two-point minimizer.** For weights `w₀, w₁ ≥ 0` with `w₀ + w₁ = 1`, the mean
`x_w = ψ'(w₀ η(μ₀) + w₁ η(μ₁))` of the member with the interpolated natural parameter minimizes
`z ↦ w₀ d(z, μ₀) + w₁ d(z, μ₁)` over the means of the family. -/
lemma mul_expFamilyDiv_add_mul_expFamilyDiv_left_le (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    {w₀ w₁ z : ℝ} (hμ₀ : μ₀ ∈ ρ.expFamilyMeans T) (hμ₁ : μ₁ ∈ ρ.expFamilyMeans T) (hw₀ : 0 ≤ w₀)
    (hw₁ : 0 ≤ w₁) (hw : w₀ + w₁ = 1) (hz : z ∈ ρ.expFamilyMeans T) :
    w₀ * ρ.expFamilyDiv T (deriv (cgf T ρ) (w₀ * ρ.natParam T μ₀ + w₁ * ρ.natParam T μ₁)) μ₀ +
        w₁ * ρ.expFamilyDiv T
          (deriv (cgf T ρ) (w₀ * ρ.natParam T μ₀ + w₁ * ρ.natParam T μ₁)) μ₁ ≤
      w₀ * ρ.expFamilyDiv T z μ₀ + w₁ * ρ.expFamilyDiv T z μ₁ := by
  have hη := mul_natParam_add_mul_natParam_mem_interior hμ₀ hμ₁ hw₀ hw₁ hw
  have h := sum_mul_expFamilyDiv_left_le (ρ := ρ) (T := T) Finset.univ (w := ![w₀, w₁])
    (μ := ![μ₀, μ₁]) (Fin.forall_fin_two.mpr ⟨fun _ ↦ hw₀, fun _ ↦ hw₁⟩)
    (x := deriv (cgf T ρ) (w₀ * ρ.natParam T μ₀ + w₁ * ρ.natParam T μ₁))
    (by simp [Fin.sum_univ_two, hw, natParam_deriv_cgf hT hη]) (deriv_cgf_mem_expFamilyMeans hη)
    hz
  simpa [Fin.sum_univ_two] using h

/-! ### The Chernoff point of two means -/

/-- The difference `d(x, μ₀) - d(x, μ₁)` is affine in `x`:
`d(x, μ₀) - d(x, μ₁) = ψ(η(μ₀)) - ψ(η(μ₁)) - x (η(μ₀) - η(μ₁))`. -/
lemma expFamilyDiv_sub_expFamilyDiv (ρ : Measure 𝓧) (T : 𝓧 → ℝ) (x μ₀ μ₁ : ℝ) :
    ρ.expFamilyDiv T x μ₀ - ρ.expFamilyDiv T x μ₁ =
      cgf T ρ (ρ.natParam T μ₀) - cgf T ρ (ρ.natParam T μ₁) -
        x * (ρ.natParam T μ₀ - ρ.natParam T μ₁) := by
  simp only [expFamilyDiv_def]
  ring

/-- **The Chernoff point.** For two distinct means `μ₀` and `μ₁` of the family, the slope
`x* = (ψ(η(μ₀)) - ψ(η(μ₁))) / (η(μ₀) - η(μ₁))` of the log-partition function `ψ` is the mean
`ψ'(η)` of a natural parameter `η` strictly between `η(μ₀)` and `η(μ₁)`, by the mean value
theorem. -/
lemma exists_mem_uIoo_deriv_cgf_eq_slope (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ₀ : μ₀ ∈ ρ.expFamilyMeans T) (hμ₁ : μ₁ ∈ ρ.expFamilyMeans T) (h : μ₀ ≠ μ₁) :
    ∃ η ∈ uIoo (ρ.natParam T μ₀) (ρ.natParam T μ₁), η ∈ interior (integrableExpSet T ρ) ∧
      deriv (cgf T ρ) η = (cgf T ρ (ρ.natParam T μ₀) - cgf T ρ (ρ.natParam T μ₁)) /
        (ρ.natParam T μ₀ - ρ.natParam T μ₁) := by
  have hη : ρ.natParam T μ₀ ≠ ρ.natParam T μ₁ := (strictMonoOn_natParam hT).injOn.ne hμ₀ hμ₁ h
  have h_ord := (convex_integrableExpSet (X := T) (μ := ρ)).interior.ordConnected
  have h_Icc : Icc (ρ.natParam T μ₀ ⊓ ρ.natParam T μ₁) (ρ.natParam T μ₀ ⊔ ρ.natParam T μ₁) ⊆
      interior (integrableExpSet T ρ) :=
    h_ord.uIcc_subset (natParam_mem_interior_integrableExpSet hμ₀)
      (natParam_mem_interior_integrableExpSet hμ₁)
  obtain ⟨η, hη_mem, hη_eq⟩ := exists_deriv_eq_slope (cgf T ρ)
    (inf_lt_sup.2 hη) (analyticOnNhd_cgf.continuousOn.mono h_Icc)
    (analyticOnNhd_cgf.differentiableOn.mono (Ioo_subset_Icc_self.trans h_Icc))
  refine ⟨η, hη_mem, h_Icc (Ioo_subset_Icc_self hη_mem), hη_eq.trans ?_⟩
  rcases le_total (ρ.natParam T μ₀) (ρ.natParam T μ₁) with h01 | h10
  · rw [inf_eq_left.2 h01, sup_eq_right.2 h01, ← neg_div_neg_eq, neg_sub, neg_sub]
  · rw [inf_eq_right.2 h10, sup_eq_left.2 h10]

/-- The slope `x* = (ψ(η(μ₀)) - ψ(η(μ₁))) / (η(μ₀) - η(μ₁))` of two distinct means of the
family is a mean of the family. -/
lemma slope_cgf_natParam_mem_expFamilyMeans (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ₀ : μ₀ ∈ ρ.expFamilyMeans T) (hμ₁ : μ₁ ∈ ρ.expFamilyMeans T) (h : μ₀ ≠ μ₁) :
    (cgf T ρ (ρ.natParam T μ₀) - cgf T ρ (ρ.natParam T μ₁)) /
      (ρ.natParam T μ₀ - ρ.natParam T μ₁) ∈ ρ.expFamilyMeans T := by
  obtain ⟨η, -, hη, hη_eq⟩ := exists_mem_uIoo_deriv_cgf_eq_slope hT hμ₀ hμ₁ h
  exact hη_eq ▸ deriv_cgf_mem_expFamilyMeans hη

/-- The natural parameter of the slope `x* = (ψ(η(μ₀)) - ψ(η(μ₁))) / (η(μ₀) - η(μ₁))` of two
distinct means of the family is `w η(μ₀) + (1 - w) η(μ₁)` for the weight
`w = (η(x*) - η(μ₁)) / (η(μ₀) - η(μ₁))`, which lies in `(0, 1)`. -/
lemma natParam_slope_sub_div_mem_Ioo (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ₀ : μ₀ ∈ ρ.expFamilyMeans T) (hμ₁ : μ₁ ∈ ρ.expFamilyMeans T) (h : μ₀ ≠ μ₁) :
    (ρ.natParam T ((cgf T ρ (ρ.natParam T μ₀) - cgf T ρ (ρ.natParam T μ₁)) /
        (ρ.natParam T μ₀ - ρ.natParam T μ₁)) - ρ.natParam T μ₁) /
      (ρ.natParam T μ₀ - ρ.natParam T μ₁) ∈ Ioo 0 1 := by
  obtain ⟨η, hη_mem, hη, hη_eq⟩ := exists_mem_uIoo_deriv_cgf_eq_slope hT hμ₀ hμ₁ h
  rw [← hη_eq, natParam_deriv_cgf hT hη]
  rcases lt_or_gt_of_ne ((strictMonoOn_natParam hT).injOn.ne hμ₀ hμ₁ h) with h01 | h10
  · rw [uIoo_of_le h01.le] at hη_mem
    exact ⟨div_pos_of_neg_of_neg (by linarith [hη_mem.2]) (by linarith),
      (div_lt_one_of_neg (by linarith)).2 (by linarith [hη_mem.1])⟩
  · rw [uIoo_of_ge h10.le] at hη_mem
    exact ⟨div_pos (by linarith [hη_mem.1]) (by linarith),
      (div_lt_one (by linarith)).2 (by linarith [hη_mem.2])⟩

/-- The slope `x* = (ψ(η(μ₀)) - ψ(η(μ₁))) / (η(μ₀) - η(μ₁))` is at the same divergence from `μ₀`
and `μ₁`: `d(x*, μ₀) = d(x*, μ₁)`, the Chernoff information of the two members. -/
lemma expFamilyDiv_slope_eq (h : ρ.natParam T μ₀ ≠ ρ.natParam T μ₁) :
    ρ.expFamilyDiv T ((cgf T ρ (ρ.natParam T μ₀) - cgf T ρ (ρ.natParam T μ₁)) /
      (ρ.natParam T μ₀ - ρ.natParam T μ₁)) μ₀ =
    ρ.expFamilyDiv T ((cgf T ρ (ρ.natParam T μ₀) - cgf T ρ (ρ.natParam T μ₁)) /
      (ρ.natParam T μ₀ - ρ.natParam T μ₁)) μ₁ := by
  rw [← sub_eq_zero, expFamilyDiv_sub_expFamilyDiv, div_mul_cancel₀ _ (sub_ne_zero.2 h), sub_self]

/-- The slope `x* = (ψ(η(μ₀)) - ψ(η(μ₁))) / (η(μ₀) - η(μ₁))` is
`μ₀ - d(μ₀, μ₁) / (η(μ₀) - η(μ₁))`. -/
lemma slope_cgf_natParam_eq_sub (h : ρ.natParam T μ₀ ≠ ρ.natParam T μ₁) :
    (cgf T ρ (ρ.natParam T μ₀) - cgf T ρ (ρ.natParam T μ₁)) /
        (ρ.natParam T μ₀ - ρ.natParam T μ₁) =
      μ₀ - ρ.expFamilyDiv T μ₀ μ₁ / (ρ.natParam T μ₀ - ρ.natParam T μ₁) := by
  have h' : ρ.natParam T μ₀ - ρ.natParam T μ₁ ≠ 0 := sub_ne_zero.2 h
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_iff h', expFamilyDiv_def]
  ring

/-- The slope `x* = (ψ(η(μ₀)) - ψ(η(μ₁))) / (η(μ₀) - η(μ₁))` is
`μ₁ + d(μ₁, μ₀) / (η(μ₀) - η(μ₁))`. -/
lemma slope_cgf_natParam_eq_add (h : ρ.natParam T μ₀ ≠ ρ.natParam T μ₁) :
    (cgf T ρ (ρ.natParam T μ₀) - cgf T ρ (ρ.natParam T μ₁)) /
        (ρ.natParam T μ₀ - ρ.natParam T μ₁) =
      μ₁ + ρ.expFamilyDiv T μ₁ μ₀ / (ρ.natParam T μ₀ - ρ.natParam T μ₁) := by
  have h' : ρ.natParam T μ₀ - ρ.natParam T μ₁ ≠ 0 := sub_ne_zero.2 h
  rw [← sub_eq_iff_eq_add', eq_div_iff h', sub_mul, div_mul_cancel₀ _ h', expFamilyDiv_def]

end MeasureTheory.Measure
