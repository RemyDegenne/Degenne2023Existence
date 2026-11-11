/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Lower bounds on the binary relative entropy

The binary relative entropy `d(p, q)` is the binary cross-entropy
`p log (1 / q) + (1 - p) log (1 / (1 - q))` minus the binary entropy of `p`, which is at most
`log 2`. Dropping the second term of the cross-entropy gives `p log (1 / q) ≤ d(p, q) + log 2`, the
form in which the change of measure bounds the probability of an event that is unlikely under one
of two laws and likely under the other.

For `p ≤ q`, the second term of `d(p, q)` is at least `q - p`, which gives
`d(p, q) ≥ q klFun (p / q)` with `klFun x = x log x + 1 - x`: a lower bound of the order of `q` when
`p / q` stays away from `1`, as the means tend to `0`. Pinsker's inequality only gives the order
`q²`.

## Main statements

* `LMLExplore.mul_neg_log_le_klBerReal_add_log_two`: for `p ∈ [0, 1]` and `q ∈ (0, 1)`,
  `p log (1 / q) ≤ d(p, q) + log 2` in real numbers.
* `LMLExplore.ofReal_mul_neg_log_le_klBer_add_log_two`: for `p, q ∈ [0, 1]`, the same bound in
  `ℝ≥0∞`, where `log (1 / 0) = ∞`.
* `InformationTheory.antitoneOn_klFun`: `klFun` is antitone on `[0, 1]`.
* `LMLExplore.mul_klFun_div_le_klBerReal`: for `p ≤ q` and `q ∈ (0, 1)`,
  `q klFun (p / q) ≤ d(p, q)`.
* `LMLExplore.klBer_ne_zero_of_klBer_eq`: if `d(z, a) = d(z, b)` for distinct `a, b ∈ [0, 1]`, then
  `d(z, a) ≠ 0`.
-/

@[expose] public section

open Real

open scoped ENNReal

namespace LMLExplore

variable {p q : ℝ}

/-- For `p ∈ [0, 1]` and `q ∈ (0, 1)`, `p log (1 / q) ≤ d(p, q) + log 2`: the binary relative
entropy is the binary cross-entropy minus the binary entropy of `p`, which is at most `log 2`. -/
lemma mul_neg_log_le_klBerReal_add_log_two (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Ioo 0 1) :
    p * -log q ≤ klBerReal p q + log 2 := by
  rw [klBerReal_eq_neg_binEntropy_sub hq.1.ne' hq.2.ne]
  have h : 0 ≤ (1 - p) * -log (1 - q) := mul_nonneg (by linarith [hp.2])
    (neg_nonneg.2 (log_nonpos (by linarith [hq.2]) (by linarith [hq.1])))
  linarith [binEntropy_le_log_two (p := p)]

/-- **Lower bound on the binary relative entropy by the cross-entropy**: for `p, q ∈ [0, 1]`,
`p log (1 / q) ≤ d(p, q) + log 2`, in `ℝ≥0∞`, where `log (1 / q) = -log q` is `∞` at `q = 0`. -/
lemma ofReal_mul_neg_log_le_klBer_add_log_two (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    ENNReal.ofReal p * (-ENNReal.log (ENNReal.ofReal q)).toENNReal ≤
      klBer p q + ENNReal.ofReal (log 2) := by
  rcases hq.1.eq_or_lt with rfl | hq0
  · -- For `q = 0`, both sides are `∞` unless `p = 0`.
    rcases hp.1.eq_or_lt with rfl | hp0
    · simp
    have : klBer p 0 = ∞ := (klBer_eq_top_iff hp ⟨le_rfl, zero_le_one⟩).2 (by simp [hp0.ne'])
    simp [this]
  rcases hq.2.eq_or_lt with rfl | hq1
  · simp
  rw [ENNReal.log_ofReal_of_pos hq0, ← EReal.coe_neg, EReal.real_coe_toENNReal,
    ← ENNReal.ofReal_mul hp.1, klBer_eq_ofReal_klBerReal hp hq (klBer_ne_top ⟨hq0, hq1⟩)]
  exact (ENNReal.ofReal_le_ofReal (mul_neg_log_le_klBerReal_add_log_two hp ⟨hq0, hq1⟩)).trans
    ENNReal.ofReal_add_le

end LMLExplore

namespace InformationTheory

/-- `klFun x = x log x + 1 - x` is antitone on `[0, 1]`: it is convex on `[0, ∞)` with its minimum
`0` at `1`. -/
lemma antitoneOn_klFun : AntitoneOn klFun (Set.Icc 0 1) := by
  intro r hr c hc hrc
  rcases hrc.eq_or_lt with rfl | hrc
  · exact le_rfl
  rcases hc.2.eq_or_lt with rfl | hc1
  · rw [klFun_one]
    exact klFun_nonneg hr.1
  refine convexOn_klFun.le_left_of_right_le hr.1 (by simp : (1 : ℝ) ∈ Set.Ici 0) ?_ ?_
  · rw [openSegment_eq_Ioo (hrc.trans hc1)]
    exact ⟨hrc, hc1⟩
  · rw [klFun_one]
    exact klFun_nonneg hc.1

end InformationTheory

namespace LMLExplore

open InformationTheory

variable {p q : ℝ}

/-- **Lower bound on the binary relative entropy by `klFun`**: for `p ≤ q` with `q ∈ (0, 1)`,
`q klFun (p / q) ≤ d(p, q)`, with `klFun x = x log x + 1 - x`. The first term of `d(p, q)` is
`q (p / q) log (p / q)`, and the second, `(1 - p) log ((1 - p) / (1 - q))`, is at least `q - p`.
-/
lemma mul_klFun_div_le_klBerReal (hpq : p ≤ q) (hq : q ∈ Set.Ioo 0 1) :
    q * klFun (p / q) ≤ klBerReal p q := by
  have h1 : 0 < 1 - p := by linarith [hq.2]
  have h2 : 0 < 1 - q := by linarith [hq.2]
  have hq0 := hq.1.ne'
  have h3 : (1 - p) * (1 - ((1 - p) / (1 - q))⁻¹) = q - p := by
    field_simp
    ring
  have h4 : q - p ≤ (1 - p) * log ((1 - p) / (1 - q)) := by
    rw [← h3]
    exact mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos (div_pos h1 h2)) h1.le
  have h5 : q * (p / q * log (p / q) + 1 - p / q) = p * log (p / q) + (q - p) := by
    field_simp
    ring
  rw [klBerReal_def, klFun_apply, h5]
  linarith

/-- If the binary relative entropies `d(z, a)` and `d(z, b)` to two distinct points `a, b ∈ [0, 1]`
are equal, they do not vanish: `d(z, ·)` vanishes only at the clamp of `z` to `[0, 1]`. -/
lemma klBer_ne_zero_of_klBer_eq {z a b : ℝ} (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1)
    (hab : a ≠ b) (h : klBer z a = klBer z b) : klBer z a ≠ 0 := by
  have key {c : ℝ} (hc : c ∈ Set.Icc 0 1) (h0 : klBer z c = 0) :
      (Set.projIcc 0 1 zero_le_one z : ℝ) = c := by
    rw [← klBer_projIcc, Set.projIcc_of_mem zero_le_one hc] at h0
    exact (klBer_eq_zero_iff (Set.projIcc 0 1 zero_le_one z).2 hc).1 h0
  exact fun h0 ↦ hab ((key ha h0).symm.trans (key hb (h ▸ h0)))

end LMLExplore
