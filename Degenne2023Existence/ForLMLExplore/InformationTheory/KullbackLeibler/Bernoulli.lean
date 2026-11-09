/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# A lower bound on the binary relative entropy by the cross-entropy

The binary relative entropy `d(p, q)` is the binary cross-entropy
`p log (1 / q) + (1 - p) log (1 / (1 - q))` minus the binary entropy of `p`, which is at most
`log 2`. Dropping the second term of the cross-entropy gives `p log (1 / q) ≤ d(p, q) + log 2`, the
form in which the change of measure bounds the probability of an event that is unlikely under one
of two laws and likely under the other.

## Main statements

* `LMLExplore.mul_neg_log_le_klBerReal_add_log_two`: for `p ∈ [0, 1]` and `q ∈ (0, 1)`,
  `p log (1 / q) ≤ d(p, q) + log 2` in real numbers.
* `LMLExplore.ofReal_mul_neg_log_le_klBer_add_log_two`: for `p, q ∈ [0, 1]`, the same bound in
  `ℝ≥0∞`, where `log (1 / 0) = ∞`.
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
