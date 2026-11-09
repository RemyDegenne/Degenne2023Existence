/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.EReal.Inv
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Defs

/-!
# Large deviation principles

A sequence of measures `P n` on a topological space `X` satisfies the *large deviation principle*
(LDP) with speed `n` and rate function `I : X → [0, ∞]` if `I` is lower semicontinuous and, for
every set `s`,
`-inf_{x ∈ int s} I(x) ≤ liminf_n (1 / n) log P n s` and
`limsup_n (1 / n) log P n s ≤ -inf_{x ∈ cl s} I(x)`.
The rate function is *good* if its sublevel sets `{x | I x ≤ c}` are compact. The logarithms are
`EReal`-valued, `log 0 = ⊥`.

This is the definition of A. Dembo and O. Zeitouni, with the bounds stated for every set: the
measure of a set that is not measurable is its outer measure, and the bounds for every set follow
from the bounds for the measurable ones by monotonicity, since interiors are open and closures are
closed.

The bounds are usually proved from exponential bounds on the probabilities: an upper bound
`P n s ≤ C exp (-(n r))` for every `r < c` gives `limsup_n (1 / n) log P n s ≤ -c`, and a lower
bound `C exp (-(n r)) ≤ P n s` for every `r > c` gives `-c ≤ liminf_n (1 / n) log P n s`. The
lower bound of the principle reduces to the neighbourhoods of single points, and the upper bound
to the closed sets.

## Main definitions

* `LMLExplore.IsGoodRateFunction I`: `I` is lower semicontinuous with compact sublevel sets.
* `LMLExplore.IsLDP P I`: the sequence of measures `P` satisfies the large deviation principle with
  speed `n` and rate function `I`.

## Main statements

* `LMLExplore.limsup_log_div_le_neg_of_le_mul_exp`: exponential upper bounds at every rate `r < c`
  give `limsup_n (1 / n) log u n ≤ -c`.
* `LMLExplore.neg_le_liminf_log_div_of_mul_exp_le`: exponential lower bounds at every rate `r > c`
  give `-c ≤ liminf_n (1 / n) log u n`.
* `LMLExplore.IsLDP.of_isClosed_of_mem_nhds`: the large deviation principle from the upper bound on
  the closed sets and the lower bound on the neighbourhoods of each point.

## References

* [DZ98] A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed.,
  Springer, 1998, Section 1.2.
-/

@[expose] public section

open MeasureTheory Filter Topology

open scoped ENNReal NNReal

namespace LMLExplore

variable {X : Type*} [TopologicalSpace X] {mX : MeasurableSpace X}

/-- The function `I : X → [0, ∞]` is a *good rate function*: it is lower semicontinuous and its
sublevel sets `{x | I x ≤ c}`, `c` finite, are compact [DZ98, Section 1.2]. -/
def IsGoodRateFunction (I : X → ℝ≥0∞) : Prop :=
  LowerSemicontinuous I ∧ ∀ c : ℝ≥0, IsCompact {x | I x ≤ c}

/-- The sequence of measures `P n` satisfies the *large deviation principle* with speed `n` and
rate function `I` [DZ98, Section 1.2]: `I` is lower semicontinuous and, for every set `s`,
`-inf_{x ∈ int s} I(x) ≤ liminf_n (1 / n) log P n s` and
`limsup_n (1 / n) log P n s ≤ -inf_{x ∈ cl s} I(x)`. -/
structure IsLDP (P : ℕ → Measure X) (I : X → ℝ≥0∞) : Prop where
  /-- The rate function is lower semicontinuous. -/
  lowerSemicontinuous : LowerSemicontinuous I
  /-- The lower bound, through the interior. -/
  neg_iInf_interior_le_liminf (s : Set X) :
    -(((⨅ x ∈ interior s, I x : ℝ≥0∞)) : EReal) ≤
      liminf (fun n : ℕ ↦ ENNReal.log (P n s) / n) atTop
  /-- The upper bound, through the closure. -/
  limsup_le_neg_iInf_closure (s : Set X) :
    limsup (fun n : ℕ ↦ ENNReal.log (P n s) / n) atTop ≤
      -(((⨅ x ∈ closure s, I x : ℝ≥0∞)) : EReal)

/-! ### Exponential bounds -/

/-- The logarithm of `C exp (-(n r))`, divided by `n`, is `log C / n - r`, for a finite `C > 0`. -/
private lemma log_mul_exp_div {C : ℝ≥0∞} (hC0 : C ≠ 0) (hC : C ≠ ⊤) {n : ℕ} (hn : 1 ≤ n)
    (r : ℝ) :
    ENNReal.log (C * ENNReal.ofReal (Real.exp (-(n * r)))) / n =
      ((Real.log C.toReal / n - r : ℝ) : EReal) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [ENNReal.log_mul_add, ← ENNReal.ofReal_toReal hC,
    ENNReal.log_ofReal_of_pos (ENNReal.toReal_pos hC0 hC),
    ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp, ← EReal.coe_add,
    ← EReal.coe_natCast, ← EReal.coe_div]
  congr 1
  rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  field_simp
  ring

/-- **Exponential upper bounds give the upper bound of a large deviation principle.** If for every
real `r < c` there is a finite `C` with `u n ≤ C exp (-(n r))` eventually, then
`limsup_n (1 / n) log u n ≤ -c`. -/
lemma limsup_log_div_le_neg_of_le_mul_exp {u : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ r : ℝ, (r : EReal) < c → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ᶠ n : ℕ in atTop, u n ≤ C * ENNReal.ofReal (Real.exp (-(n * r)))) :
    limsup (fun n : ℕ ↦ ENNReal.log (u n) / n) atTop ≤ -(c : EReal) := by
  rw [EReal.le_neg]
  refine EReal.ge_of_forall_gt_iff_ge.1 fun r hr ↦ ?_
  rw [EReal.le_neg]
  obtain ⟨C, hC, hu⟩ := h r hr
  have hC0 : max C 1 ≠ 0 := (zero_lt_one.trans_le (le_max_right C 1)).ne'
  have hCtop : max C 1 ≠ ⊤ := max_ne_top hC ENNReal.one_ne_top
  have h_tendsto : Tendsto (fun n : ℕ ↦ ((Real.log (max C 1).toReal / n - r : ℝ) : EReal)) atTop
      (𝓝 (-(r : EReal))) := by
    rw [← EReal.coe_neg]
    refine EReal.tendsto_coe.2 ?_
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (Real.log (max C 1).toReal)).sub_const r
  rw [← h_tendsto.limsup_eq]
  refine limsup_le_limsup ?_
  filter_upwards [hu, eventually_ge_atTop 1] with n hn hn1
  rw [← log_mul_exp_div hC0 hCtop hn1]
  refine EReal.div_le_div_right_of_nonneg (by exact_mod_cast n.cast_nonneg) ?_
  exact ENNReal.log_monotone (hn.trans (by gcongr; exact le_max_left _ _))

/-- **Exponential lower bounds give the lower bound of a large deviation principle.** If for every
real `r > c` there is a nonzero `C` with `C exp (-(n r)) ≤ u n` eventually, then
`-c ≤ liminf_n (1 / n) log u n`. -/
lemma neg_le_liminf_log_div_of_mul_exp_le {u : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ r : ℝ, (c : EReal) < r → ∃ C : ℝ≥0∞, C ≠ 0 ∧
      ∀ᶠ n : ℕ in atTop, C * ENNReal.ofReal (Real.exp (-(n * r))) ≤ u n) :
    -(c : EReal) ≤ liminf (fun n : ℕ ↦ ENNReal.log (u n) / n) atTop := by
  rw [EReal.neg_le]
  refine EReal.le_of_forall_lt_iff_le.1 fun r hr ↦ ?_
  rw [EReal.neg_le]
  obtain ⟨C, hC, hu⟩ := h r hr
  have hC0 : min C 1 ≠ 0 := by simp [hC]
  have hCtop : min C 1 ≠ ⊤ := ((min_le_right C 1).trans_lt ENNReal.one_lt_top).ne
  have h_tendsto : Tendsto (fun n : ℕ ↦ ((Real.log (min C 1).toReal / n - r : ℝ) : EReal)) atTop
      (𝓝 (-(r : EReal))) := by
    rw [← EReal.coe_neg]
    refine EReal.tendsto_coe.2 ?_
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (Real.log (min C 1).toReal)).sub_const r
  rw [← h_tendsto.liminf_eq]
  refine liminf_le_liminf ?_
  filter_upwards [hu, eventually_ge_atTop 1] with n hn hn1
  rw [← log_mul_exp_div hC0 hCtop hn1]
  refine EReal.div_le_div_right_of_nonneg (by exact_mod_cast n.cast_nonneg) ?_
  refine ENNReal.log_monotone (le_trans ?_ hn)
  gcongr
  exact min_le_left _ _

/-! ### Reduction to closed sets and to neighbourhoods of points -/

/-- **The large deviation principle from the bounds on closed sets and neighbourhoods.** If `I` is
lower semicontinuous, `limsup_n (1 / n) log P n s ≤ -inf_s I` for every closed set `s`, and
`-I(x) ≤ liminf_n (1 / n) log P n s` for every neighbourhood `s` of every point `x`, then the
measures `P n` satisfy the large deviation principle with rate function `I`. -/
lemma IsLDP.of_isClosed_of_mem_nhds {P : ℕ → Measure X} {I : X → ℝ≥0∞}
    (hI : LowerSemicontinuous I)
    (h_upper : ∀ s, IsClosed s →
      limsup (fun n : ℕ ↦ ENNReal.log (P n s) / n) atTop ≤ -(((⨅ x ∈ s, I x : ℝ≥0∞)) : EReal))
    (h_lower : ∀ x, ∀ s ∈ 𝓝 x,
      -(I x : EReal) ≤ liminf (fun n : ℕ ↦ ENNReal.log (P n s) / n) atTop) :
    IsLDP P I where
  lowerSemicontinuous := hI
  neg_iInf_interior_le_liminf s := by
    have h_mono (n : ℕ) :
        ENNReal.log (P n (interior s)) / n ≤ ENNReal.log (P n s) / n :=
      EReal.div_le_div_right_of_nonneg (by exact_mod_cast n.cast_nonneg)
        (ENNReal.log_monotone (measure_mono interior_subset))
    refine le_trans ?_ (liminf_le_liminf (Eventually.of_forall h_mono))
    rw [EReal.neg_le]
    set L := liminf (fun n : ℕ ↦ ENNReal.log (P n (interior s)) / n) atTop
    rcases le_or_gt (-L) 0 with hL | hL
    · exact hL.trans (EReal.coe_ennreal_nonneg _)
    rw [← EReal.coe_toENNReal hL.le, EReal.coe_ennreal_le_coe_ennreal_iff]
    refine le_iInf₂ fun x hx ↦ ?_
    rw [← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_toENNReal hL.le, EReal.neg_le]
    exact h_lower x _ (isOpen_interior.mem_nhds hx)
  limsup_le_neg_iInf_closure s := by
    have h_mono (n : ℕ) :
        ENNReal.log (P n s) / n ≤ ENNReal.log (P n (closure s)) / n :=
      EReal.div_le_div_right_of_nonneg (by exact_mod_cast n.cast_nonneg)
        (ENNReal.log_monotone (measure_mono subset_closure))
    exact (limsup_le_limsup (Eventually.of_forall h_mono)).trans (h_upper _ isClosed_closure)

end LMLExplore
