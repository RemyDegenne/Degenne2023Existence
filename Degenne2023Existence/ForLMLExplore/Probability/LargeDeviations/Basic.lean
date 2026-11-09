/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Data.EReal.Inv
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.LiminfLimsup
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

## Main definitions

* `LMLExplore.IsGoodRateFunction I`: `I` is lower semicontinuous with compact sublevel sets.
* `LMLExplore.IsLDP P I`: the sequence of measures `P` satisfies the large deviation principle with
  speed `n` and rate function `I`.

## References

* [DZ98] A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed.,
  Springer, 1998, Section 1.2.
-/

@[expose] public section

open MeasureTheory Filter

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

end LMLExplore
