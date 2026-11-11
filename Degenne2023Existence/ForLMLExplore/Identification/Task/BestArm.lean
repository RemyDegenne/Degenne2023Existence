/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Identification.Task.BestArm

/-!
# The answer sets of best arm identification on vectors of means

In best arm identification on the vectors of means `μ : α → ℝ`, the answer set of the arm `a`, the
vectors with unique best arm `a`, is open (`LMLExplore.Identification.isOpen_answerSet_baiTask`)
and convex. For the task restricted to an open set `S`, the closure of the answer set of `a`
contains every vector of `S` whose largest mean is attained at `a`, so that the closures of the
answer sets cover `S`, and when `S` is also convex each answer set is the interior of its closure.
These are the regularity conditions on the answer sets of Assumption 1 of [D23], under which the
static proportions algorithms of fixed-budget identification have an explicit rate.

These lemmas belong next to the topology of the alternatives of best arm identification in
`LMLExplore/Identification/Task/BestArm.lean` (`LMLExplore.Identification.closure_alt_baiTask`).

## Main statements

* `LMLExplore.Identification.convex_answerSet_baiTask`: the answer sets are convex.
* `LMLExplore.Identification.mem_closure_answerSet_baiTask_restrict`: a vector whose largest mean
  is attained at `a` is a limit of vectors with unique best arm `a`.
* `LMLExplore.Identification.subset_iUnion_closure_answerSet_baiTask_restrict`: the closures of the
  answer sets cover the open set `S`.
* `LMLExplore.Identification.interior_closure_answerSet_baiTask_restrict`: for `S` open and convex,
  each answer set is the interior of its closure.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace LMLExplore.Identification

variable {α 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)] {S : Set (α → ℝ)}

/-- The vectors of means with unique best arm `a` form a convex set, an intersection of open
half-spaces. -/
lemma convex_answerSet_baiTask (a : α) : Convex ℝ ((baiTask ν id).answerSet a) := by
  intro x hx y hy s t hs ht hst
  rw [mem_answerSet_baiTask_iff] at hx hy ⊢
  intro b hb
  have hxb := hx b hb
  have hyb := hy b hb
  simp only [id, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hxb hyb ⊢
  rcases hs.eq_or_lt with rfl | hs'
  · rw [zero_add] at hst
    subst hst
    simpa using hyb
  · nlinarith

/-- For a neighbourhood `S` of a vector of means `μ'` whose largest mean is attained at the arm
`a`, the vector `μ'` lies in the closure of the answer set of `a` in best arm identification
restricted to `S`: raising the mean of `a` makes it the unique best arm. -/
lemma mem_closure_answerSet_baiTask_restrict {μ' : α → ℝ} (hS : S ∈ 𝓝 μ') {a : α}
    (ha : ∀ b, μ' b ≤ μ' a) : μ' ∈ closure (((baiTask ν id).restrict S).answerSet a) := by
  classical
  -- The path `t ↦ μ' + t • Pi.single a 1` tends to `μ'` and lies in the answer set of `a` for
  -- small `t > 0`.
  set f : ℝ → α → ℝ := fun t ↦ μ' + t • Pi.single a 1 with hf
  have hf_tendsto : Tendsto f (𝓝[>] 0) (𝓝 μ') := by
    have hf_cont : Continuous f := by fun_prop
    simpa [hf] using hf_cont.continuousWithinAt.tendsto (x := 0) (s := Set.Ioi 0)
  refine mem_closure_of_tendsto hf_tendsto ?_
  filter_upwards [hf_tendsto.eventually hS, self_mem_nhdsWithin] with t htS ht
  rw [IdentTask.answerSet_restrict]
  refine ⟨(mem_answerSet_baiTask_iff ν id).2 fun b hb ↦ ?_, htS⟩
  simpa [hf, Pi.single_apply, hb] using (ha b).trans_lt (lt_add_of_pos_right _ ht)

/-- For an open set `S` of vectors of means, the closures of the answer sets of best arm
identification restricted to `S` cover `S`: every vector of `S` is a limit of vectors of `S` with
unique best arm one of its arms of largest mean. -/
lemma subset_iUnion_closure_answerSet_baiTask_restrict [Finite α] [Nonempty α] (hS : IsOpen S) :
    S ⊆ ⋃ a, closure (((baiTask ν id).restrict S).answerSet a) := fun μ' hμ' ↦ by
  obtain ⟨a, ha⟩ := Finite.exists_max μ'
  exact Set.mem_iUnion.2 ⟨a, mem_closure_answerSet_baiTask_restrict ν (hS.mem_nhds hμ') ha⟩

/-- For an open convex set `S` of vectors of means, the answer set of the arm `a` in best arm
identification restricted to `S` is the interior of its closure, as an open convex set. -/
lemma interior_closure_answerSet_baiTask_restrict [Finite α] (hS : IsOpen S) (hSc : Convex ℝ S)
    (a : α) :
    interior (closure (((baiTask ν id).restrict S).answerSet a)) =
      ((baiTask ν id).restrict S).answerSet a := by
  have hopen := isOpen_answerSet_baiTask_restrict ν hS a
  rcases Set.eq_empty_or_nonempty (((baiTask ν id).restrict S).answerSet a) with h | h
  · rw [h, closure_empty, interior_empty]
  have hconv : Convex ℝ (((baiTask ν id).restrict S).answerSet a) := by
    rw [IdentTask.answerSet_restrict]
    exact (convex_answerSet_baiTask ν a).inter hSc
  rw [hconv.interior_closure_eq_interior_of_nonempty_interior (hopen.interior_eq.symm ▸ h),
    hopen.interior_eq]

end LMLExplore.Identification
