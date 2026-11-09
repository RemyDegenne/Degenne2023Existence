/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Identification.Task.TransportationCost
public import LMLExplore.InformationTheory.KullbackLeibler.Gaussian

/-!
# Transportation costs of Gaussian arms with per-arm variances

For a task on the vectors of means `μ : α → ℝ` whose arm `a` has the Gaussian law of mean `μ a`
and known variance `v a ≠ 0`, the transportation cost is the weighted squared distance
`cost_μ(w, μ') = ∑ a, w a (μ a - μ' a)² / (2 v a)`, which is symmetric in `μ` and `μ'`. This
generalizes `LMLExplore.Identification.IdentTask.cost_gaussianBandit` (a common variance) of
`LMLExplore/Identification/Task/ExpFamily.lean`, next to which it belongs.

## Main statements

* `LMLExplore.Identification.IdentTask.cost_gaussianReal`: the transportation cost of Gaussian
  arms with per-arm variances.
* `LMLExplore.Identification.IdentTask.cost_comm_gaussianReal`: it is symmetric in the two models.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory

open scoped ENNReal NNReal

namespace LMLExplore.Identification.IdentTask

variable {α ℐ : Type*} [Fintype α] {mα : MeasurableSpace α} {task : IdentTask α (α → ℝ) ℐ ℝ}
  {v : α → ℝ≥0}

/-- For Gaussian arms with variances `v a ≠ 0`, the transportation cost is the weighted squared
distance between the vectors of means: `cost_μ(w, μ') = ∑ a, w a (μ a - μ' a)² / (2 v a)`. -/
lemma cost_gaussianReal (hv : ∀ a, v a ≠ 0) (hν : ∀ μ a, task.ν μ a = gaussianReal (μ a) (v a))
    {w : α → ℝ} (hw : 0 ≤ w) (μ μ' : α → ℝ) :
    task.cost w μ μ' = ENNReal.ofReal (∑ a, w a * (μ a - μ' a) ^ 2 / (2 * v a)) := by
  rw [cost_def, ENNReal.ofReal_sum_of_nonneg fun a _ ↦
    div_nonneg (mul_nonneg (hw a) (sq_nonneg _)) (by positivity)]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [hν, hν, klDiv_gaussianReal_gaussianReal_same_var (hv a), ← ENNReal.ofReal_mul (hw a),
    mul_div_assoc]

/-- For Gaussian arms with variances `v a ≠ 0`, the transportation cost is symmetric:
`cost_μ(w, μ') = cost_{μ'}(w, μ)`. -/
lemma cost_comm_gaussianReal (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, task.ν μ a = gaussianReal (μ a) (v a)) (w μ μ' : α → ℝ) :
    task.cost w μ μ' = task.cost w μ' μ := by
  simp_rw [cost_def, hν, klDiv_gaussianReal_gaussianReal_same_var (hv _), sub_sq_comm]

end LMLExplore.Identification.IdentTask
