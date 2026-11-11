/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Setting
public import Degenne2023Existence.ForLMLExplore.Identification.Task.HalfSpace

/-!
# Lemma 15 of [D23]: the static-proportions difficulty of Gaussian half-space identification

For Gaussian arms with variances `σ_a² > 0` and the half-space task with normal vector `u`, the
static-proportions difficulty is `H^{sp}(λ)⁻¹ = (λ ⬝ u)² / (2 (∑ a, |u_a| σ_a)²)`, which is
`(λ ⬝ u)² / 2` for the normalization `∑ a, |u_a| σ_a = 1` of the paper. The proof is
`LMLExplore.Identification.inv_staticDifficulty_halfSpaceTask_gaussianReal`, in
`Degenne2023Existence/ForLMLExplore/Identification/Task/HalfSpace.lean`.

## Main statements

* `Degenne2023Existence.inv_staticDifficulty_halfSpaceTask_gaussian`: [D23, Lemma 15].

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory LMLExplore.Identification

open scoped ENNReal NNReal

namespace Degenne2023Existence

variable {α : Type*} [Fintype α] {mα : MeasurableSpace α}

/-- **The static-proportions difficulty of Gaussian half-space identification**
[D23, Lemma 15]. For Gaussian arms with variances `v a ≠ 0` and the half-space task with normal
vector `u ≠ 0`, every admissible model `μ` (with `u ⬝ μ ≠ 0`) has
`H^{sp}(μ)⁻¹ = (u ⬝ μ)² / (2 (∑ a, |u a| √(v a))²)`.

The paper normalizes `∑ a, |u a| √(v a) = 1`. The statement as frozen at the end of phase 1
assumed `[MeasurableSingletonClass α]`, which the proof does not use. -/
theorem inv_staticDifficulty_halfSpaceTask_gaussian (ν : (α → ℝ) → Kernel α ℝ)
    [∀ μ, IsMarkovKernel (ν μ)] {v : α → ℝ≥0} (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) {u : α → ℝ} (hu : u ≠ 0) {μ : α → ℝ}
    (hμ : u ⬝ᵥ μ ≠ 0) :
    ((halfSpaceTask ν id u).staticDifficulty μ)⁻¹ =
      ENNReal.ofReal ((u ⬝ᵥ μ) ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2)) :=
  inv_staticDifficulty_halfSpaceTask_gaussianReal ν hv hν hu hμ

end Degenne2023Existence
