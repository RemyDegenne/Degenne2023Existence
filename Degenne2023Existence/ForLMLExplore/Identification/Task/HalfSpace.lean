/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.ForLMLExplore.Identification.FixedBudgetComplexity
public import Degenne2023Existence.ForLMLExplore.Identification.Task.ExpFamily
public import LMLExplore.Identification.Task.Classical

/-!
# Static proportions in Gaussian half-space identification

In half-space identification (`halfSpaceTask ν id u`) the correct answer of a vector of means `μ`
is the sign of `u ⬝ᵥ μ`, and the alternatives to `μ` are the vectors of means on the other side of
the hyperplane `u ⬝ᵥ λ = 0`. Let the arm `a` have the Gaussian law of mean `μ a` and variance
`v a ≠ 0`, and write `L = ∑ a, |u a| √(v a)`.

* For every allocation `w` of the simplex, moving `μ` across the hyperplane along the direction
  `(sign (u a) √(v a))_a` reaches alternatives `λ` with `u ⬝ᵥ λ = (1 - t) u ⬝ᵥ μ`, for `t > 1`,
  at a cost `∑ a, w a KL(ν_a(λ), ν_a(μ))` at most `t² (u ⬝ᵥ μ)² / (2 L²)`.
* At the allocation `w a = |u a| √(v a) / L`, by the Cauchy–Schwarz inequality, every alternative
  costs at least `(u ⬝ᵥ μ)² / (2 L²)`.

Hence the static-proportions difficulty is `H^{sp}(μ) = 2 L² / (u ⬝ᵥ μ)²` [D23, Lemma 15], and at
every admissible `μ`, `max_w inf_{λ ∈ Alt(μ)} H^{sp}(λ) ∑ a, w a KL(ν_a(μ), ν_a(λ)) ≤ 1`: the
lower bound of [D23, Theorem 3] for the difficulty `H^{sp}` is at least `1` [D23, Lemma 16].
For a common variance, LMLExplore's `LMLExplore/Identification/Task/HalfSpace.lean` computes the
characteristic time, with the cost in the other order (equal for Gaussian arms).

## Main statements

* `LMLExplore.Identification.mem_alternatives_halfSpaceTask_iff`: the alternatives of half-space
  identification.
* `LMLExplore.Identification.inv_staticDifficulty_halfSpaceTask_gaussianReal`,
  `LMLExplore.Identification.staticDifficulty_halfSpaceTask_gaussianReal`: [D23, Lemma 15].
* `LMLExplore.Identification.iSup_iInf_staticDifficulty_mul_cost_halfSpaceTask_le_one`:
  [D23, proof of Lemma 16].

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α Θ 𝓨 : Type*} [Fintype α] {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  {u : α → ℝ}

/-- The alternatives to a model `θ` with `u ⬝ᵥ mean θ ≠ 0` in half-space identification are the
models on the other side of the hyperplane: `u ⬝ᵥ mean θ * u ⬝ᵥ mean θ' < 0`. -/
lemma mem_alternatives_halfSpaceTask_iff (ν : Θ → Kernel α 𝓨) [∀ θ, IsMarkovKernel (ν θ)]
    (mean : Θ → α → ℝ) {θ θ' : Θ} (hθ : u ⬝ᵥ mean θ ≠ 0) :
    θ' ∈ (halfSpaceTask ν mean u).alternatives θ ↔ u ⬝ᵥ mean θ * u ⬝ᵥ mean θ' < 0 := by
  simp only [IdentTask.alternatives, M_halfSpaceTask, correct_halfSpaceTask_eq_singleton,
    Set.disjoint_singleton, Set.mem_ofPred_eq, ne_eq, decide_eq_decide, mul_neg_iff]
  grind

/-- For a nonzero vector `u` and positive variances `v`, `∑ a, |u a| √(v a)` is positive. -/
lemma sum_abs_mul_sqrt_pos {v : α → ℝ≥0} (hv : ∀ a, v a ≠ 0) (hu : u ≠ 0) :
    0 < ∑ a, |u a| * √(v a : ℝ) := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hu
  refine Finset.sum_pos' (fun b _ ↦ by positivity) ⟨a, Finset.mem_univ a, ?_⟩
  have : (0 : ℝ) < v a := by have := hv a; positivity
  exact mul_pos (abs_pos.2 ha) (Real.sqrt_pos.2 this)

/-- For a nonzero vector `u` and positive variances `v`, the allocation proportional to
`|u a| √(v a)` belongs to the simplex. -/
lemma abs_mul_sqrt_div_mem_simplex {v : α → ℝ≥0} (hv : ∀ a, v a ≠ 0) (hu : u ≠ 0) :
    (fun a ↦ |u a| * √(v a : ℝ) / ∑ b, |u b| * √(v b : ℝ)) ∈ simplex α := by
  have hL := sum_abs_mul_sqrt_pos hv hu
  refine mem_simplex_iff.2 ⟨fun a ↦ by positivity, ?_⟩
  rw [← Finset.sum_div, div_self hL.ne']

variable {v : α → ℝ≥0} {μ : α → ℝ}

/-- **A direction across the hyperplane** [D23, proof of Lemma 15]. For variances `v a ≠ 0` and
`L = ∑ a, |u a| √(v a)`, the direction `d a = sign (u a) √(v a) / L` has `u ⬝ᵥ d = 1`, and for
every allocation `w` of the simplex and `s : ℝ`,
`∑ a, w a (s d a)² / (2 v a) ≤ s² / (2 L²)`. -/
lemma exists_dotProduct_eq_one_sum_le (hv : ∀ a, v a ≠ 0) (hu : u ≠ 0) :
    ∃ d : α → ℝ, u ⬝ᵥ d = 1 ∧ ∀ w ∈ simplex α, ∀ s : ℝ,
      ∑ a, w a * (s * d a) ^ 2 / (2 * v a) ≤ s ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2) := by
  set L := ∑ a, |u a| * √(v a : ℝ) with hL_def
  have hL : 0 < L := sum_abs_mul_sqrt_pos hv hu
  set d : α → ℝ := fun a ↦ u a * √(v a : ℝ) / (|u a| * L)
  have hd : u ⬝ᵥ d = 1 := by
    have (a : α) : u a * d a = |u a| * √(v a : ℝ) / L := by
      rcases eq_or_ne (u a) 0 with h | h
      · simp [d, h]
      · have : |u a| ≠ 0 := abs_ne_zero.2 h
        simp only [d]
        field_simp
        rw [← sq_abs]
        ring
    rw [dotProduct, Finset.sum_congr rfl fun a _ ↦ this a, ← Finset.sum_div, ← hL_def,
      div_self hL.ne']
  refine ⟨d, hd, fun w hw s ↦ ?_⟩
  have hw0 := (mem_simplex_iff.1 hw).1
  set C := s ^ 2 / (2 * L ^ 2)
  have hC : 0 ≤ C := by positivity
  calc ∑ a, w a * (s * d a) ^ 2 / (2 * v a)
      ≤ ∑ a, w a * C := Finset.sum_le_sum fun a _ ↦ ?_
    _ = C := by rw [← Finset.sum_mul, (mem_simplex_iff.1 hw).2, one_mul]
  have hva : (0 : ℝ) < v a := by have := hv a; positivity
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hw0 a)
  rcases eq_or_ne (u a) 0 with h | h
  · simpa [d, h] using hC
  · refine le_of_eq ?_
    have : |u a| ≠ 0 := abs_ne_zero.2 h
    simp only [d, C]
    rw [mul_pow, div_pow, mul_pow, mul_pow, Real.sq_sqrt hva.le, ← sq_abs (u a)]
    field_simp

/-- **Crossing a hyperplane costs at least the squared distance to it** [D23, proof of
Lemma 15]. For variances `v a ≠ 0`, `L = ∑ a, |u a| √(v a)` and two vectors `x`, `y` on different
sides of the hyperplane `u ⬝ᵥ z = 0` (or on it),
`(u ⬝ᵥ x)² / (2 L²) ≤ ∑ a, w a (y a - x a)² / (2 v a)` at the allocation
`w a = |u a| √(v a) / L`, by the Cauchy–Schwarz inequality. -/
lemma sq_dotProduct_div_le_sum (hv : ∀ a, v a ≠ 0) (hu : u ≠ 0) {x y : α → ℝ}
    (hxy : u ⬝ᵥ x * u ⬝ᵥ y ≤ 0) :
    (u ⬝ᵥ x) ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2) ≤
      ∑ a, |u a| * √(v a : ℝ) / (∑ b, |u b| * √(v b : ℝ)) * (y a - x a) ^ 2 / (2 * v a) := by
  set L := ∑ a, |u a| * √(v a : ℝ) with hL_def
  have hL : 0 < L := sum_abs_mul_sqrt_pos hv hu
  set S := ∑ a, |u a| * √(v a : ℝ) / L * (y a - x a) ^ 2 / (2 * v a)
  have h1 : (u ⬝ᵥ x) ^ 2 ≤ (u ⬝ᵥ (x - y)) ^ 2 := by
    rw [dotProduct_sub]
    nlinarith
  have h2 : (u ⬝ᵥ (x - y)) ^ 2 ≤
      (∑ a, |u a| * √(v a : ℝ) * L) * ∑ a, |u a| * √(v a : ℝ) * (x a - y a) ^ 2 / (L * v a) := by
    rw [dotProduct]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun a _ ↦ by positivity)
      (fun a _ ↦ by positivity) fun a _ ↦ le_of_eq ?_
    have hva : (0 : ℝ) < v a := by have := hv a; positivity
    simp only [Pi.sub_apply]
    field_simp
    rw [sq_abs, Real.sq_sqrt hva.le]
    ring
  have h3 : ∑ a, |u a| * √(v a : ℝ) * L = L ^ 2 := by rw [← Finset.sum_mul, ← hL_def, sq]
  have h4 : ∑ a, |u a| * √(v a : ℝ) * (x a - y a) ^ 2 / (L * v a) = 2 * S := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have hva : (0 : ℝ) < v a := by have := hv a; positivity
    field_simp
    ring
  rw [h3, h4] at h2
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **Moving across the hyperplane** [D23, proof of Lemma 15]. For Gaussian arms with variances
`v a ≠ 0` and `t > 1`, the vector of means `λ = μ - t (u ⬝ᵥ μ) d`, with
`d a = sign (u a) √(v a) / L` and `L = ∑ a, |u a| √(v a)`, is an alternative to `μ` with
`u ⬝ᵥ λ = (1 - t) u ⬝ᵥ μ`, and for every allocation `w` of the simplex its cost
`∑ a, w a KL(ν_a(λ), ν_a(μ))` is at most `t² (u ⬝ᵥ μ)² / (2 L²)`. -/
lemma exists_mem_alternatives_halfSpaceTask_gaussianReal (ν : (α → ℝ) → Kernel α ℝ)
    [∀ μ, IsMarkovKernel (ν μ)] (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) (hu : u ≠ 0) (hμ : u ⬝ᵥ μ ≠ 0) {t : ℝ}
    (ht : 1 < t) :
    ∃ μ' ∈ (halfSpaceTask ν id u).alternatives μ, u ⬝ᵥ μ' = (1 - t) * u ⬝ᵥ μ ∧
      ∀ w ∈ simplex α, (halfSpaceTask ν id u).cost w μ' μ ≤
        ENNReal.ofReal (t ^ 2 * ((u ⬝ᵥ μ) ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2))) := by
  obtain ⟨d, hd, hdw⟩ := exists_dotProduct_eq_one_sum_le hv hu
  have hdot : u ⬝ᵥ (μ - (t * u ⬝ᵥ μ) • d) = (1 - t) * u ⬝ᵥ μ := by
    rw [dotProduct_sub, dotProduct_smul, hd, smul_eq_mul]
    ring
  refine ⟨μ - (t * u ⬝ᵥ μ) • d, ?_, hdot, fun w hw ↦ ?_⟩
  · rw [mem_alternatives_halfSpaceTask_iff ν id hμ, id_eq, id_eq, hdot]
    have : 0 < (u ⬝ᵥ μ) ^ 2 := by positivity
    nlinarith
  rw [IdentTask.cost_gaussianReal (task := halfSpaceTask ν id u) hv (by simpa using hν)
    (mem_simplex_iff.1 hw).1]
  refine ENNReal.ofReal_le_ofReal ((le_of_eq ?_).trans ((hdw w hw (t * u ⬝ᵥ μ)).trans_eq
    (by ring)))
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_sub_cancel_left, neg_sq]

/-- **Crossing the hyperplane costs at least the squared distance to it** [D23, proof of
Lemma 15]. For Gaussian arms with variances `v a ≠ 0`, the allocation `w a = |u a| √(v a) / L`,
with `L = ∑ a, |u a| √(v a)`, and a vector of means `λ` on the other side of the hyperplane from
`μ` (or on it), `(u ⬝ᵥ μ)² / (2 L²) ≤ ∑ a, w a KL(ν_a(λ), ν_a(μ))`, by the Cauchy–Schwarz
inequality (`sq_dotProduct_div_le_sum`). -/
lemma ofReal_le_cost_halfSpaceTask_gaussianReal (ν : (α → ℝ) → Kernel α ℝ)
    [∀ μ, IsMarkovKernel (ν μ)] (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) (hu : u ≠ 0) {μ' : α → ℝ}
    (hμ' : u ⬝ᵥ μ * u ⬝ᵥ μ' ≤ 0) :
    ENNReal.ofReal ((u ⬝ᵥ μ) ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2)) ≤
      (halfSpaceTask ν id u).cost (fun a ↦ |u a| * √(v a : ℝ) / ∑ b, |u b| * √(v b : ℝ))
        μ' μ := by
  rw [IdentTask.cost_gaussianReal (task := halfSpaceTask ν id u) hv (by simpa using hν)
    (mem_simplex_iff.1 (abs_mul_sqrt_div_mem_simplex hv hu)).1]
  exact ENNReal.ofReal_le_ofReal (sq_dotProduct_div_le_sum hv hu hμ')

/-- **The static-proportions difficulty of Gaussian half-space identification**
[D23, Lemma 15]. For Gaussian arms with variances `v a ≠ 0` and the half-space task with normal
vector `u ≠ 0`, every admissible model `μ` (with `u ⬝ᵥ μ ≠ 0`) has
`H^{sp}(μ)⁻¹ = (u ⬝ᵥ μ)² / (2 (∑ a, |u a| √(v a))²)`, attained at the allocation proportional to
`|u a| √(v a)`. -/
lemma inv_staticDifficulty_halfSpaceTask_gaussianReal (ν : (α → ℝ) → Kernel α ℝ)
    [∀ μ, IsMarkovKernel (ν μ)] (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) (hu : u ≠ 0) (hμ : u ⬝ᵥ μ ≠ 0) :
    ((halfSpaceTask ν id u).staticDifficulty μ)⁻¹ =
      ENNReal.ofReal ((u ⬝ᵥ μ) ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2)) := by
  set C := (u ⬝ᵥ μ) ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2)
  rw [IdentTask.staticDifficulty, inv_inv]
  refine le_antisymm (iSup₂_le fun w hw ↦ ?_) ?_
  · -- The alternatives `μ - t (u ⬝ᵥ μ) d` cost at most `t² C`, for every `t > 1`.
    have key (t : ℝ) (ht : 1 < t) :
        ⨅ μ' ∈ (halfSpaceTask ν id u).alternatives μ, (halfSpaceTask ν id u).cost w μ' μ ≤
          ENNReal.ofReal (t ^ 2 * C) := by
      obtain ⟨μ', hμ', -, hcost⟩ :=
        exists_mem_alternatives_halfSpaceTask_gaussianReal ν hv hν hu hμ ht
      exact (iInf₂_le μ' hμ').trans (hcost w hw)
    have hlim : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (t ^ 2 * C)) (𝓝[>] 1)
        (𝓝 (ENNReal.ofReal C)) := by
      have hc : Continuous fun t : ℝ ↦ ENNReal.ofReal (t ^ 2 * C) :=
        ENNReal.continuous_ofReal.comp ((continuous_pow 2).mul continuous_const)
      simpa using hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (1 : ℝ)))
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall key)
  · -- At the allocation proportional to `|u a| √(v a)`, every alternative costs at least `C`.
    refine le_iSup₂_of_le _ (abs_mul_sqrt_div_mem_simplex hv hu) (le_iInf₂ fun μ' hμ' ↦ ?_)
    exact ofReal_le_cost_halfSpaceTask_gaussianReal ν hv hν hu
      ((mem_alternatives_halfSpaceTask_iff ν id hμ).1 hμ').le

/-- **The static-proportions difficulty of Gaussian half-space identification**
[D23, Lemma 15]. Under the assumptions of `inv_staticDifficulty_halfSpaceTask_gaussianReal`,
`H^{sp}(μ) = 2 (∑ a, |u a| √(v a))² / (u ⬝ᵥ μ)²`. -/
lemma staticDifficulty_halfSpaceTask_gaussianReal (ν : (α → ℝ) → Kernel α ℝ)
    [∀ μ, IsMarkovKernel (ν μ)] (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) (hu : u ≠ 0) (hμ : u ⬝ᵥ μ ≠ 0) :
    (halfSpaceTask ν id u).staticDifficulty μ =
      ENNReal.ofReal (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2 / (u ⬝ᵥ μ) ^ 2) := by
  have hL := sum_abs_mul_sqrt_pos hv hu
  rw [← inv_inv ((halfSpaceTask ν id u).staticDifficulty μ),
    inv_staticDifficulty_halfSpaceTask_gaussianReal ν hv hν hu hμ,
    ← ENNReal.ofReal_inv_of_pos (by positivity), inv_div]

/-- **Static proportions are optimal for the lower bound** [D23, proof of Lemma 16]. For Gaussian
arms with variances `v a ≠ 0`, the half-space task with normal vector `u ≠ 0` and every
admissible model `μ`,
`max_w inf_{λ ∈ Alt(μ)} H^{sp}(λ) ∑ a, w a KL(ν_a(μ), ν_a(λ)) ≤ 1`: the alternatives
`λ = μ - t (u ⬝ᵥ μ) d` of `exists_mem_alternatives_halfSpaceTask_gaussianReal` have
`H^{sp}(λ) ∑ a, w a KL(ν_a(μ), ν_a(λ)) ≤ t² / (t - 1)²`, which tends to `1` as `t → ∞`. -/
lemma iSup_iInf_staticDifficulty_mul_cost_halfSpaceTask_le_one (ν : (α → ℝ) → Kernel α ℝ)
    [∀ μ, IsMarkovKernel (ν μ)] (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) (hu : u ≠ 0) (hμ : u ⬝ᵥ μ ≠ 0) :
    ⨆ w ∈ simplex α, ⨅ μ' ∈ (halfSpaceTask ν id u).alternatives μ,
      (halfSpaceTask ν id u).staticDifficulty μ' * (halfSpaceTask ν id u).cost w μ μ' ≤ 1 := by
  have hL := sum_abs_mul_sqrt_pos hv hu
  refine iSup₂_le fun w hw ↦ ?_
  have key (t : ℝ) (ht : 1 < t) :
      ⨅ μ' ∈ (halfSpaceTask ν id u).alternatives μ,
        (halfSpaceTask ν id u).staticDifficulty μ' * (halfSpaceTask ν id u).cost w μ μ' ≤
          ENNReal.ofReal ((1 - t⁻¹)⁻¹ ^ 2) := by
    obtain ⟨μ', hμ', hdot, hcost⟩ :=
      exists_mem_alternatives_halfSpaceTask_gaussianReal ν hv hν hu hμ ht
    refine (iInf₂_le μ' hμ').trans ?_
    have ht1 : 1 - t ≠ 0 := by linarith
    have ht0 : t ≠ 0 := by linarith
    have ht1' : t - 1 ≠ 0 := by linarith
    rw [IdentTask.cost_comm_gaussianReal (task := halfSpaceTask ν id u) hv (by simpa using hν),
      staticDifficulty_halfSpaceTask_gaussianReal ν hv hν hu
        (by rw [hdot]; exact mul_ne_zero ht1 hμ)]
    calc _ ≤ ENNReal.ofReal (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2 / (u ⬝ᵥ μ') ^ 2) *
          ENNReal.ofReal (t ^ 2 * ((u ⬝ᵥ μ) ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2))) := by
          gcongr
          exact hcost w hw
      _ = ENNReal.ofReal ((1 - t⁻¹)⁻¹ ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity), hdot]
          congr 1
          field_simp
          ring
  have hlim : Tendsto (fun t : ℝ ↦ ENNReal.ofReal ((1 - t⁻¹)⁻¹ ^ 2)) atTop (𝓝 1) := by
    have : Tendsto (fun t : ℝ ↦ (1 - t⁻¹)⁻¹ ^ 2) atTop (𝓝 ((1 - 0)⁻¹ ^ 2)) :=
      ((tendsto_const_nhds.sub tendsto_inv_atTop_zero).inv₀ (by norm_num)).pow 2
    simpa using ENNReal.tendsto_ofReal this
  exact ge_of_tendsto hlim ((eventually_gt_atTop 1).mono key)

end LMLExplore.Identification
