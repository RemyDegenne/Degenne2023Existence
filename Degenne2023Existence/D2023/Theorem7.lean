/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Setting
public import Degenne2023Existence.D2023.Theorem3
public import Degenne2023Existence.ForLMLExplore.Identification.Task.HalfSpace

/-!
# Theorem 7 of [D23]: tasks with a flat boundary

If, in a ball around a vector of means `η`, the task has exactly two answers, separated by a
hyperplane through `η`, then for Gaussian arms with known variances every fixed-budget algorithm
family has maximal difficulty ratio at least `1` to the static-proportions difficulty. This
applies to best arm identification, thresholding and positivity.

The paper writes `H_{𝒞^{sp}}` for the oracle difficulty of the class of static proportions
algorithms, equal to the static-proportions difficulty by Theorem 1, and uses a Euclidean ball;
since balls for the different norms of `α → ℝ` contain each other, the hypothesis is the same for
the ball of the sup norm used here. Lemmas 17 and 18 of the paper's proof are misprinted, and the
proof of Lemma 18 uses a value of `H^{sp}` near `η` that Lemma 17 does not give (errata E4 and E5
of `notes/paper-errata.md`).

The proof here takes a shorter route than the paper's, without Lemmas 17 and 18. Write
`L = ∑ a, |u a| √(v a)`.

* Near `η`, `H^{sp}(λ) ≤ 2 L² / (c (u ⬝ᵥ (λ - η))²)` for every `c < 1`
  (`exists_ofReal_le_inv_staticDifficulty_of_hyperplane`, the correction of E5): the allocation
  `c w* + (1 - c) / K`, with the optimal allocation `w*` of the half-space, pays at least
  `c (u ⬝ᵥ (λ - η))² / (2 L²)` for the alternatives inside the ball, and a positive constant for
  those outside it.
* At the model `μ = η - s u`, for `s > 0` small, the alternatives `λ = μ - t (u ⬝ᵥ (μ - η)) d`,
  with `t > 1` and the direction `d` of `LMLExplore.Identification.exists_dotProduct_eq_one_sum_le`,
  stay near `η`, and `H^{sp}(λ) ∑ a, w a KL(ν_a(μ), ν_a(λ)) ≤ t² / (c (t - 1)²)` for every
  allocation `w`. Theorem 3 (`inv_iSup_asymptoticRatio_le`) over the alternatives near `η` bounds
  the inverse of the maximal ratio by this quantity, for the families whose probability of error at
  `μ` tends to `0`; the others have an infinite ratio at `μ`. Take `c = 1 - 1 / t` and `t → ∞`.

## Main statements

* `Degenne2023Existence.one_le_iInf_maxRatio_of_hyperplane`: [D23, Theorem 7].

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Learning LMLExplore LMLExplore.Identification

open scoped ENNReal NNReal

namespace Degenne2023Existence

variable {α ℐ : Type*} [Fintype α] {mα : MeasurableSpace α}

/-- **The static-proportions difficulty near a flat boundary** [D23, proof of Theorem 7], with the
correction E5 of `notes/paper-errata.md`. In the setting of `one_le_iInf_maxRatio_of_hyperplane`,
for every `c ∈ (0, 1)` there is `ρ ∈ (0, r]` such that every model `λ` at distance less than `ρ`
from `η` and off the hyperplane has `c (u ⬝ᵥ (λ - η))² / (2 L²) ≤ H^{sp}(λ)⁻¹`, with
`L = ∑ a, |u a| √(v a)`. The allocation `c w* + (1 - c) / K`, mixing the allocation
`w* a = |u a| √(v a) / L` with the uniform one, pays at least that much for the alternatives
inside the ball of radius `r`, by the Cauchy–Schwarz inequality, and at least
`(1 - c) / K (r / 2)² / (2 ∑ a, v a)` for those outside it. -/
lemma exists_ofReal_le_inv_staticDifficulty_of_hyperplane {task : IdentTask α (α → ℝ) ℐ ℝ}
    {v : α → ℝ≥0} (hv : ∀ a, v a ≠ 0) (hν : ∀ μ a, task.ν μ a = gaussianReal (μ a) (v a))
    {η u : α → ℝ} (hu : u ≠ 0) {r : ℝ} (hr : 0 < r) {i j : ℐ}
    (hball : ∀ μ ∈ Metric.ball η r, (μ ∈ task.M ↔ u ⬝ᵥ (μ - η) ≠ 0) ∧
      (u ⬝ᵥ (μ - η) < 0 → task.correct μ = {i}) ∧ (0 < u ⬝ᵥ (μ - η) → task.correct μ = {j}))
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ ρ > 0, ρ ≤ r ∧ ∀ μ, dist μ η < ρ → u ⬝ᵥ (μ - η) ≠ 0 →
      ENNReal.ofReal (c * ((u ⬝ᵥ (μ - η)) ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2))) ≤
        (task.staticDifficulty μ)⁻¹ := by
  obtain ⟨a₀, -⟩ := Function.ne_iff.1 hu
  have : Nonempty α := ⟨a₀⟩
  set L := ∑ a, |u a| * √(v a : ℝ)
  have hL : 0 < L := sum_abs_mul_sqrt_pos hv hu
  set N := ∑ a, |u a|
  have hN : 0 < N := (Finset.sum_nonneg fun a _ ↦ abs_nonneg (u a)).lt_of_ne'
    (LMLExplore.sum_abs_ne_zero hu)
  have hva (a : α) : (0 : ℝ) < v a := by have := hv a; positivity
  set V := ∑ a, (v a : ℝ)
  have hV : 0 < V := Finset.sum_pos (fun a _ ↦ hva a) Finset.univ_nonempty
  set K := (Fintype.card α : ℝ)
  have hK : 0 < K := by simp only [K]; exact_mod_cast Fintype.card_pos
  set B := (1 - c) / K * (r / 2) ^ 2 / (2 * V)
  have hB : 0 < B := by
    have : 0 < 1 - c := by linarith
    positivity
  set A := N ^ 2 / (2 * L ^ 2)
  have hA : 0 < A := by positivity
  set ρ := min (r / 2) √(B / A)
  have hρ : 0 < ρ := lt_min (by linarith) (Real.sqrt_pos.2 (by positivity))
  have hρr : ρ ≤ r / 2 := min_le_left _ _
  have hAρ : A * ρ ^ 2 ≤ B := by
    have h1 : ρ ^ 2 ≤ B / A :=
      (pow_le_pow_left₀ hρ.le (min_le_right _ _) 2).trans_eq (Real.sq_sqrt (by positivity))
    rwa [le_div_iff₀ hA, mul_comm] at h1
  refine ⟨ρ, hρ, hρr.trans (by linarith), fun μ hμ hμη ↦ ?_⟩
  have hμa (a : α) : |μ a - η a| < ρ := by
    simpa [Real.dist_eq] using (dist_pi_lt_iff hρ).1 hμ a
  have hμr : μ ∈ Metric.ball η r := Metric.mem_ball.2 (hμ.trans_le (hρr.trans (by linarith)))
  -- The allocation `c w* + (1 - c) / K`.
  set w : α → ℝ := c • (fun a ↦ |u a| * √(v a : ℝ) / L) + (1 - c) • fun _ ↦ K⁻¹
  have hw : w ∈ simplex α := convex_simplex α (abs_mul_sqrt_div_mem_simplex hv hu)
    (uniform_mem_simplex α) hc0.le (by linarith) (by ring)
  have hw0 := (mem_simplex_iff.1 hw).1
  have hww (a : α) : c * (|u a| * √(v a : ℝ) / L) ≤ w a := by
    simp only [w, Pi.add_apply, Pi.smul_apply, smul_eq_mul, le_add_iff_nonneg_right]
    exact mul_nonneg (by linarith) (by positivity)
  have hwK (a : α) : (1 - c) / K ≤ w a := by
    simp only [w, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : 0 ≤ c * (|u a| * √(v a : ℝ) / L) := mul_nonneg hc0.le (by positivity)
    rw [div_eq_mul_inv]
    linarith
  rw [IdentTask.staticDifficulty, inv_inv]
  refine le_iSup₂_of_le w hw (le_iInf₂ fun μ' hμ' ↦ ?_)
  rw [IdentTask.cost_gaussianReal hv hν hw0]
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases hμ'r : dist μ' η < r
  · -- Inside the ball, `μ'` is on the other side of the hyperplane.
    have hside : u ⬝ᵥ (μ - η) * u ⬝ᵥ (μ' - η) ≤ 0 := by
      obtain ⟨hμ'M, hμ'i, hμ'j⟩ := hball μ' (Metric.mem_ball.2 hμ'r)
      have hμ'0 := hμ'M.1 hμ'.1
      obtain ⟨-, hμi, hμj⟩ := hball μ hμr
      by_contra hcon
      have hdisj := hμ'.2
      rcases hμη.lt_or_gt with h | h
      · have h' : u ⬝ᵥ (μ' - η) < 0 := hμ'0.lt_or_gt.resolve_right fun h' ↦ by nlinarith
        rw [hμi h, hμ'i h'] at hdisj
        exact Set.disjoint_singleton.1 hdisj rfl
      · have h' : 0 < u ⬝ᵥ (μ' - η) := hμ'0.lt_or_gt.resolve_left fun h' ↦ by nlinarith
        rw [hμj h, hμ'j h'] at hdisj
        exact Set.disjoint_singleton.1 hdisj rfl
    have hcs := sq_dotProduct_div_le_sum hv hu hside
    simp only [Pi.sub_apply, sub_sub_sub_cancel_right] at hcs
    calc c * ((u ⬝ᵥ (μ - η)) ^ 2 / (2 * L ^ 2))
        ≤ c * ∑ a, |u a| * √(v a : ℝ) / L * (μ' a - μ a) ^ 2 / (2 * v a) := by gcongr
      _ = ∑ a, c * (|u a| * √(v a : ℝ) / L) * (μ' a - μ a) ^ 2 / (2 * v a) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ ↦ by ring
      _ ≤ ∑ a, w a * (μ' a - μ a) ^ 2 / (2 * v a) := by
          gcongr with a _
          exact hww a
  · -- Outside the ball, some arm moves by at least `r / 2`.
    obtain ⟨a, ha⟩ : ∃ a, r ≤ |μ' a - η a| := by
      simpa [dist_pi_lt_iff hr, Real.dist_eq] using hμ'r
    have h1 : r / 2 ≤ |μ' a - μ a| := by
      have := hμa a
      have := abs_sub_abs_le_abs_sub (μ' a - η a) (μ a - η a)
      rw [sub_sub_sub_cancel_right] at this
      linarith
    have h2 : (u ⬝ᵥ (μ - η)) ^ 2 ≤ N ^ 2 * ρ ^ 2 := by
      have : |u ⬝ᵥ (μ - η)| ≤ N * ρ :=
        calc |u ⬝ᵥ (μ - η)| ≤ ∑ a, |u a * (μ - η) a| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ a, |u a| * ρ := Finset.sum_le_sum fun a _ ↦ by
              rw [abs_mul, Pi.sub_apply]
              exact mul_le_mul_of_nonneg_left (hμa a).le (abs_nonneg _)
          _ = N * ρ := by rw [Finset.sum_mul]
      rw [← mul_pow, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have hvV : (v a : ℝ) ≤ V :=
      Finset.single_le_sum (f := fun b ↦ (v b : ℝ)) (fun b _ ↦ (hva b).le) (Finset.mem_univ a)
    have h3 : (r / 2) ^ 2 ≤ (μ' a - μ a) ^ 2 := by
      rw [← sq_abs (μ' a - μ a)]
      exact pow_le_pow_left₀ (by linarith) h1 2
    have hwa : 0 ≤ (1 - c) / K := div_nonneg (by linarith) hK.le
    calc c * ((u ⬝ᵥ (μ - η)) ^ 2 / (2 * L ^ 2))
        ≤ (u ⬝ᵥ (μ - η)) ^ 2 / (2 * L ^ 2) := by
          have : 0 ≤ (u ⬝ᵥ (μ - η)) ^ 2 / (2 * L ^ 2) := by positivity
          nlinarith
      _ ≤ A * ρ ^ 2 := by
          rw [show A * ρ ^ 2 = N ^ 2 * ρ ^ 2 / (2 * L ^ 2) by ring]
          gcongr
      _ ≤ B := hAρ
      _ ≤ w a * (μ' a - μ a) ^ 2 / (2 * V) := by
          rw [show B = (1 - c) / K * (r / 2) ^ 2 / (2 * V) from rfl]
          have := hw0 a
          gcongr
          exact hwK a
      _ ≤ w a * (μ' a - μ a) ^ 2 / (2 * v a) := by
          have := hw0 a
          have := hva a
          gcongr
      _ ≤ ∑ b, w b * (μ' b - μ b) ^ 2 / (2 * v b) :=
          Finset.single_le_sum (f := fun b ↦ w b * (μ' b - μ b) ^ 2 / (2 * v b))
            (fun b _ ↦ by have := hw0 b; have := hva b; positivity) (Finset.mem_univ a)

variable [MeasurableSingletonClass α] [MeasurableSpace ℐ]

/-- **Tasks with a flat boundary** [D23, Theorem 7]. Let the arm `a` of the model `μ` have the
Gaussian law of mean `μ a` and variance `v a ≠ 0`. Suppose that in the ball of center `η` and
radius `r > 0`, the admissible models are the vectors off the hyperplane through `η` orthogonal to
`u ≠ 0`, with the single correct answer `i` on one side and `j ≠ i` on the other. Then the infimum
over the fixed-budget algorithm families of the maximal difficulty ratio to the static-proportions
difficulty is at least `1`.

The paper also assumes Assumption 1, which the statement does not need. -/
theorem one_le_iInf_maxRatio_of_hyperplane {task : IdentTask α (α → ℝ) ℐ ℝ} {v : α → ℝ≥0}
    (hv : ∀ a, v a ≠ 0) (hν : ∀ μ a, task.ν μ a = gaussianReal (μ a) (v a)) {η u : α → ℝ}
    (hu : u ≠ 0) {r : ℝ} (hr : 0 < r) {i j : ℐ} (hij : i ≠ j)
    (hball : ∀ μ ∈ Metric.ball η r, (μ ∈ task.M ↔ u ⬝ᵥ (μ - η) ≠ 0) ∧
      (u ⬝ᵥ (μ - η) < 0 → task.correct μ = {i}) ∧ (0 < u ⬝ᵥ (μ - η) → task.correct μ = {j})) :
    1 ≤ ⨅ (𝒜 : ℕ → IdentAlg Unit α ℝ ℐ) (_ : IsFixedBudgetFamily 𝒜),
      task.maxRatio task.staticDifficulty 𝒜 := by
  obtain ⟨d, hd, hdw⟩ := exists_dotProduct_eq_one_sum_le hv hu
  set L := ∑ a, |u a| * √(v a : ℝ)
  have hL : 0 < L := sum_abs_mul_sqrt_pos hv hu
  have hq : 0 < u ⬝ᵥ u := by
    have h0 : u ⬝ᵥ u ≠ 0 := by simpa [dotProduct_self_eq_zero] using hu
    exact h0.lt_or_gt.resolve_left fun h ↦
      (Finset.sum_nonneg fun a _ ↦ mul_self_nonneg (u a)).not_gt h
  refine le_iInf₂ fun 𝒜 h𝒜 ↦ ?_
  rw [← ENNReal.inv_le_one]
  have key (t : ℝ) (ht : 1 < t) :
      (task.maxRatio task.staticDifficulty 𝒜)⁻¹ ≤ ENNReal.ofReal ((1 - t⁻¹)⁻¹ ^ 3) := by
    have ht0 : 0 < t := by linarith
    have hc0 : 0 < 1 - t⁻¹ := by have : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht; linarith
    have hc1 : 1 - t⁻¹ < 1 := by have : 0 < t⁻¹ := inv_pos.2 ht0; linarith
    obtain ⟨ρ, hρ, hρr, hH⟩ :=
      exists_ofReal_le_inv_staticDifficulty_of_hyperplane hv hν hu hr hball hc0 hc1
    -- The model `μ = η - s u` and the alternative `λ = μ + t s (u ⬝ᵥ u) d`, for `s > 0` small.
    have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), dist (η - s • u) η < ρ := by
      have : Tendsto (fun s : ℝ ↦ η - s • u) (𝓝 0) (𝓝 η) := by
        have hc : Continuous fun s : ℝ ↦ η - s • u := by fun_prop
        simpa using hc.tendsto 0
      exact this.eventually (Metric.ball_mem_nhds η hρ)
    have h2 : ∀ᶠ s in 𝓝 (0 : ℝ), dist (η - s • u + (t * s * u ⬝ᵥ u) • d) η < ρ := by
      have : Tendsto (fun s : ℝ ↦ η - s • u + (t * s * u ⬝ᵥ u) • d) (𝓝 0) (𝓝 η) := by
        have hc : Continuous fun s : ℝ ↦ η - s • u + (t * s * u ⬝ᵥ u) • d := by fun_prop
        simpa using hc.tendsto 0
      exact this.eventually (Metric.ball_mem_nhds η hρ)
    obtain ⟨s, hs0, hs1, hs2⟩ := ((eventually_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))).and
      ((h1.and h2).filter_mono nhdsWithin_le_nhds)).exists
    have hs0 : 0 < s := hs0
    set μ := η - s • u
    set lam := η - s • u + (t * s * u ⬝ᵥ u) • d
    have hμη : u ⬝ᵥ (μ - η) = -(s * u ⬝ᵥ u) := by
      simp only [μ, sub_sub_cancel_left, dotProduct_neg, dotProduct_smul, smul_eq_mul]
    have hlamη : u ⬝ᵥ (lam - η) = (t - 1) * (s * u ⬝ᵥ u) := by
      simp only [lam, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul, hd]
      ring
    have hsq : 0 < s * u ⬝ᵥ u := mul_pos hs0 hq
    have hball_of (μ' : α → ℝ) (h : dist μ' η < ρ) : μ' ∈ Metric.ball η r :=
      Metric.mem_ball.2 (h.trans_le hρr)
    have hμ0 : u ⬝ᵥ (μ - η) ≠ 0 := by rw [hμη]; exact neg_ne_zero.2 hsq.ne'
    have hμM : μ ∈ task.M := ((hball μ (hball_of μ hs1)).1).2 hμ0
    have hμi : task.correct μ = {i} :=
      (hball μ (hball_of μ hs1)).2.1 (by rw [hμη]; exact neg_neg_of_pos hsq)
    have hlam0 : 0 < u ⬝ᵥ (lam - η) := by rw [hlamη]; exact mul_pos (by linarith) hsq
    have hlamM : lam ∈ task.M := ((hball lam (hball_of lam hs2)).1).2 hlam0.ne'
    have hlamj : task.correct lam = {j} := (hball lam (hball_of lam hs2)).2.2 hlam0
    -- `H^{sp}` is finite near `η`.
    have hHtop (μ' : α → ℝ) (h : dist μ' η < ρ) (h0 : u ⬝ᵥ (μ' - η) ≠ 0) :
        task.staticDifficulty μ' ≠ ∞ := by
      refine ENNReal.inv_ne_zero.1 (ne_of_gt (lt_of_lt_of_le ?_ (hH μ' h h0)))
      exact ENNReal.ofReal_pos.2 (by positivity)
    by_cases hp : Tendsto (task.errorProb 𝒜 μ) atTop (𝓝 0)
    swap
    · -- A family whose probability of error at `μ` does not tend to `0` has an infinite ratio.
      have htop := task.asymptoticRatio_eq_top (H := task.staticDifficulty)
        (hHtop μ hs1 hμ0) hp
      have hmax : task.maxRatio task.staticDifficulty 𝒜 = ∞ := by
        refine top_unique ?_
        rw [← htop, IdentTask.maxRatio]
        exact le_iSup₂_of_le (f := fun μ' _ ↦ task.asymptoticRatio task.staticDifficulty 𝒜 μ')
          μ hμM le_rfl
      rw [hmax, ENNReal.inv_top]
      exact zero_le
    -- Theorem 3 at `μ`, over the alternatives near `η`.
    set D := {μ' | μ' ∈ task.alternatives μ ∧ dist μ' η < ρ}
    have hD0 (μ' : α → ℝ) (h : μ' ∈ D) : u ⬝ᵥ (μ' - η) ≠ 0 :=
      ((hball μ' (hball_of μ' h.2)).1).1 h.1.1
    have hH₀ (μ' : α → ℝ) (h : μ' ∈ D) : task.staticDifficulty μ' ≠ 0 := by
      rw [IdentTask.staticDifficulty, ne_eq, ENNReal.inv_eq_zero]
      refine ne_top_of_le_ne_top (b := ENNReal.ofReal (∑ a, 1 * (μ a - μ' a) ^ 2 / (2 * v a)))
        ENNReal.ofReal_ne_top (iSup₂_le fun w hw ↦ ?_)
      refine (iInf₂_le μ ⟨hμM, h.1.2.symm⟩).trans ?_
      rw [IdentTask.cost_gaussianReal hv hν (mem_simplex_iff.1 hw).1]
      refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun a _ ↦ ?_)
      have hva : (0 : ℝ) < v a := by have := hv a; positivity
      have hwa : w a ≤ 1 := (Finset.single_le_sum (fun b _ ↦ (mem_simplex_iff.1 hw).1 b)
        (Finset.mem_univ a)).trans_eq (mem_simplex_iff.1 hw).2
      gcongr
    have h3 := inv_iSup_asymptoticRatio_le task task.staticDifficulty h𝒜 hp (D := D)
      (fun μ' h ↦ h.1.2) hH₀ (fun μ' h ↦ hHtop μ' h.2 (hD0 μ' h))
    have hmax : ⨆ μ' ∈ D, task.asymptoticRatio task.staticDifficulty 𝒜 μ' ≤
        task.maxRatio task.staticDifficulty 𝒜 := iSup₂_mono' fun μ' h ↦ ⟨μ', h.1.1, le_rfl⟩
    refine (ENNReal.inv_le_inv.2 hmax).trans (h3.trans (iSup₂_le fun w hw ↦ ?_))
    have hdisj : Disjoint (task.correct μ) (task.correct lam) := by
      rw [hμi, hlamj]
      exact Set.disjoint_singleton.2 hij
    refine (iInf₂_le lam ⟨⟨hlamM, hdisj⟩, hs2⟩).trans ?_
    have hHlam : task.staticDifficulty lam ≤ ENNReal.ofReal
        ((((1 - t⁻¹) * (((t - 1) * (s * u ⬝ᵥ u)) ^ 2 / (2 * L ^ 2))))⁻¹) := by
      have ht1 : t - 1 ≠ 0 := by linarith
      rw [ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.le_inv_iff_le_inv, ← hlamη]
      exact hH lam hs2 hlam0.ne'
    have hcost : task.cost w μ lam ≤ ENNReal.ofReal ((t * (s * u ⬝ᵥ u)) ^ 2 / (2 * L ^ 2)) := by
      rw [IdentTask.cost_gaussianReal hv hν (mem_simplex_iff.1 hw).1]
      refine ENNReal.ofReal_le_ofReal ((le_of_eq ?_).trans
        ((hdw w hw (-(t * (s * u ⬝ᵥ u)))).trans_eq (by ring)))
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      simp only [μ, lam, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    calc task.staticDifficulty lam * task.cost w μ lam
        ≤ ENNReal.ofReal ((((1 - t⁻¹) * (((t - 1) * (s * u ⬝ᵥ u)) ^ 2 / (2 * L ^ 2))))⁻¹) *
          ENNReal.ofReal ((t * (s * u ⬝ᵥ u)) ^ 2 / (2 * L ^ 2)) := by gcongr
      _ = ENNReal.ofReal ((1 - t⁻¹)⁻¹ ^ 3) := by
          have ht1 : t - 1 ≠ 0 := by linarith
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  have hlim : Tendsto (fun t : ℝ ↦ ENNReal.ofReal ((1 - t⁻¹)⁻¹ ^ 3)) atTop (𝓝 1) := by
    have : Tendsto (fun t : ℝ ↦ (1 - t⁻¹)⁻¹ ^ 3) atTop (𝓝 ((1 - 0)⁻¹ ^ 3)) :=
      ((tendsto_const_nhds.sub tendsto_inv_atTop_zero).inv₀ (by norm_num)).pow 3
    simpa using ENNReal.tendsto_ofReal this
  exact ge_of_tendsto hlim ((eventually_gt_atTop 1).mono key)

end Degenne2023Existence
