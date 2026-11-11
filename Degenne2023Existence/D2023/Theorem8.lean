/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Degenne2023Existence.D2023.Corollary4
public import Degenne2023Existence.D2023.Theorem1
public import Degenne2023Existence.ForLMLExplore.Identification.Task.ExpFamily
public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Theorem 8 of [D23]: no complexity in Gaussian best arm identification for many arms

For best arm identification with Gaussian arms of variance `1` and every class `𝒞` of algorithm
families containing the static proportions algorithms, every fixed-budget algorithm family has
maximal difficulty ratio at least `(3 / 80) log K` to the oracle difficulty of `𝒞`. For `K` large
enough, no such class admits a complexity.

The proof follows the paper's. The oracle difficulty of `𝒞` is at most that of the static
proportions algorithms, which is at most the static-proportions difficulty `H^{sp}` (Theorem 1,
under Assumption 1, which best arm identification satisfies), equal to the characteristic time
`T*` for Gaussian arms; and `T* ≤ 2 H_Δ` [GK16]. Corollary 4 at a model `μ` with the alternatives
`λ⁽ʲ⁾` that move the mean of the arm `j` above the best mean bounds the ratio below by
`∑_j 1 / (H^{sp}(λ⁽ʲ⁾) KL(μ_j, λ⁽ʲ⁾_j))`.

The construction differs slightly from the paper's: the means are `μ = (0, -1, …, -(K - 1))`
instead of `(0, -2, …, -K)`, and `λ⁽ʲ⁾_j = -μ_j`. With `m = -μ_j`, the gaps of `λ⁽ʲ⁾` are `m` and
`m + l` for the arms of mean `-l`, so that
`2 H_Δ(λ⁽ʲ⁾) ≤ 4 / m² + 4 ∑_{l ≥ 0} 1 / (m + l)² ≤ 12 / m` and
`H^{sp}(λ⁽ʲ⁾) KL(μ_j, λ⁽ʲ⁾_j) ≤ (12 / m) 2 m² = 24 m`. The bound is then
`(1 / 24) ∑_{m=1}^{K-1} 1 / m ≥ (1 / 24) log K ≥ (3 / 80) log K`, for every `K`. The paper's last
inequality, `(log (K + 1) - log 2) / 8 ≥ (3 / 40) log K`, fails for `K = 2`, where the statement
still holds (erratum E6 of `notes/paper-errata.md`).

## Main statements

* `Degenne2023Existence.oracleDifficulty_le_staticDifficulty_baiTask_gaussian`:
  [D23, proof of Theorem 8], the oracle difficulty of a class containing the static proportions
  algorithms is at most the static-proportions difficulty.
* `Degenne2023Existence.ofReal_mul_log_le_iInf_maxRatio_baiTask_gaussian`:
  [D23, Theorem 8].

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology InformationTheory Learning LMLExplore
  LMLExplore.Identification

open scoped ENNReal NNReal

namespace Degenne2023Existence

variable {α : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α]

/-- **The oracle difficulty in Gaussian best arm identification** [D23, proof of Theorem 8]. For
best arm identification with Gaussian arms of variance `1` and a class `𝒞` of algorithm families
containing the static proportions algorithms, at every model `μ` with a unique best arm,
`H_𝒞(μ) ≤ H_{𝒞^{sp}}(μ) ≤ H^{sp}(μ)`: the task satisfies Assumption 1 on all the vectors of means,
which are the means of the Gaussian family. -/
lemma oracleDifficulty_le_staticDifficulty_baiTask_gaussian (𝒞 : Set (ℕ → IdentAlg Unit α ℝ α))
    (h𝒞 : (baiTask (Bandits.gaussianBandit · 1) id).staticClass ⊆ 𝒞) {μ : α → ℝ}
    (hμ : μ ∈ (baiTask (Bandits.gaussianBandit · 1) id).M) :
    (baiTask (Bandits.gaussianBandit · 1) id).oracleDifficulty 𝒞 μ ≤
      (baiTask (Bandits.gaussianBandit · 1) id).staticDifficulty μ := by
  have : Nonempty α := by
    have h := hμ
    rw [M_baiTask] at h
    exact ⟨h.choose⟩
  have hreg : IsRegular (baiTask (Bandits.gaussianBandit · 1) id)
      {μ : α → ℝ | ∀ a, μ a ∈ (gaussianReal 0 1).expFamilyMeans id} := by
    rw [setOf_forall_mem_expFamilyMeans_gaussianReal 0 one_ne_zero]
    simpa using isRegular_baiTask (Bandits.gaussianBandit · (1 : ℝ≥0)) isOpen_univ convex_univ
  refine ((baiTask _ id).oracleDifficulty_anti h𝒞 μ).trans ?_
  exact oracleDifficulty_staticClass_le (ρ := fun _ ↦ gaussianReal 0 1)
    (fun _ c ↦ not_ae_eq_const_gaussianReal 0 one_ne_zero c)
    (fun _ ↦ by simp [expFamilyMeans_gaussianReal 0 one_ne_zero])
    (fun μ a _ ↦ by
      rw [expFamily_natParam_gaussianReal 0 one_ne_zero, ν_baiTask, Bandits.gaussianBandit_apply])
    hreg
    (isSingleAnswer_baiTask _ id) hμ (Set.toFinite _).measurableSet

/-- **No complexity in Gaussian best arm identification for many arms** [D23, Theorem 8]. For
best arm identification with Gaussian arms of variance `1` and a class `𝒞` of algorithm families
containing the static proportions algorithms, the infimum over the fixed-budget algorithm
families of the maximal difficulty ratio to the oracle difficulty of `𝒞` is at least
`(3 / 80) log K`, with `K` the number of arms.

The proof applies Corollary 4 at the means `(0, -1, …, -(K - 1))`, a variant of the paper's
construction whose bound `(1 / 24) log K` holds for every `K` (see the module docstring). -/
theorem ofReal_mul_log_le_iInf_maxRatio_baiTask_gaussian (𝒞 : Set (ℕ → IdentAlg Unit α ℝ α))
    (h𝒞 : (baiTask (Bandits.gaussianBandit · 1) id).staticClass ⊆ 𝒞) :
    ENNReal.ofReal (3 / 80 * Real.log (Fintype.card α)) ≤
      ⨅ (𝒜 : ℕ → IdentAlg Unit α ℝ α) (_ : IsFixedBudgetFamily 𝒜),
        (baiTask (Bandits.gaussianBandit · 1) id).maxRatio
          ((baiTask (Bandits.gaussianBandit · 1) id).oracleDifficulty 𝒞) 𝒜 := by
  set task := baiTask (Bandits.gaussianBandit · (1 : ℝ≥0)) (id : (α → ℝ) → α → ℝ)
  set K := Fintype.card α
  -- For `K ≤ 1`, the bound is `0`.
  rcases lt_or_ge K 2 with hK | hK
  · have hlog : Real.log K ≤ 0 :=
      Real.log_nonpos (Nat.cast_nonneg _) (by exact_mod_cast Nat.lt_succ_iff.1 hK)
    rw [ENNReal.ofReal_of_nonpos (by linarith)]
    exact zero_le
  refine le_iInf₂ fun 𝒜 h𝒜 ↦ ?_
  -- The arms are numbered `l a = 0, …, K - 1`; `a₀` has number `0` and `a₁` number `1`.
  set e := Fintype.equivFin α
  set l : α → ℕ := fun a ↦ (e a : ℕ)
  set a₀ := e.symm ⟨0, by omega⟩
  set a₁ := e.symm ⟨1, by omega⟩
  have hsum (g : ℕ → ℝ) : ∑ a, g (l a) = ∑ i ∈ Finset.range K, g i := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Fintype.sum_equiv e _ _ fun _ ↦ rfl
  have hla₀ : l a₀ = 0 := by simp [l, a₀]
  have hla₁ : l a₁ = 1 := by simp [l, a₁]
  have hl_pos (a : α) (ha : a ≠ a₀) : 1 ≤ l a := by
    refine Nat.one_le_iff_ne_zero.2 fun h ↦ ha ?_
    rw [Equiv.eq_symm_apply]
    exact Fin.ext h
  have ha₁₀ : a₁ ≠ a₀ := fun h ↦ by simpa [hla₀, hla₁] using congrArg l h
  -- The model `μ` has the means `μ a = -l a`, and `λ j` moves the arm `j` to `l j`.
  set μ : α → ℝ := fun a ↦ -(l a : ℝ)
  set lam : α → α → ℝ := fun j ↦ Function.update μ j (l j)
  have hμa₀ : μ a₀ = 0 := by simp [μ, hla₀]
  have hμ_lt (b : α) (hb : b ≠ a₀) : μ b < μ a₀ := by
    have := hl_pos b hb
    simp only [μ, hla₀, CharP.cast_eq_zero, neg_zero, Left.neg_neg_iff]
    exact_mod_cast this
  have hμ_le (b : α) (hb : b ≠ a₀) : μ b ≤ μ a₁ := by
    have := hl_pos b hb
    simp only [μ, hla₁, Nat.cast_one, neg_le_neg_iff]
    exact_mod_cast this
  have hlam_self (j : α) : lam j j = l j := by simp [lam]
  have hlam_ne (j b : α) (hb : b ≠ j) : lam j b = μ b := by simp [lam, hb]
  have hlam_lt (j : α) (hj : j ≠ a₀) (b : α) (hb : b ≠ j) : lam j b < lam j j := by
    rw [hlam_self, hlam_ne j b hb]
    have : (0 : ℝ) < l j := by exact_mod_cast hl_pos j hj
    simp only [μ]
    linarith [(Nat.cast_nonneg (l b) : (0 : ℝ) ≤ l b)]
  have hlam_le (j : α) (hj : j ≠ a₀) (b : α) (hb : b ≠ j) : lam j b ≤ lam j a₀ := by
    rw [hlam_ne j b hb, hlam_ne j a₀ (Ne.symm hj), hμa₀]
    simp only [μ, Left.neg_nonpos_iff, Nat.cast_nonneg]
  have hμM : μ ∈ task.M := by
    rw [M_baiTask]
    exact ⟨a₀, hμ_lt⟩
  have hlamM (j : α) (hj : j ≠ a₀) : lam j ∈ task.M := by
    rw [M_baiTask]
    exact ⟨j, hlam_lt j hj⟩
  have hcorrect_μ : task.correct μ = {a₀} := (correct_baiTask_eq_singleton_iff _ id).2 hμ_lt
  have hcorrect_lam (j : α) (hj : j ≠ a₀) : task.correct (lam j) = {j} :=
    (correct_baiTask_eq_singleton_iff _ id).2 (hlam_lt j hj)
  have hstatic (θ : α → ℝ) (i : α) (hi : task.correct θ = {i}) :
      task.staticDifficulty θ = task.charTime θ :=
    IdentTask.staticDifficulty_eq_charTime_gaussianReal (v := fun _ ↦ 1) (fun _ ↦ one_ne_zero)
      (fun _ _ ↦ by rw [ν_baiTask, Bandits.gaussianBandit_apply]) hi
  have hHC (θ : α → ℝ) (hθ : θ ∈ task.M) : task.oracleDifficulty 𝒞 θ ≤ task.staticDifficulty θ :=
    oracleDifficulty_le_staticDifficulty_baiTask_gaussian 𝒞 h𝒞 hθ
  -- If the probability of error at `μ` does not tend to `0`, the ratio at `μ` is infinite.
  by_cases hp : Tendsto (task.errorProb 𝒜 μ) atTop (𝓝 0)
  swap
  · have hfin : task.oracleDifficulty 𝒞 μ ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (hHC μ hμM)
      rw [hstatic μ a₀ hcorrect_μ]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (charTime_baiTask_gaussianBandit_le one_ne_zero ha₁₀ hμ_lt hμ_le)
    refine le_trans le_top (le_of_eq ?_)
    rw [eq_comm, eq_top_iff, ← (baiTask _ id).asymptoticRatio_eq_top hfin hp]
    exact le_iSup₂ (f := fun θ (_ : θ ∈ task.M) ↦ task.asymptoticRatio _ 𝒜 θ) μ hμM
  set s := Finset.univ.erase a₀
  -- The static-proportions difficulty of `λ j`, times the divergence at the arm `j`, is at most
  -- `24 l j`.
  have hbound (j : α) (hj : j ∈ s) :
      task.staticDifficulty (lam j) * klDiv (task.ν μ j) (task.ν (lam j) j) ≤
        ENNReal.ofReal (24 * l j) := by
    have hj' : j ≠ a₀ := Finset.ne_of_mem_erase hj
    have hm : 1 ≤ l j := hl_pos j hj'
    have hm' : (1 : ℝ) ≤ l j := by exact_mod_cast hm
    -- `∑_{i < K} 1 / (m + i)² ≤ 2 / m`, for `m ≥ 1`.
    have hsq : ∑ i ∈ Finset.range K, (((l j : ℝ) + i) ^ 2)⁻¹ ≤ 2 / l j := by
      obtain ⟨k, hk⟩ : ∃ k, l j = k + 1 := ⟨l j - 1, by omega⟩
      rw [hk]
      calc ∑ i ∈ Finset.range K, ((((k + 1 : ℕ) : ℝ) + i) ^ 2)⁻¹
          = ∑ i ∈ Finset.Ico (k + 1) (k + 1 + K), ((i : ℝ) ^ 2)⁻¹ := by
            rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
            push_cast
            rfl
        _ = ∑ i ∈ Finset.Ioo k (k + 1 + K), ((i : ℝ) ^ 2)⁻¹ := by
            rw [Finset.Ico_add_one_left_eq_Ioo]
        _ ≤ 2 / (k + 1) := sum_Ioo_inv_sq_le k _
        _ = 2 / ((k + 1 : ℕ) : ℝ) := by push_cast; rfl
    -- The bound `H_Δ(λ j) ≤ 6 / l j` on the quantity of [GK16].
    have hHΔ : 2 * ((1 : ℝ≥0) : ℝ) / (lam j j - lam j a₀) ^ 2 +
        ∑ b ∈ Finset.univ.erase j, 2 * ((1 : ℝ≥0) : ℝ) / (lam j j - lam j b) ^ 2 ≤
          6 / (l j : ℝ) := by
      have h1 : lam j j - lam j a₀ = l j := by
        rw [hlam_self, hlam_ne j a₀ (Ne.symm hj'), hμa₀, sub_zero]
      have h2 : ∑ b ∈ Finset.univ.erase j, 2 * ((1 : ℝ≥0) : ℝ) / (lam j j - lam j b) ^ 2 ≤
          2 * (2 / (l j : ℝ)) := by
        calc ∑ b ∈ Finset.univ.erase j, 2 * ((1 : ℝ≥0) : ℝ) / (lam j j - lam j b) ^ 2
            = ∑ b ∈ Finset.univ.erase j, 2 * (((l j : ℝ) + l b) ^ 2)⁻¹ := by
              refine Finset.sum_congr rfl fun b hb ↦ ?_
              rw [hlam_self, hlam_ne j b (Finset.ne_of_mem_erase hb)]
              simp only [μ, NNReal.coe_one, mul_one, sub_neg_eq_add, div_eq_mul_inv]
          _ ≤ ∑ b, 2 * (((l j : ℝ) + l b) ^ 2)⁻¹ :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
                fun _ _ _ ↦ by positivity
          _ = 2 * ∑ i ∈ Finset.range K, (((l j : ℝ) + i) ^ 2)⁻¹ := by
              rw [← Finset.mul_sum, hsum fun i ↦ (((l j : ℝ) + i) ^ 2)⁻¹]
          _ ≤ 2 * (2 / (l j : ℝ)) := by gcongr
      rw [h1]
      have h3 : 2 * ((1 : ℝ≥0) : ℝ) / (l j : ℝ) ^ 2 ≤ 2 / l j := by
        rw [NNReal.coe_one, mul_one]
        gcongr
        nlinarith
      calc _ ≤ 2 / (l j : ℝ) + 2 * (2 / (l j : ℝ)) := add_le_add h3 h2
        _ = 6 / (l j : ℝ) := by ring
    have hT : task.charTime (lam j) ≤ ENNReal.ofReal (12 / l j) :=
      (charTime_baiTask_gaussianBandit_le one_ne_zero hj'.symm (hlam_lt j hj')
        (hlam_le j hj')).trans (ENNReal.ofReal_le_ofReal
          ((mul_le_mul_of_nonneg_left hHΔ zero_le_two).trans_eq (by ring)))
    have hKL : klDiv (task.ν μ j) (task.ν (lam j) j) = ENNReal.ofReal (2 * (l j : ℝ) ^ 2) := by
      simp only [task, ν_baiTask, Bandits.gaussianBandit_apply]
      rw [klDiv_gaussianReal_gaussianReal_same_var one_ne_zero, hlam_self]
      congr 1
      simp only [μ, NNReal.coe_one]
      ring
    rw [hstatic _ j (hcorrect_lam j hj'), hKL]
    calc task.charTime (lam j) * ENNReal.ofReal (2 * (l j : ℝ) ^ 2)
        ≤ ENNReal.ofReal (12 / l j) * ENNReal.ofReal (2 * (l j : ℝ) ^ 2) := by gcongr
      _ = ENNReal.ofReal (24 * l j) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
  -- Corollary 4 at `μ` with the alternatives `λ j`, `j ≠ a₀`.
  have hcor := sum_inv_le_iSup_asymptoticRatio task task.staticDifficulty h𝒜 hp s lam
    (fun j hj ↦ by
      rw [hcorrect_μ, hcorrect_lam j (Finset.ne_of_mem_erase hj)]
      exact Set.disjoint_singleton.2 (Finset.ne_of_mem_erase hj).symm)
    (fun j _ b hb ↦ by simp [task, lam, hb])
    (fun j hj ↦ by
      have hj' : j ≠ a₀ := Finset.ne_of_mem_erase hj
      rw [hstatic _ j (hcorrect_lam j hj')]
      refine (lt_of_lt_of_le ?_ (le_charTime_baiTask_gaussianBandit one_ne_zero hj'.symm
        (hlam_lt j hj'))).ne'
      have : 0 < lam j j - lam j a₀ := sub_pos.2 (hlam_lt j hj' a₀ hj'.symm)
      exact ENNReal.ofReal_pos.2 (add_pos_of_pos_of_nonneg (by positivity)
        (Finset.sum_nonneg fun _ _ ↦ by positivity)))
    (fun j hj ↦ by
      have hj' : j ≠ a₀ := Finset.ne_of_mem_erase hj
      rw [hstatic _ j (hcorrect_lam j hj')]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (charTime_baiTask_gaussianBandit_le one_ne_zero hj'.symm (hlam_lt j hj')
          (hlam_le j hj')))
  -- The real lower bound: `∑_{j ≠ a₀} 1 / (24 l j) ≥ (1 / 24) log K ≥ (3 / 80) log K`.
  have hreal : 3 / 80 * Real.log K ≤ ∑ j ∈ s, (24 * (l j : ℝ))⁻¹ := by
    rw [Finset.sum_erase _ (by simp [hla₀]), hsum fun i ↦ (24 * (i : ℝ))⁻¹]
    simp_rw [mul_inv, ← Finset.mul_sum]
    have hlog : 0 ≤ Real.log K := Real.log_natCast_nonneg K
    -- `log K ≤ ∑_{i < K} 1 / i`, with `1 / 0 = 0`: the harmonic number `H_{K-1}`.
    have hharm : Real.log K ≤ ∑ i ∈ Finset.range K, ((i : ℝ))⁻¹ := by
      obtain ⟨n, hn⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
      rw [hn, Finset.sum_range_succ', Nat.cast_zero, inv_zero, add_zero]
      calc Real.log ((n + 1 : ℕ) : ℝ) ≤ harmonic n := log_add_one_le_harmonic n
        _ = _ := by simp [harmonic]
    nlinarith
  calc ENNReal.ofReal (3 / 80 * Real.log K)
      ≤ ENNReal.ofReal (∑ j ∈ s, (24 * (l j : ℝ))⁻¹) := ENNReal.ofReal_le_ofReal hreal
    _ = ∑ j ∈ s, (ENNReal.ofReal (24 * l j))⁻¹ := by
        rw [ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ by positivity]
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        have : (0 : ℝ) < l j := by exact_mod_cast hl_pos j (Finset.ne_of_mem_erase hj)
        rw [ENNReal.ofReal_inv_of_pos (by positivity)]
    _ ≤ ∑ j ∈ s, (task.staticDifficulty (lam j) * klDiv (task.ν μ j) (task.ν (lam j) j))⁻¹ :=
        Finset.sum_le_sum fun j hj ↦ ENNReal.inv_le_inv.2 (hbound j hj)
    _ ≤ ⨆ j ∈ s, task.asymptoticRatio task.staticDifficulty 𝒜 (lam j) := hcor
    _ ≤ ⨆ j ∈ s, task.asymptoticRatio (task.oracleDifficulty 𝒞) 𝒜 (lam j) :=
        iSup₂_mono fun j hj ↦ task.asymptoticRatio_le_of_le 𝒜
          (hHC _ (hlamM j (Finset.ne_of_mem_erase hj)))
    _ ≤ task.maxRatio (task.oracleDifficulty 𝒞) 𝒜 :=
        iSup₂_le fun j hj ↦ le_iSup₂ (f := fun θ (_ : θ ∈ task.M) ↦
          task.asymptoticRatio (task.oracleDifficulty 𝒞) 𝒜 θ) (lam j)
          (hlamM j (Finset.ne_of_mem_erase hj))

end Degenne2023Existence
