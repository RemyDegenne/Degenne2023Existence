/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Identification.ErrorLowerBound

/-!
# The change of measure for fixed-budget algorithms

A fixed-budget algorithm `A` with budget `T` stops at time `T`, so the divergence decomposition at
its stopping time bounds the relative entropy between the laws of its output on the bandits `κ`
and `κ'` by `∑ a, E_κ[N_a(T)] KL(κ a ‖ κ' a)`, with the numbers of pulls `N_a(T)` of the first `T`
rounds. For `T ≠ 0` the expected proportions of pulls `E_κ[N_a(T)] / T` form a vector of the
simplex, and the bound is `T` times the transportation cost of these proportions.

## Main statements

* `LMLExplore.Identification.IsFixedBudget.klDiv_outputMeasure_le`: the relative entropy between
  the laws of the output of a fixed-budget algorithm with budget `T` on two bandits is at most
  `∑ a, E_κ[N_a(T)] KL(κ a ‖ κ' a)`.
* `LMLExplore.Identification.IsFixedBudget.lintegral_pullCount_div`: for `T ≠ 0`,
  `E[N_a(T)] / T` is the expected proportion of pulls of `a`.
* `LMLExplore.Identification.IsFixedBudget.expectedPullProportion_mem_simplex`: for `T ≠ 0`, the
  expected proportions of pulls lie in the simplex.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Learning

open scoped ENNReal

namespace LMLExplore.Identification.IsFixedBudget

variable {α 𝓨 𝓓 : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {m𝓨 : MeasurableSpace 𝓨} [MeasurableSpace.CountablyGenerated 𝓨]
  {m𝓓 : MeasurableSpace 𝓓} {A : IdentAlg Unit α 𝓨 𝓓} {T : ℕ}

omit [Fintype α] [DecidableEq α] [MeasurableSingletonClass α]
  [MeasurableSpace.CountablyGenerated 𝓨] in
/-- A fixed-budget algorithm with budget `T` stops at time `T`. -/
lemma toNat_stoppingTime (hA : IsFixedBudget A T) (ω : ℕ → Round Unit α 𝓨) :
    ENat.toNat (A.stoppingTime IT.obs IT.action IT.feedback ω) = T := by
  rw [hA.stoppingTime_eq]
  exact ENat.toNat_natCast T

/-- **Divergence decomposition for the output of a fixed-budget algorithm.** If `A` has budget
`T`, the relative entropy between the laws of its output on the bandits `κ` and `κ'` is at most
`∑ a, E_κ[N_a(T)] KL(κ a ‖ κ' a)`, where `N_a(T)` is the number of pulls of the arm `a` in the
first `T` rounds. -/
lemma klDiv_outputMeasure_le (hA : IsFixedBudget A T) (κ κ' : Kernel α 𝓨) [IsMarkovKernel κ]
    [IsMarkovKernel κ'] :
    klDiv (A.outputMeasure (Environment.bandit κ)) (A.outputMeasure (Environment.bandit κ')) ≤
      ∑ a, (∫⁻ ω, (pullCount IT.action a T ω : ℝ≥0∞)
        ∂(trajMeasure A.alg (Environment.bandit κ))) * klDiv (κ a) (κ' a) := by
  simpa only [hA.toNat_stoppingTime] using
    Identification.klDiv_outputMeasure_le A κ κ' (hA.stopsAS _)

omit [Fintype α] [MeasurableSingletonClass α] [MeasurableSpace.CountablyGenerated 𝓨] in
/-- For a fixed-budget algorithm with budget `T ≠ 0`, the expected number of pulls of the arm `a`
divided by `T` is the expected proportion of pulls of `a`. -/
lemma lintegral_pullCount_div (hA : IsFixedBudget A T) (hT : T ≠ 0)
    (env : Environment Unit α 𝓨) (a : α) :
    (∫⁻ ω, (pullCount IT.action a T ω : ℝ≥0∞) ∂(trajMeasure A.alg env)) / T =
      ENNReal.ofReal (expectedPullProportion A env a) := by
  have h := expectedStoppingTime_mul_ofReal_expectedPullProportion
    (hA.expectedStoppingTime_eq env ▸ ENNReal.natCast_ne_top T) a
  simp only [hA.toNat_stoppingTime, hA.expectedStoppingTime_eq env] at h
  rw [← h, mul_comm, ENNReal.mul_div_cancel_right (by exact_mod_cast hT) (ENNReal.natCast_ne_top T)]

omit [MeasurableSpace.CountablyGenerated 𝓨] in
/-- For a fixed-budget algorithm with budget `T ≠ 0`, the expected proportions of pulls lie in the
simplex. -/
lemma expectedPullProportion_mem_simplex (hA : IsFixedBudget A T) (hT : T ≠ 0)
    (env : Environment Unit α 𝓨) : expectedPullProportion A env ∈ simplex α :=
  Identification.expectedPullProportion_mem_simplex (by simp [hA.expectedStoppingTime_eq env, hT])
    (by simp [hA.expectedStoppingTime_eq env])

end LMLExplore.Identification.IsFixedBudget
