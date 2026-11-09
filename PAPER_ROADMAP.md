# Paper roadmap: On the Existence of a Complexity in Fixed Budget Bandit Identification

Paper: RemyDegenne/Degenne2023Existence · LMLExplore afd365492580 · LMLRoadmaps 468f19f45fae · Refreshed 2026-11-09

## Items

| Id | Item | Tag | Link | Status | Files |
|---|---|---|---|---|---|
| R1 | Fixed-budget identification algorithms | exists | `LMLExplore.Identification.IsFixedBudget` | – | |
| R2 | Identification tasks, alternatives and transportation costs | exists | `LMLExplore.Identification.IdentTask.cost` | – | |
| R3 | Classical tasks: best arm identification, minimum threshold, half-space | exists | `LMLExplore.Identification.minThresholdTask` | – | |
| R4 | Exponential families in the mean parametrization and their extended divergence | exists | `MeasureTheory.Measure.expFamilyRate` | – | |
| R5 | Change of measure for events of the output at a stopping time | exists | `LMLExplore.Identification.klBer_measureReal_histOutputMeasure_le` | – | |
| R6 | Cumulative tracking with fixed targets | exists | `LMLExplore.Identification.cumulativeTracking` | – | |
| R7 | Characteristic time of Gaussian best arm identification, `H ≤ T* ≤ 2H` | exists | `LMLExplore.Identification.charTime_baiTask_gaussianBandit_le` | – | |
| R8 | Sub-Gaussian lower bound on the Cramér rate function | exists | `ProbabilityTheory.HasSubgaussianMGF.ofReal_sq_div_le_rateFunction` | – | |
| R9 | Fixed-budget algorithm families, probability of error, rate, oracle difficulty, difficulty ratios, consistency | target | Identification 8.4 | todo | `ForLMLExplore/Identification/FixedBudgetComplexity.lean` |
| R10 | Large deviation principles and Cramér's theorem on `ℝ` | target | Identification 8.3 | todo | `ForLMLExplore/Probability/LargeDeviations/Basic.lean`, `D2023/Lemma11.lean` |
| R11 | Static proportions families, their existence, and the static-proportions difficulty | target | Identification 8.3 | todo | `ForLMLExplore/Identification/FixedBudgetComplexity.lean` |
| R12 | Large deviations of the empirical means under static allocations, and the error exponent of static proportions | target | Identification 8.3 | todo | `D2023/Setting.lean`, `D2023/Theorem12.lean`, `D2023/Theorem1.lean` |
| R13 | Lower bounds on the difficulty ratio | target | Identification 8.4 | todo | `D2023/Theorem2.lean`, `D2023/Theorem3.lean`, `D2023/Corollary4.lean`, `D2023/Theorem13.lean`, `D2023/Corollary14.lean` |
| R14 | Two-armed best arm identification: the best static exponent is the Chernoff information | target | Identification 8.3 | todo | `D2023/Lemma19.lean`, `D2023/Lemma20.lean`, `D2023/Lemma9.lean` |
| R15 | The ratio of static proportions is at most `K`, attained by positivity | target | Identification 8.4 | todo | `D2023/Theorem5.lean`, `D2023/Theorem6.lean` |
| R16 | Tasks with a flat boundary, Gaussian half-space identification | target | Identification 8.4 | todo | `D2023/Lemma15.lean`, `D2023/Lemma16.lean`, `D2023/Theorem7.lean` |
| R17 | No complexity in best arm identification: Gaussian arms with `K` large, two Bernoulli arms | target | Identification 8.4 | todo | `D2023/Theorem8.lean`, `D2023/Theorem10.lean` |

## Notes

- R9: the notions of the fixed-budget complexity of [D23, Sections 1–2], for every identification
  task (any models, multiple correct answers): `IsFixedBudgetFamily`, `IdentTask.alternatives`
  (admissible models without a common correct answer), `errorProb`, `errorRate`
  (`T / (-log p)`, in `ℝ≥0∞`), `oracleDifficulty`, `difficultyRatio`, `asymptoticRatio`,
  `maxRatio`, `IsConsistent`. The port needs their basic API (blueprint chapter
  `prereq-complexity`: `lem:inv_difficultyRatio`, `lem:tendsto_errorRate_iff`,
  `lem:oracleDifficulty_mono`, `lem:asymptoticRatio_eq_top`).
- R10: Identification 8.3 asks for Cramér's theorem for every law on `ℝ` whose cumulant generating
  function is finite on a neighbourhood of `0` [DZ98, Theorem 2.2.3], the upper bound from
  LMLExplore's Cramér–Chernoff bounds and the lower bound by exponential tilting at the means of the
  generated family and by truncation at the other levels of finite rate; [D23, Lemma 11] (the
  exponential-family case) is its specialization. Also the goodness of the rate function, and the
  independence across coordinates (`lem:ldp_pi`).
- R11: `IsStaticProportions`, `staticClass` and `staticDifficulty` (alternative first in the
  divergence, unlike `IdentTask.altCost`), with `lem:exists_static` (cumulative tracking, R6),
  `lem:exists_rec`, `lem:iSup_open_simplex` and `lem:staticDifficulty_eq_charTime`.
- R12: Identification 8.3 asks for the large deviations of the empirical means of independent
  samples with fixed proportions of arms with any laws whose cgf is finite near `0`, with the
  rate functions of Layer 1.2, and for the error exponent of the static-proportions algorithm
  recommending `i*(μ̂)` as the infimum of `∑ a, w a I_a(x_a)` over the vectors of means at which
  `i*(μ)` is not correct [GJ04]; [D23, Theorems 1, 12] are its exponential-family case under
  Assumption 1 (`D2023.IsRegular`, which the port should state for tasks on any mean functional).
  The recommendation rule needs the condition of erratum E1, and the families the closure
  hypothesis of E2.
- R13: [D23, Theorems 2, 3, 13, Corollaries 4, 14], for every task; they use R5 and the bound
  `kl(a, b) ≥ a log (1/b) - log 2`, absent from LMLExplore (`lem:klBer_ge`, for
  `InformationTheory/KullbackLeibler/Bernoulli.lean`).
- R14: Identification 8.3, third bullet: for two arms, the best static exponent is the Chernoff
  information `d(z, μ₁) = d(z, μ₂)` [D23, Lemmas 9, 19, 20]; the matching lower bound for
  consistent algorithms [KCG16, Theorems 12–13] is not part of this paper.
- R15–R17: Identification 8.4, the results of [D23] on the existence of a complexity
  (Theorems 5–8 and 10, Lemmas 15–18). The proofs of Theorems 6 and 7 follow the corrections E3–E5
  of `notes/paper-errata.md`, and the one of Theorem 8 the correction E6.

## Proposed targets
