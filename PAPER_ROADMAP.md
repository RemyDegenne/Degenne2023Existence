# Paper roadmap: On the Existence of a Complexity in Fixed Budget Bandit Identification

Paper: RemyDegenne/Degenne2023Existence · LMLExplore afd365492580 · LMLRoadmaps 468f19f45fae · Refreshed 2026-11-11

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
| R9 | Fixed-budget algorithm families, probability of error, rate, oracle difficulty, difficulty ratios, consistency | target | Identification 8.4 | PR #267 | `ForLMLExplore/Identification/FixedBudgetComplexity.lean` |
| R10 | Large deviation principles and Cramér's theorem on `ℝ` | target | Identification 8.3 | PR #261 | `ForLMLExplore/Probability/LargeDeviations/Basic.lean`, `ForLMLExplore/Probability/LargeDeviations/Cramer.lean`, `D2023/Lemma11.lean` |
| R11 | Static proportions families, their existence, and the static-proportions difficulty | target | Identification 8.3 | PR #268 | `ForLMLExplore/Identification/FixedBudgetComplexity.lean` |
| R12 | Large deviations of the empirical means under static allocations, and the error exponent of static proportions | target | Identification 8.3 | proved | `ForLMLExplore/Bandits/StaticAllocation.lean`, `D2023/Setting.lean`, `D2023/Theorem12.lean`, `D2023/Theorem1.lean` |
| R13 | Lower bounds on the difficulty ratio | target | Identification 8.4 | merged #258 | `D2023/Theorem2.lean`, `D2023/Theorem3.lean`, `D2023/Corollary4.lean`, `D2023/Theorem13.lean`, `D2023/Corollary14.lean`, `ForLMLExplore/Identification/ErrorLowerBound.lean`, `ForLMLExplore/InformationTheory/KullbackLeibler/Bernoulli.lean`, `ForLMLExplore/Analysis/Convex/Simplex.lean` |
| R14 | Two-armed best arm identification: the best static exponent is the Chernoff information | target | Identification 8.3 | merged #260 | `ForLMLExplore/Identification/Task/BestArmTwo.lean`, `ForLMLExplore/Probability/Distributions/ExponentialFamily/Mean.lean`, `ForLMLExplore/Probability/Distributions/ExponentialFamily/RateFunction.lean`, `D2023/Lemma19.lean`, `D2023/Lemma20.lean`, `D2023/Lemma9.lean` |
| R15 | The ratio of static proportions is at most `K`, attained by positivity | target | Identification 8.4 | todo | `D2023/Theorem5.lean`, `D2023/Theorem6.lean` |
| R16 | Tasks with a flat boundary, Gaussian half-space identification | target | Identification 8.4 | PR #259 | `D2023/Lemma15.lean`, `D2023/Lemma16.lean`, `D2023/Theorem7.lean`, `ForLMLExplore/Identification/Task/HalfSpace.lean`, `ForLMLExplore/Identification/Task/ExpFamily.lean` |
| R17 | No complexity in best arm identification: Gaussian arms with `K` large, two Bernoulli arms | target | Identification 8.4 | proved | `D2023/Theorem8.lean`, `D2023/Theorem10.lean`, `ForLMLExplore/Identification/Task/BestArm.lean`, `ForLMLExplore/Identification/Task/ExpFamily.lean`, `ForLMLExplore/InformationTheory/KullbackLeibler/Bernoulli.lean` |

## Notes

- R9: the notions of the fixed-budget complexity of [D23, Sections 1–2], for every identification
  task (any models, multiple correct answers): `IsFixedBudgetFamily`, `IdentTask.alternatives`
  (admissible models without a common correct answer), `errorProb`, `errorRate`
  (`T / (-log p)`, in `ℝ≥0∞`), `oracleDifficulty`, `difficultyRatio`, `asymptoticRatio`,
  `maxRatio`, `IsConsistent`. The port needs their basic API (blueprint chapter
  `prereq-complexity`: `lem:inv_difficultyRatio`, `lem:tendsto_errorRate_iff`,
  `lem:oracleDifficulty_mono`, `lem:asymptoticRatio_eq_top`). PR #258 (item R13, merged) ports
  `IsFixedBudgetFamily`, `alternatives`, `errorProb`, `errorRate`, `difficultyRatio`,
  `asymptoticRatio`, `maxRatio`, `IsConsistent` and `inv_difficultyRatio` to
  `LMLExplore/Identification/DifficultyRatio.lean`, `FixedBudget.lean` and `Task/Basic.lean`
  (`alternatives`, next to `alt`), with bodies not exposed, `IsFixedBudgetFamily` for any
  observation, action and output spaces, and `errorRate` renamed `errorComplexity`, as
  `T / log (1 / p)`. The port of R9 then adds the rest: `oracleDifficulty`,
  `AdmitsComplexity`, `lem:tendsto_errorRate_iff`, `lem:oracleDifficulty_mono` and
  `lem:asymptoticRatio_eq_top`. Proved, without `sorry`: `asymptoticRatio_eq_top`,
  `tendsto_errorRate_of_tendsto_log_div` (`lem:tendsto_errorRate_iff`, the direction the proofs
  use) with the rate as an inverse (`errorRate_eq_inv`) and the one-sided form
  `inv_le_liminf_errorRate_of_neg_le_liminf`, `lem:oracleDifficulty_mono` as the antitonicity of
  the oracle difficulty in the class and of the difficulty ratios in the difficulty function
  (`oracleDifficulty_anti`, `difficultyRatio_anti`, `asymptoticRatio_anti`, `maxRatio_anti`, and
  at a single model `asymptoticRatio_le_of_le`), `alternatives_eq_alt` and, for R11, `IsStaticProportions.errorProb_eq` (the probability of
  error of a static proportions family as a probability of the trajectory, for a measurable set of
  correct answers; the recommendation rule need not be measurable). PR #267 ports the rest of R9
  from commit ccbde8e to `LMLExplore/Identification/DifficultyRatio.lean`: `oracleDifficulty` and
  `AdmitsComplexity`, bodies not exposed, with characterising lemmas, `oracleDifficulty_anti`,
  `asymptoticRatio_eq_top`, the antitonicity of the difficulty ratios, and the rate lemmas renamed
  after `errorComplexity` (`errorComplexity_eq_inv`, `tendsto_errorComplexity_of_tendsto_log_div`,
  `inv_le_liminf_errorComplexity_of_neg_le_liminf`); it adds
  `admitsComplexity_iff_exists_maxRatio_le_one` (the reformulation of [D23, Section 1], for a
  positive oracle difficulty) and `asymptoticRatio_eq_limsup_div`. It does not port the
  static-proportions material of the same file (R11, PR #268), and removes or renames no public
  declaration. The final bump moves the paper's uses of `errorRate` and its lemmas to
  `errorComplexity`.
- R10: Identification 8.3 asks for Cramér's theorem for every law on `ℝ` whose cumulant generating
  function is finite on a neighbourhood of `0` [DZ98, Theorem 2.2.3], the upper bound from
  LMLExplore's Cramér–Chernoff bounds and the lower bound by exponential tilting at the means of the
  generated family and by truncation at the other levels of finite rate; [D23, Lemma 11] (the
  exponential-family case) is its specialization. Also the goodness of the rate function, and the
  independence across coordinates (`lem:ldp_pi`). Proved so far, without `sorry`: the criteria for
  the bounds and `IsLDP.of_isClosed_of_mem_nhds` (`Basic.lean`), and in `Cramer.lean` Cramér's
  theorem `isLDP_cramer` for every law with a mean (the lower bound
  `neg_rateFunction_le_liminf_log_measure` for every law, by truncation as in [DZ98]), the
  goodness `isGoodRateFunction_rateFunction` when the cgf is finite near `0`, and the
  exponential-family form `isLDP_cramer_expFamily`. The laws are those of the empirical means
  under `Measure.pi` over `Fin n`. [D23, Lemma 11] (`D2023/Lemma11.lean`) is
  `isLDP_cramer_expFamily`, with the hypothesis `NeZero ρ` that the paper leaves implicit
  (`notes/statement-corrections.md`). `Basic.lean` also has the converse exponential bounds of a
  principle (`IsLDP.eventually_measure_le_exp`, `IsLDP.eventually_exp_le_measure`), exponential
  tightness on normed groups from a good rate function
  (`IsLDP.exists_eventually_measure_norm_ge_le_exp`) and the goodness of positive weighted sums
  of good rate functions on a finite product (`isGoodRateFunction_sum_mul`). The independence
  across coordinates (`lem:ldp_pi`) is proved in the form the empirical means of a bandit need,
  in `ForLMLExplore/Bandits/StaticAllocation.lean` (item R12). PR #261 ports `Basic.lean` and
  `Cramer.lean` from commit 5afa577, to `LMLExplore/Probability/LargeDeviations/`:
  `IsGoodRateFunction` becomes a structure with named fields, no bodies are exposed, and the
  exponential-family form `Measure.isLDP_cramer_expFamily` is generalized to any statistic on any
  measurable space and split from its goodness, `Measure.isGoodRateFunction_expFamilyRate_left`.
  It adds the form for i.i.d. sequences `isLDP_cramer_of_iIndepFun` and
  `Measure.map_pi_comp_eq_map_pi_map` (new file `LMLExplore/MeasureTheory/Constructions/Pi.lean`),
  does not port `D2023/Lemma11.lean`, and removes or renames no public declaration. After review
  it also adds the facts the lower bound shares as public lemmas: the coercivity of
  `t ↦ cgf id ν t - t x` and the mean of the family at `x`
  (`Measure.tendsto_cgf_id_sub_mul_cocompact`,
  `Measure.mem_expFamilyMeans_id_of_measure_Iio_ne_zero_of_measure_Ioi_ne_zero`, in
  `ExponentialFamily/Mean.lean`) and `rateFunction_eq_ofReal_expFamilyDiv`
  (`ExponentialFamily/RateFunction.lean`).
- R11: `IsStaticProportions`, `staticClass` and `staticDifficulty` (alternative first in the
  divergence, unlike `IdentTask.altCost`), with `lem:exists_static` (cumulative tracking, R6),
  `lem:exists_rec`, `lem:iSup_open_simplex` and `lem:staticDifficulty_eq_charTime`. PR #260
  (item R14) ports `staticDifficulty`, with `staticDifficulty_def`, `inv_staticDifficulty` and
  `staticDifficulty_restrict_le`, to `LMLExplore/Identification/StaticProportions.lean`; the port
  of R11 then adds the rest. Proved, without `sorry`: `lem:exists_static`
  (`IdentTask.exists_isStaticProportions`: cumulative tracking with the constant targets `w` and
  the deterministic output `rec μ̂_T`, for any measurable rule and any task),
  `lem:iSup_open_simplex` (`IdentTask.iSup_pos_iInf_cost_eq`, for the cost of any set of models)
  and `lem:staticDifficulty_eq_charTime` (`IdentTask.staticDifficulty_eq_charTime`, with the
  symmetry of the divergences only between the model and its alternatives). `lem:exists_rec`
  depends on Assumption 1 and is in `D2023/Theorem1.lean` (`exists_measurable_rec`,
  `rec_mem_correct`); the port's statement for any mean functional can take as hypotheses finitely
  many answers, open answer sets, and the covering of the vectors of means by their closures.
  PR #268 ports the rest of R11 from commit ccbde8e to
  `LMLExplore/Identification/StaticProportions.lean`: `IsStaticProportions` as a structure with
  named fields (`pos`, `sum_eq_one`, `isFixedBudgetFamily`, `ae_abs_pullCount_sub_le`,
  `outputAt_eq`; the pull-count field quantifies over the model before the budget), for any type
  of models; `staticClass` with a mean functional (`mean = id` on vectors of means), with
  `mem_staticClass_iff`, `IsStaticProportions.mem_staticClass`, `IsStaticProportions.mem_simplex`
  and `staticClass_nonempty`; `exists_isStaticProportions`, `IsStaticProportions.errorProb_eq`,
  `iSup_pos_iInf_cost_eq` and `staticDifficulty_eq_charTime`; and the mixing step of
  `iSup_pos_iInf_cost_eq` as `exists_pos_mem_simplex_mul_cost_le`
  (`Identification/Task/TransportationCost.lean`). It does not port `lem:exists_rec`
  (`D2023/Theorem1.lean`), and removes or renames no public declaration. The final bump moves the
  uses of the conjunction form of `IsStaticProportions` to its fields, and `staticClass` to its
  mean functional.
- R12: Identification 8.3 asks for the large deviations of the empirical means of independent
  samples with fixed proportions of arms with any laws whose cgf is finite near `0`, with the
  rate functions of Layer 1.2, and for the error exponent of the static-proportions algorithm
  recommending `i*(μ̂)` as the infimum of `∑ a, w a I_a(x_a)` over the vectors of means at which
  `i*(μ)` is not correct [GJ04]; [D23, Theorems 1, 12] are its exponential-family case under
  Assumption 1 (`D2023.IsRegular`, which the port should state for tasks on any mean functional).
  The recommendation rule needs the condition of erratum E1, and the families the closure
  hypothesis of E2. Proved, without `sorry`: the first half, in
  `ForLMLExplore/Bandits/StaticAllocation.lean` (namespace `LMLExplore.Bandits`), for any
  algorithms whose numbers of pulls satisfy `|N_{T,a} - T w a| ≤ k` almost surely and any laws of
  the arms whose empirical means satisfy a principle with a good rate function
  (`isLDP_empMean_of_abs_pullCount_sub_le`), in particular any laws whose cgf is finite near `0`
  with their Cramér rate functions (`isLDP_empMean_rateFunction_of_abs_pullCount_sub_le`). The
  proof works in LML's array model: the rows of `streamMeasure ν` are independent i.i.d.
  sequences (`streamMeasure_map_swap`), the upper bound is uniform over the numbers of samples
  `n a ≥ T w a - k` (`exists_eventually_streamMeasure_mean_mem_le`), and the lower bound holds for
  all the numbers of samples of the window at once
  (`exists_eventually_le_streamMeasure_forall_mean_mem`). [D23, Theorem 12] (`D2023/Theorem12.lean`)
  is its exponential-family case. The error exponent of static proportions ([D23, Theorem 1],
  `D2023/Theorem1.lean`) is proved for a measurable set of correct answers
  (`tendsto_errorRate_of_isStaticProportions_of_measurableSet`), over the empirical means in the
  convex supports of the arms (`LMLExplore.Bandits.ae_empMean_mem`, `StaticAllocation.lean`). Its
  headline statements take `[MeasurableSingletonClass ℐ]`, which the paper leaves implicit
  (`notes/statement-corrections.md`, Theorems 1 and 5); `tendsto_errorRate_of_isStaticProportions`
  and `oracleDifficulty_staticClass` are proved, the latter from its two halves at the models
  with a measurable set of correct answers: `staticDifficulty_le_oracleDifficulty_staticClass`, by
  the lower bound on the probability of error for every rule correct on the admissible models
  (`neg_le_liminf_log_errorProb_of_isStaticProportions`), and `oracleDifficulty_staticClass_le`,
  by the rate of the families of R11 with the rule of `exists_measurable_rec`. The rate uses only
  the openness of the answer sets from Assumption 1, and the oracle difficulty also the covering of
  the vectors of means by the closures of the answer sets (for the recommendation rule), which the
  port's statement for any mean functional can take as its hypotheses.
- R13: [D23, Theorems 2, 3, 13, Corollaries 4, 14], for every task; they use R5, the definitions
  of R9 and the bound `kl(a, b) ≥ a log (1/b) - log 2`, absent from LMLExplore (`lem:klBer_ge`, in
  `ForLMLExplore/InformationTheory/KullbackLeibler/Bernoulli.lean`), with the change of measure
  for fixed-budget algorithms (`ForLMLExplore/Identification/ErrorLowerBound.lean`) and the
  maximin bound `lem:iSup_iInf_mul` (`ForLMLExplore/Analysis/Convex/Simplex.lean`). The proof of
  Theorem 3 also covers alternatives at infinite divergence from `μ`. PR #258, merged on
  2026-11-09 (LMLExplore commit 26f37c75807e, after the pin), ports it from commit 5ca48e7, with
  the R9 definitions it uses (see R9), and removes or renames no public declaration. The final
  bump replaces the local copies of these files by the LMLExplore declarations.
- R14: Identification 8.3, third bullet: for two arms, the best static exponent is the Chernoff
  information `d(z, μ₁) = d(z, μ₂)` [D23, Lemmas 9, 19, 20]; the matching lower bound for
  consistent algorithms [KCG16, Theorems 12–13] is not part of this paper. Proved for any
  exponential family `ρ.expFamily T` on any space with any statistic, in
  `ForLMLExplore/Identification/Task/BestArmTwo.lean` (namespace `LMLExplore.Identification`:
  `inv_staticDifficulty_baiTask_two`, `iInf_cost_baiTask_two`, `isMaxOn_iInf_cost_baiTask_two`,
  `ofReal_div_le_inv_staticDifficulty_baiTask_two`), with no derivative: the cost of the
  alternatives is attained on the diagonal at the mean of natural parameter
  `w₀ η(μ₀) + w₁ η(μ₁)`, by the compensation identity with the free mean first, and the slope
  `x* = (ψ(η₀) - ψ(η₁)) / (η₀ - η₁)` bounds it for every allocation. The exponential-family
  lemmas go next to LMLExplore's `Probability/Distributions/ExponentialFamily/Mean.lean`
  (`sum_mul_expFamilyDiv_left_eq` and the Chernoff point `exists_mem_uIoo_deriv_cgf_eq_slope`,
  `expFamilyDiv_slope_eq`) and `RateFunction.lean` (`sq_div_le_expFamilyDiv_of_hasSubgaussianMGF`).
  The port needs `IdentTask.staticDifficulty` and `IdentTask.alternatives_restrict` (R9, R11). The
  D2023 files state the paper's forms and derive them from these: Lemmas 19 and 20 by
  specialization to the statistic `id`; the Gaussian case of Lemma 20 and Lemma 9 by computing `x*`
  for the Gaussian family and for the Bernoulli family generated by `Ber(1/2)`. PR #260 ports it
  from commit a424417, with `staticDifficulty` (body not exposed, new file
  `LMLExplore/Identification/StaticProportions.lean`) and `alternatives_restrict`, the two-armed
  results to `LMLExplore/Identification/Task/BestArm/StaticProportions.lean`, the Gaussian case in
  closed form (`staticDifficulty_baiTask_gaussianBandit_two`, `8 σ2 / (μ 0 - μ 1)²`) and Lemma 9 as
  `inv_staticDifficulty_baiTask_bernoulliBandit_two`; it drops the `NeZero ρ` hypothesis of
  `sq_div_le_expFamilyDiv_of_hasSubgaussianMGF`, and does not port the paper-form restatements of
  `D2023/Lemma19.lean` and `Lemma20.lean`. It moves the module
  `LMLExplore.Identification.Task.BestArm` to `LMLExplore.Identification.Task.BestArm.Basic`, and
  removes or renames no public declaration. Merged on 2026-11-09 (LMLExplore commit faf2c0906563,
  after the pin); the final bump replaces the local copies of these files by the LMLExplore
  declarations and moves the imports of `Task.BestArm` to `Task.BestArm.Basic`.
- R15: Theorem 5 is proved for measurable sets of correct answers (the `_of_measurableSet` lemmas
  of `D2023/Theorem5.lean`), and its headline statements, which take `[MeasurableSingletonClass ℐ]`
  as those of Theorem 1, follow from them. Theorem 6 remains.
- R15–R17: Identification 8.4, the results of [D23] on the existence of a complexity
  (Theorems 5–8 and 10, Lemmas 15–18). The proofs of Theorems 6 and 7 follow the corrections E3–E5
  of `notes/paper-errata.md`, and the one of Theorem 8 the correction E6.
- R17: Theorem 8 is proved (`D2023/Theorem8.lean`), for any class containing the static
  proportions algorithms, by Corollary 4 (R13) at the means `(0, -1, …, -(K - 1))`, with
  `H_𝒞 ≤ H^{sp} = T* ≤ 2 H_Δ` (R11, R7). It uses three library-shaped additions: the convexity and
  the closures of the answer sets of best arm identification on vectors of means
  (`ForLMLExplore/Identification/Task/BestArm.lean`: `convex_answerSet_baiTask`,
  `mem_closure_answerSet_baiTask_restrict`, `subset_iUnion_closure_answerSet_baiTask_restrict`,
  `interior_closure_answerSet_baiTask_restrict`, next to `isOpen_answerSet_baiTask` of LMLExplore's
  `Identification/Task/BestArm.lean`), the static-proportions difficulty of Gaussian arms with
  known variances as their characteristic time
  (`IdentTask.staticDifficulty_eq_charTime_gaussianReal`, added to
  `ForLMLExplore/Identification/Task/ExpFamily.lean` after the R16 port's commit; it needs
  `staticDifficulty`, R11), and `asymptoticRatio_le_of_le` (R9). Assumption 1 for best arm
  identification on any open convex set of vectors of means is `D2023.isRegular_baiTask`
  (`D2023/Setting.lean`), from these; it also covers the Bernoulli case `(0, 1)²` of Theorem 10.
  Theorem 10 is proved (`D2023/Theorem10.lean`), for any class containing the static proportions
  algorithms, by Corollary 4 at the means `(x (1 + x), x)` with Lemma 9 (R14) and
  `H_𝒞 ≤ H^{sp}` (`oracleDifficulty_le_staticDifficulty_baiTask_bernoulli`, for any number of
  arms); it bounds the paper's limit below rather than computing it. The library-shaped
  additions are in `ForLMLExplore/InformationTheory/KullbackLeibler/Bernoulli.lean`, next to the
  R13 lemma of that file (merged): `mul_klFun_div_le_klBerReal`
  (`q klFun (p / q) ≤ d(p, q)` for `p ≤ q`, `q ∈ (0, 1)`), `klBer_ne_zero_of_klBer_eq`, and
  `InformationTheory.antitoneOn_klFun` (Mathlib's `klFun` is antitone on `[0, 1]`); they belong in
  LMLExplore's `InformationTheory/KullbackLeibler/Bernoulli.lean`.
- R16: the static-proportions difficulty of Gaussian half-space identification with per-arm
  variances (`ForLMLExplore/Identification/Task/HalfSpace.lean`, [D23, Lemma 15]) generalizes
  LMLExplore's common-variance `Identification/Task/HalfSpace.lean`, with the reversed cost; the
  per-arm Gaussian transportation cost (`ForLMLExplore/Identification/Task/ExpFamily.lean`)
  generalizes `IdentTask.cost_gaussianBandit` and belongs next to it. The Lean proof of Theorem 7
  does not use Lemmas 17 and 18. PR #259 ports the part that does not need R9, R11 or Theorem 3
  (R13), from commit 76f5b36: the per-arm cost `IdentTask.cost_gaussianReal` and its symmetry,
  and LMLExplore's half-space file generalized in place to per-arm variances, with the
  `_gaussianBandit` statements renamed `altCost_halfSpaceTask_gaussianReal`,
  `answerValue_halfSpaceTask_gaussianReal`, `optAlloc_halfSpaceTask_gaussianReal` and
  `charTime_halfSpaceTask_gaussianReal`. What remains of R16 after it: Lemma 15 stated for the
  static-proportions difficulty, Lemma 16 and Theorem 7.

## Proposed targets
