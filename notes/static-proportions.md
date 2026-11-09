# Static proportions: the large deviation principle and the rate (Theorems 12 and 1)

## Theorem 12 (done, round of 2026-11-09)

- **Generality.** The principle is proved in `ForLMLExplore/Bandits/StaticAllocation.lean` for any
  family of algorithms `alg T` whose numbers of pulls satisfy `|N_{T,a} - T w a| ≤ k` almost
  surely, and any laws of the arms whose empirical means satisfy a large deviation principle with a
  good rate function `I a` (`isLDP_empMean_of_abs_pullCount_sub_le`). Cramér's theorem gives the
  case of laws whose cgf is finite near `0` (`isLDP_empMean_rateFunction_of_abs_pullCount_sub_le`),
  which Identification 8.3 asks for. Static proportions, the recommendation rule and exponential
  families appear only in `D2023/Theorem12.lean`.
- **No general product principle.** The blueprint's `lem:ldp_pi` (products of principles along
  speeds `n_k(T) / T → ω_k`) is not proved as such: the window of numbers of pulls needs bounds
  that are uniform over the numbers of samples, which the general statement does not give. The
  Lean proof states the two exponential bounds directly on the reward array, uniform over the
  numbers of samples `n a ≥ T w a - k` (upper bound) and for all the numbers of samples of the
  window at once (lower bound). The blueprint's `lem:ldp_pi` and `lem:ldp_window` now say this.
- **Array model.** The laws transfer from `trajMeasure` to LML's `ArrayModel.arrayMeasure` through
  `IsAlgEnvSeq.identDistrib_pullCount_sumRewards`, and the empirical mean of an arm there is the
  mean of the first `N_{T,a}` entries of its row (`ArrayModel.sumRewards_eq`). The rows of
  `streamMeasure ν` are independent i.i.d. sequences (`streamMeasure_map_swap`, by currying the
  product measure twice).
- **Lower bound in the window.** Asking the means after every number of pulls of the window to be
  near the target is done by asking the mean of the first `⌈T w a - k⌉₊` entries to be within
  `δ / 2` and the next `2 k + 1` entries to be within a fixed `L a` of the target, an event of
  probability bounded below by a constant times the probability of the first.

## Theorem 1 (done for measurable correct answers, round of 2026-11-09)

- **Blocked headline.** The frozen statements of Theorems 1 and 5 take any σ-algebra on the answers
  `ℐ`; for the trivial one, the probability of error is an outer measure equal to `1`, and the four
  statements are false (`notes/statement-corrections.md`, Theorems 1 and 5, with a Lean
  counterexample). They wait for `/lml:formalize-paper decide`; the recommended fix is
  `[MeasurableSingletonClass ℐ]`.
- **What is proved.** `tendsto_errorRate_of_isStaticProportions_of_measurableSet` (hypothesis
  `MeasurableSet (task.correct μ)` at the model) and the two forms of Theorem 5 with
  `∀ μ ∈ task.M, MeasurableSet (task.correct μ)`. The upper half of the proof is its own lemma,
  `eventually_errorProb_le_of_isStaticProportions`, which Theorem 5 uses at the models without
  alternatives (the error probability then vanishes for `T` large, so the ratio to
  `H^{sp} = 0` is `0`, not `∞`).
- **Measurability.** The recommendation rule `rec` is not assumed measurable; the output kernel
  makes `rec ∘ μ̂_T` measurable on the histories, which is all `IsStaticProportions.errorProb_eq`
  needs. The LDP bounds hold for every set, so no measurability of the error set in `ℝ^K` is
  needed either: the lower bound goes through the open set of alternatives, the upper bound
  through the closed set `cl(S) ∩ cl(Alt_i)`.
- **Unused hypotheses.** The proof uses from Assumption 1 only the inclusion `𝒟 ⊆ S` and the
  openness of the answer sets, and not the finiteness of `ℐ`.

The plan that the proof followed:

`tendsto_errorRate_of_isStaticProportions`, at a model `μ ∈ task.M` with answer `i`, rate
`J x = ∑ a, w a dbar(x a, μ a)`, `L = ⨅ μ' ∈ task.alternatives μ, task.cost w μ' μ`:

1. **Lower bound on the error.** The alternatives to `μ` form the open set `⋃_{j ≠ i} 𝒟_j`
   (Assumption 1, single answer), on which `rec` errs (`hrec`: a point of the open `𝒟_j` is not in
   the closure of `alt j`). The lower bound of Theorem 12 on it gives
   `-L ≤ liminf (1 / T) log p_T`, since `J = cost` on the admissible models.
2. **Upper bound on the error.** The error event lies in `{μ̂ ∈ closure S ∩ closure (alt i)}`
   (contrapositive of `hrec`) plus `{μ̂ ∉ closure S}`, `S` the vectors of means. The second is
   null for `T` large: the samples lie in the closure of the means (`hρ_closure`, through
   `expFamily_absolutelyContinuous`), which is convex, and `N_{T,a} > 0`. On the closed first set,
   `J ≥ L` by the continuity of `dbar(·, μ a)` on the closure of the means (LMLExplore's
   `Measure.continuousOn_expFamilyRate_left`, `lem:rate_continuousOn`), since its points are
   limits of alternatives. The upper bound of Theorem 12 gives `limsup (1 / T) log p_T ≤ -L`.
3. **The rate.** `lem:tendsto_errorRate_iff` turns `(1 / T) log p_T → -L` into
   `h_T = T / log (1 / p_T) → L⁻¹`, with the conventions of `errorRate` in `ℝ≥0∞` (the case
   `L = ∞`, where `p_T` may vanish, and `L = 0`).

`oracleDifficulty_staticClass` then needs `lem:exists_static` (a static proportions family for
every `w ∈ Δ_K^0`, from LMLExplore's cumulative tracking), `lem:exists_rec` and
`lem:iSup_open_simplex`; its lower bound uses only step 1, for every rule correct on `𝒟`. These
remain, and Theorems 6, 8 and 10 need the upper half (`lem:oracleDifficulty_staticClass_le`).
Theorem 5 followed from Theorem 1 alone.
