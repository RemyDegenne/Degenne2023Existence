# Comparator setup

Machine-checkable verification, with [leanprover/comparator](https://github.com/leanprover/comparator),
that this repository proves the headline results claimed in [`formalization.yaml`](../formalization.yaml)
without having to read or trust the Lean development in `Degenne2023Existence/`.

**Status.** Phase 1 (2026-11-09): the 24 challenges are generated and compile (`lake build
Comparator`); none is proved yet, so comparator does not pass.

Each challenge is one file that imports modules of LMLExplore, LML, Tau Ceti and Mathlib only (those
the project uses), no project modules and no sibling helpers.

## The trust story

For each headline theorem `Degenne2023Existence.<name>` there is a challenge file `Challenge_<name>.lean` and a
config `<name>.json`; the list is `targets.txt`:

| paper result | challenge(s) |
|---|---|
| Theorem 1 | `tendsto_errorRate_of_isStaticProportions` |
| Theorem 1 (displayed consequence) | `oracleDifficulty_staticClass` |
| Theorem 2 | `inv_difficultyRatio_mul_le` |
| Theorem 3 (first inequality) | `inv_iSup_asymptoticRatio_le` |
| Theorem 3 (second inequality) | `inv_maxRatio_le` |
| Corollary 4 | `sum_inv_le_iSup_asymptoticRatio` |
| Theorem 5 | `maxRatio_staticDifficulty_le_of_isStaticProportions` |
| Theorem 5 (uniform allocation) | `maxRatio_staticDifficulty_le_card` |
| Theorem 6 | `iInf_maxRatio_minThresholdTask_eq_card` |
| Theorem 7 | `one_le_iInf_maxRatio_of_hyperplane` |
| Theorem 8 | `ofReal_mul_log_le_iInf_maxRatio_baiTask_gaussian` |
| Lemma 9 | `inv_staticDifficulty_baiTask_bernoulli_two` |
| Theorem 10 | `one_lt_iInf_maxRatio_baiTask_bernoulli_two` |
| Lemma 11 | `isLDP_empiricalMean_expFamily` |
| Theorem 12 | `isLDP_empMean_of_isStaticProportions` |
| Theorem 13 | `inv_liminf_iSup_difficultyRatio_le` |
| Corollary 14 | `inv_liminf_iSup_difficultyRatio_le_liminf` |
| Lemma 15 | `inv_staticDifficulty_halfSpaceTask_gaussian` |
| Lemma 16 | `one_le_iInf_maxRatio_halfSpaceTask_gaussian` |
| Lemma 19 | `inv_staticDifficulty_baiTask_expFamily_two` |
| Lemma 19 (the minimizers) | `iInf_cost_baiTask_expFamily_two` |
| Lemma 19 (the maximizer) | `isMaxOn_iInf_cost_baiTask_expFamily_two` |
| Lemma 20 | `ofReal_div_le_inv_staticDifficulty_baiTask_two` |
| Lemma 20 (Gaussian case) | `inv_staticDifficulty_baiTask_gaussian_two` |

Each challenge states the theorem with `sorry`, with every definition of the project that the
statement rests on copied verbatim from its source by
[challenge-gen](https://github.com/LeanTrustBuilders/challenge-gen); the definitions of
LMLExplore, LML, Tau Ceti and Mathlib that it uses are imported. A reader checks the *statement*
(the challenge file) by hand and lets comparator check that the project proves exactly it, with
no axioms beyond `propext`, `Classical.choice` and `Quot.sound`, the proofs replayed through the
kernel. The config also lists the lemmas the definitions use, left `sorry` in the challenge and
proved by the project, and the theorems Lean makes of the proofs inside definitions.

## Regenerating and running

`scripts/make-challenges.py` regenerates every challenge and config from `targets.txt`;
`lake build Comparator` checks that they compile; `scripts/comparator-verify.sh [--insecure]`
runs comparator on every config (see the script header for the sandbox requirements).
