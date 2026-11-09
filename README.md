# Degenne2023Existence

A Lean 4 formalization of *<title of the paper>* (<authors>, <venue, year>), on top of
[LMLExplore](https://github.com/LeanMachineLearning/LMLExplore), and so of
[LML](https://github.com/LeanMachineLearning/LML), [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
and [Mathlib](https://github.com/leanprover-community/mathlib4). Made from
[lml-paper-template](https://github.com/LeanMachineLearning/lml-paper-template).

- Website: https://RemyDegenne.github.io/Degenne2023Existence/, with the blueprint, the referee site and the
  literature links (which declarations formalize which results of the paper). CI builds it on each
  push to `main`. `scripts/formalize.sh` also commits the literature links, as
  `literature/annotations.jsonl`, when the paper is formalized and after the final bump.
- The paper: `source/`. Errors found in it, with their corrections: `notes/paper-errata.md`.
- The paper's results: `Degenne2023Existence/Deg2023/`, one file per result, listed with their status in
  `formalization.yaml`; comparator challenges in `comparator/`.
- Library-shaped material: `Degenne2023Existence/ForLMLExplore/`, which Tau Ceti workers port to LMLExplore;
  `PAPER_ROADMAP.md` says where each item goes.

## Building

```bash
scripts/build.sh
```

The script fetches Mathlib's and Tau Ceti's prebuilt files, then runs `lake build`; its arguments go
to `lake build`.

## Working on it

The workflow is the `formalize-paper` skill of the `lml` Claude Code plugin
([lml-claude](https://github.com/LeanMachineLearning/lml-claude)). Phase 1 (outline, blueprint,
statements) is done in a Claude Code session. After it, `scripts/formalize.sh`, in a terminal or
tmux, proves the rest and sends the reusable parts to LMLExplore.
