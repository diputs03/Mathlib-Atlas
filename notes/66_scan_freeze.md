# 66 — Freeze of the map-family scan

Date: 2026-09-23

## What is frozen

The campaign that began with script 64's structural channel and concluded with
script 66's falsification is closed to further expansion:

- No further searches for unary `map`, binary `map₂`/`zipWith`, `bind`, or
  `pure` families across Mathlib.
- No additional candidate constructors will be added to the orphan-functor
  census.
- The PR candidate material (`notes/66_pr_candidate.md`) is complete as a
  proposal and will not be grown into Applicative/Monad proposals without an
  explicit new instruction.

## Final index of the campaign

- Detector: `script/python/64_stdlib_semantic_analogies.py` (structural
  channel; 1,973 pairs; 549 clusters) + verifier.
- Falsification: `script/lean/66_orphan_functor_falsification.lean` —
  **6/6 candidates clean omissions**, kernel-verified downstream, EXIT=0,
  empty log; Sym2/WithBot/WithTop/OnePoint/Stream' reuse already-proved laws,
  Cycle's two laws proved in the experiment.
- False-positive classes documented: hypothesis-constrained lifts,
  alias-of-integrated-type, lift-without-proved-laws, elaboration lookalikes,
  same-theory duplicates (`notes/66_orphan_functor_case_study.md` §4).
- Standing result: the mature stdlib's missing-integration signal is
  structural; semantic scanning maps propagation/renaming debt.

## Hand-back

Center of gravity returns to **discovery of a different phenomenon** over the
now-larger adjudicated dataset (features + skeletons + 64 pairs/clusters + 66
verdicts). The four-gate omission test established here (no instance present;
signature matches; laws present or proved; no hypotheses/diamond) becomes the
standard falsification template for future class-integration candidates.
