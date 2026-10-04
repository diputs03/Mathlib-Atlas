# 42 — Frontier-stratified generalization scan

## Question
Script 40 predicted frontier areas carry more missing-abstraction pressure;
script 36 found 0 missing generalizations globally. This script applies 36's
**exact** generic/specialized classifier and filters, but keeps each repeated
shape group's area profile, to (a) measure missing-generalization pressure per
area, (b) test the frontier prediction at the shape-group level, and (c) emit a
frontier shortlist. Built-in consistency check: the post-filter survivor set
must reproduce 36's 5.

## Result 1 — pressure is indeed 4.4× higher in frontier areas
Specialized-only repeated shape groups (≥3 specialized members, no generic) per
1,000 theorems, bucket means (areas ≥500 theorems):

| bucket | groups / 1k theorems |
|---|---|
| core | 1.06 |
| **frontier** | **4.69** |
| infra (metaprogramming) | 6.60 |

Highest-pressure areas: Condensed 27.7, AlgebraicGeometry 25.3 (125 groups),
NumberTheory 9.2 (69), SetTheory 8.0, AlgebraicTopology 7.3. This confirms
script 40's prediction on an independent, stricter signal (repeated shape
groups rather than the single-declaration concrete fraction).

## Result 2 — but the extra repetition is NOT missing named-operator lemmas
Rejection-reason share within specialized-only groups:

| reason | core | frontier |
|---|---|---|
| class/prop-fact head (per-carrier fact derivation) | 0.343 | **0.503** |
| bare logical head (Eq/Iff/Exists/order) | 0.143 | 0.275 |
| empty constraints | 0.479 | 0.186 |
| single-carrier / artifact | 0.024 | 0.029 |
| **survives as a candidate generic** | **0.010** | **0.007** |

Frontier areas repeat more, but half of that extra repetition is *per-carrier
class/prop-fact derivation* and another quarter is concrete equalities/order
facts — the expected developmental work of a young area (establishing instances
and concrete facts for newly introduced objects), not the same abstractable
named-operator lemma restated over carriers. The named-operator survivor share
is in fact slightly *lower* in the frontier (0.7% vs 1.0%).

Post-filter survivors = **5**, exactly reproducing script 36; only two are
frontier-majority (`Differentiable`, `ContinuousOn` over NumberTheory
L-functions), and both were already triaged in 36/37 as heterogeneous facts.
No new Lean candidate arises, so no kernel probe is warranted.

## Interpretation
This sharpens — rather than overturns — the 40 hypothesis:
* Frontier areas ARE less abstracted and repeat more (4.4× pressure), so they
  remain the right place to watch as they mature.
* But the current frontier backlog is **concrete fact / instance accumulation**,
  which is normal growth, not a stock of duplicated abstractable theorems.
* A missing *named-operator* generic is rare everywhere (0 globally, 36); the
  single genuine new abstraction across the whole project remains
  `PointwiseLift` (23–25).
* Practical implication: future frontier sweeps should target the
  class/prop-fact and concrete-computation streams with *different* detectors
  (e.g. "many carriers derive the same class fact without a generic instance
  construction"), not reuse the named-theorem generalization lens unchanged.

## Verification & files
`verify_frontier_scan.py` independently rebuilds groups, per-area density,
rejection reasons and bucket means, and asserts the 36-consistency (5 survivors)
→ VERIFICATION OK.
* `script/python/42_frontier_generalization_scan.py`
* `script/python/verify_frontier_scan.py`
* `data/frontier_generalization_shortlist.jsonl` (5 rows),
  `data/area_opportunity_density.jsonl` (32 rows),
  `data/frontier_scan_summary.json`
