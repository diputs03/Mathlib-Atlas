# 40 — Area abstraction-maturity / opportunity-pressure profile

## Motivation
Prior discovery sweeps (16–37) found the mature stdlib core almost fully
abstracted — one positive new abstraction (`PointwiseLift`) and a string of
kernel-confirmed negatives. Per the working hypothesis, **contemporary /
frontier research areas are less developed and should carry more missing
abstractions**. Script 40 gives every one of the 32 areas a transparent maturity
profile from already-verified artifacts and tests that hypothesis.

## Proxies (all directly counted, no model)
Per area, from `atlas_features.jsonl` (joined with 38/39/14 summaries):
* **concrete-theorem fraction** — theorems with 0 implicit type binder AND 0
  instance binder, i.e. stated on a fixed carrier rather than polymorphically.
  Its complement is the *generic-statement share*.
* **mean instance constraints per theorem** — class-constraint richness.
* **rfl-closed fraction** — share of theorems discharged by reduction.
* **instance density**, proof/type term size, modules, namespace roots,
  classes instantiated, typeclass-bridge degree (39), reference degree (14).

**Maturity score** = mean of the cross-area percentile ranks of generic share,
constraint density, rfl share, instance density (∈ [0,1]). **Opportunity
pressure** = 1 − maturity, for areas with ≥500 declarations. Buckets are a
*declared* heuristic echoed in the output:
* **core** (10): Algebra, Data, Order, Logic, GroupTheory, RingTheory,
  FieldTheory, LinearAlgebra, Topology, Analysis.
* **frontier** (14): CategoryTheory, AlgebraicGeometry, AlgebraicTopology,
  Condensed, NumberTheory, RepresentationTheory, Geometry, Combinatorics,
  Dynamics, Probability, MeasureTheory, InformationTheory, ModelTheory,
  SetTheory.
* **infra** (8): Tactic, Lean, Control, Util, Testing, Init, Basic, Computability.

## Result — the hypothesis holds
| bucket | areas | generic share | concrete frac | mean constraints | rfl frac | maturity | opportunity |
|---|---|---|---|---|---|---|---|
| core | 10 | 0.950 | **0.050** | **2.35** | **0.072** | **0.654** | 0.346 |
| frontier | 14 | 0.889 | **0.111** | 1.86 | 0.049 | **0.513** | **0.502** |
| infra | 8 | 0.591 | 0.284 | 0.44 | 0.032 | 0.285 | 0.684 |

Frontier mathematical areas are markedly less abstracted than the core: they
have **2.2× the concrete-statement rate**, fewer class constraints per theorem,
and a maturity score ~0.14 lower. (Infra scores lowest but is meta-programming,
not mathematics, and is excluded from the math conclusion.)

### Frontier areas ranked by opportunity pressure (prioritized hunting ground)
| area | decls | concrete frac | opportunity |
|---|---|---|---|
| SetTheory | 5,582 | 0.308 | 0.790 |
| Dynamics | 1,390 | 0.117 | 0.694 |
| Combinatorics | 15,984 | 0.051 | 0.661 |
| NumberTheory | 14,475 | 0.170 | 0.661 |
| Condensed | 976 | 0.337 | 0.581 |
| Probability | 6,487 | 0.058 | 0.573 |
| AlgebraicTopology | 9,844 | 0.144 | 0.500 |

## Interpretation and caveats
* This is a **prioritization heuristic, not a claim** that any area contains a
  missing abstraction. A high concrete fraction is sometimes intrinsic (e.g.
  SetTheory/Computability deliberately reason about specific constructions), so
  every candidate still needs the same kernel-level follow-up as 23–25/29/33/37.
* It explains the earlier negative results and redirects effort: future analogy
  /generalization sweeps should be **stratified by area** and oversample
  SetTheory, Dynamics, Combinatorics, NumberTheory, Condensed, Probability,
  AlgebraicTopology rather than scanning uniformly (where the giant, mature core
  dominates counts).
* `Data` (core, opportunity 0.589) and `Analysis` (0.540) are notable within-core
  exceptions — large libraries with many concrete carrier lemmas worth a
  second look.

## Verification & files
`verify_area_maturity.py` independently recomputes every per-area counter, the
percentile composite, bucket means and conservation (rows sum to 574,391) →
VERIFICATION OK.
* `script/python/40_area_maturity_profile.py`, `script/python/verify_area_maturity.py`
* `data/area_maturity_profile.jsonl` (32 rows), `data/area_maturity_summary.json`
