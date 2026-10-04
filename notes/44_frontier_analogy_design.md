# 44 — Frontier-restricted analogy map

## Question
42/43 showed frontier repetition is concrete growth on existing generics and
recommended an *analogy* lens (not another missing-lemma detector). This script
reuses the already-computed pair artifacts (no re-embedding) and asks: which
**frontier** declarations have a near-identical-shape counterpart in a mature
**core** area under a *different conclusion head* — the signature (cf. the one
positive, Set↔Filter `PointwiseLift`) of an abstraction solved in the core that
the frontier re-derives?

## Inputs & cuts
* Structural pairs `embedding_cross_area_analogies.jsonl` (cosine ≥ 0.90),
  semantic pairs `semantic_hidden_candidates.jsonl` (cosine ≥ 0.85); heads from
  type skeletons; area buckets from script 40.
* All frontier-involved cross-area pairs: frontier↔core 1,791,
  frontier↔frontier 392, frontier↔infra 230.
* Shortlist = frontier↔core, **different** conclusion heads, deduped by decl
  pair and grouped by (frontier area, donor area, frontier head, core head).

## Result — 73 different-head groups, 0 unresolved, 0 new abstractions
| triage | n | meaning |
|---|---|---|
| wrapperVariant | 17 | both heads are logical/categorical wrappers (Eq/Iff/Mono/Epi/…) over one construction — e.g. AlgebraicGeometry `SheafedSpace` stalk criteria vs `TopCat.Presheaf` stalk criteria, both already on generic category/presheaf-colimit machinery. |
| sharedHeadFamily | 56 | the two heads are spellings of one already-generic family: manifold `M`-prefix / global-At-On-WithinAt locality variants (`ContMDiff*`↔`ContDiff*`, `HasMFDeriv*`↔`HasFDeriv*` — case G, 30), the `Filter.Eventually*` family (case F, 29), `Preserves*Homology`, `SplitEpiCategory`↔`IsSplitEpi`, `Injective`↔`Injective2` (the latter is *defined* as `∀ a, Injective (f a)`). |
| **unresolved** | **0** | — |

The decisive distinction from `PointwiseLift`: a positive requires two
constructions with **no shared generic**. Here every group's two sides already
share the unifying generic — either as a common constraint class in the
structural signature (`C:Category…`, `C:Field/Valuation`) or as a common concept
head family. The "different head" is only a wrapper or a locality/qualifier
spelling. No Lean probe is warranted: these families were kernel-decided in
29/30 or are definitional variants.

## Descriptive finding — the donor map
Although negative for new abstractions, the donor map quantifies *where each
frontier area's analogical structure is already solved*:

| frontier area | analog groups | principal donor core areas |
|---|---|---|
| Geometry | 33 | Analysis (104 pairs), Topology (17) |
| MeasureTheory | 13 | Analysis (26), Order (19) |
| CategoryTheory | 8 | Algebra (13) |
| RepresentationTheory | 2 | Algebra (8), RingTheory (4) |
| others (SetTheory, NumberTheory, Probability, AlgebraicGeometry, Combinatorics, AlgebraicTopology, Dynamics) | 1–4 each | Analysis / RingTheory / Data / Order / Topology |

Geometry's frontier smoothness/manifold material is overwhelmingly structured by
Analysis (the manifold generic of case G); MeasureTheory draws on Analysis and
the Order/Filter layer. This is a map of conceptual debt: the strongest analog
signals point at generics that already exist, so any future frontier abstraction
hunt should target the thin donor columns (e.g. Dynamics/Combinatorics with only
one analog link), not the saturated Geometry–Analysis axis.

## Verification & files
`verify_frontier_analogy_map.py` independently rebuilds filtering, grouping,
token-family triage and donor totals from the raw pair files; asserts group
bijection, the 17/56 split, unresolved=0, sort order → VERIFICATION OK.
* `script/python/44_frontier_analogy_map.py`, `verify_frontier_analogy_map.py`
* `data/frontier_analogy_shortlist.jsonl` (73), `data/frontier_donor_map.jsonl`,
  `data/frontier_analogy_summary.json`
