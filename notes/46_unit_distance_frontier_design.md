# 46 — Dependency frontier for the Erdős unit-distance problem

## Goal
Script 45 ranked Erdős unit-distance the most research-ready famous problem
(named object already present). This script decomposes the classic
Spencer–Szemerédi–Trotter `u(n) = O(n^{4/3})` upper bound into its proof
ingredients and measures, from the pinned corpus, which exist, which are
partial, and which are the frontier to build. Each ingredient is matched by name
regex **and** by expected module location, so keyword false-friends are exposed
rather than mistaken for coverage.

## Coverage map (verifier VERIFICATION OK)

| step | ingredient | layer | verdict | footprint |
|---|---|---|---|---|
| 1 | unit-distance graph object | combinatorial | **present** | `SimpleGraph.UnitDistEmbedding`, 31 |
| 2 | Euclidean / inner-product plane | geometric | **present** | InnerProductSpace/Euclidean, 3,804 in expected modules |
| 3 | Turán extremal bounds | combinatorial | **present** | Extremal.Turan, 126 |
| 4 | Zarankiewicz K_{s,t}-free bound | combinatorial | **present** | Extremal.Zarankiewicz, 31 |
| 5 | Euler characteristic | topological | **partial** | abstract/homological EulerCharacteristic (41); no planar V−E+F |
| 6 | geometric point–line incidence I(P,L) | geometric | **absent** | 327 raw hits are IncidenceAlgebra/graph incidence (false friend) |
| 7 | Szemerédi–Trotter theorem | geometric | **absent** | 171 raw hits = regularity lemma / Ruzsa–Szemerédi (false friend) |
| 8 | crossing number / crossing lemma | topological | **absent** | 125 raw hits = martingale upcrossing (false friend) |
| 9 | planar graph + planar Euler formula | topological | **absent** | 18 raw hits = coplanar affine vectors (false friend) |
| 10 | graph degeneracy (k-degenerate) | combinatorial | **absent** | 446 raw hits = nondegenerate matrices/simplices (false friend) |

## The frontier, precisely
The **combinatorial half of the proof is built** (the target graph, the ambient
Euclidean space, Turán and — crucially — the Zarankiewicz K_{2,3}-free bound that
encodes "two points lie together on at most two unit circles"). The
**incidence-geometric and planar-topological half is entirely absent**, and
naive keyword search would badly overstate coverage: five ingredients have large
raw name-hit counts (327/171/125/18/446) but **zero** declarations in the module
where the needed concept could live — every hit is a different mathematical
object sharing an English word.

### Required build order (each unblocks the next)
1. **graph degeneracy** — a k-degenerate graph has ≤ kn−… edges (pure
   combinatorics; closest to existing SimpleGraph material).
2. **planar graphs** — planar embedding + the planar Euler formula V−E+F=2 (the
   abstract homological Euler characteristic of step 5 is a starting point, not
   the planar statement).
3. **crossing lemma** — crossing-number inequality `cr(G) ≥ e − 3v`, and the
   probabilistic `cr(G) ≥ e³/(64v²)` form; depends on (2).
4. **point–line incidence** — define I(P,L) for finite point/line sets in the
   plane.
5. **Szemerédi–Trotter** — `I(P,L) = O(n^{4/3})` via the crossing lemma.
6. **unit-distance bound** — reduce unit distances to point–(unit)circle
   incidences and apply (5) + the step-4 Zarankiewicz fact to reach `u(n) =
   O(n^{4/3})`.

Steps 1–3 are general graph theory (reusable far beyond this problem); steps 4–5
are incidence geometry; step 6 is the problem-specific join. The Atlas edge/
relation corpus can next quantify, for each missing ingredient, which of its OWN
prerequisites already exist (a second-level frontier) — e.g. how close
SimpleGraph is to supporting a degeneracy ordering or a planar-embedding API.

## Methodological note
This is a reusable "research-target dependency frontier" template: decompose a
target theorem into ingredients → match each by name AND expected module →
classify present/partial/absent with false-friend notes → emit a build order.
Script 45 supplies the target list and readiness ranking; this script is the
one-level-deep frontier for the top target. It is complementary to, not a
substitute for, a human proof sketch — the ingredient decomposition is authored,
the coverage is measured.

## Verification & files
`verify_unit_distance_frontier.py` independently recomputes name hits and
expected-module counts, asserts present⇒coverage>0 / absent⇒coverage=0, module
bijection and summary consistency → VERIFICATION OK.
* `script/python/46_unit_distance_frontier.py`, `verify_unit_distance_frontier.py`
* `data/unit_distance_frontier.jsonl` (10 rows), `data/unit_distance_frontier_summary.json`
