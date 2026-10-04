# 14 — Graph analysis

Script 14 is the first layer that **combines** the corpus rather than extracting
from Lean. It is pure Python (no Lean run): it streams the labelled reference
graph from 09 and the structural links from 12 onto the node frame from 13, and
computes graph-theoretic signals at three granularities — declaration, source
module, and top-level mathematical area.

* Analyzer:  `script/python/14_graph_analysis.py`
* Verifier:  `script/python/verify_graph.py` (independently re-streams 09/12)
* Summary:   `notes/14_graph_summary.txt` (full distributions and rankings)

## Inputs and graph definition

* **Nodes** — the 574,391 Mathlib declarations from 13 features, each with
  module and top-level **area** (the segment after `Mathlib.`, e.g.
  `Mathlib.Algebra.Group.Defs → Algebra`; 32 areas).
* **Term-reference edges** — 16,316,230 distinct directed edges from 09
  (one row per distinct source→target), each carrying a **multiplicity** =
  total `Expr.const` occurrences, decomposed by structural role
  (type/value × head/arg × main/binder). Targets outside Mathlib (core/Std)
  are counted as external, never as nodes.
* **Structural links** — 80,374 environment-encoded links from 12
  (constructor/recursor/projection/equationLemma/structExtends/…), kept as a
  separate axis (`structLinks`, never merged into reference degree).

Direct one-hop edges only — no transitive, axiom, or reduction closure (those
remain downstream choices). Edge labels are preserved throughout.

## Outputs

### `data/atlas_node_graph_stats.jsonl` (574,391 rows)
Per declaration: `outRefs/inRefs` (multiplicity), `outNeighbors/inNeighbors`
(distinct counterparties), type-vs-value split both directions, the four role
buckets both directions, `selfRefs`, `structLinks` + `structByKind`, and
carried identity/flags (kind, module, area, namespace, conclusionHead,
isClass/isInstance/valueIsRfl).

### `data/atlas_module_graph.jsonl` (8,287 rows)
Per module: declaration count, internal (same-module) reference multiplicity,
cross-module in/out, references to non-Mathlib targets, cross-area in/out
(bridge weight), distinct in/out modules, distinct areas reached/reached-by,
and structural-link count.

### `data/atlas_area_summary.jsonl` (32) + `data/atlas_area_edges.jsonl` (437)
Per-area internal/out/in multiplicity and area reach; and the weighted directed
area→area edge list (437 of 32×31 = 992 ordered area pairs are connected).

## Headline findings

**Scale and degree distribution (heavy-tailed).** 752,376,214 total reference
occurrences over 16,316,230 distinct edges; 162,354,213 occurrences (21.6%)
target core/Std outside Mathlib. Median declaration makes 103 references to 21
distinct neighbours, but p99 outRefs ≈ 19.7k; median inRefs is 1 and
**176,006 declarations (30.6%) are never referenced** — a large leaf/fringe.
Only **839 declarations have zero outgoing references** (matches the count
established in 08/09).

**Foundational hubs are typeclass-coercion definitions, not theorems.** The
top in-hubs are `Real`, then instance-coercion projections such as
`CommSemiring.toSemiring`, `CommRing.toCommSemiring`,
`AddCommGroup.toAddCommMonoid`, `CategoryStruct.toQuiver` — the algebraic
hierarchy's forgetful/coercion chain is the literal backbone of the graph.
The largest out-degrees are machine-generated `_proof_n` terms
(`CategoryTheory.CommShift₂Setup`, algebraic-geometry gluing proofs) — the
heaviest proof terms, not human lemmas.

**A clear dependency-direction / layering at area level.** `Algebra`
(in 173.6M) and `Data` (in 89.6M) are the dominant sinks; the strongest
cross-area flow is `RingTheory → Algebra` (47.6M), followed by
`Analysis → Data/Algebra`, `LinearAlgebra → Algebra`. Consumer areas with
near-zero incoming flow — `AlgebraicGeometry` (in 87), `RepresentationTheory`
(52), `NumberTheory` (36k), `Condensed`/`InformationTheory` (0) — sit at the
top of the formalization stack and depend broadly downward.

**Bridge modules (cross-domain integrators).** Ranking modules by distinct
other areas reached: `NumberTheory.NumberField.CanonicalEmbedding.*` and the
`AlgebraicGeometry.*` modules reach 13–15 of 32 areas (e.g.
`AlgebraicGeometry.Modules.Tilde`, cross-area out 2.56M) — exactly the kind of
module that fuses otherwise distant areas, and natural seeds for 15's
analogy/bridge experiments.

**Reduction-heavy anomalies.** The rfl-closed proofs with the largest terms
hit the 50,000-node walk cap (e.g. `SpecModulesToSheafFullyFaithful._proof_6`,
several category-theory limit/colimit `_proof_n`): equalities discharged by
definitional reduction through enormous terms — a distinct signal from
lemma-chaining proofs, and candidates to inspect for abstraction opportunities.

## Verification

`verify_graph.py` independently re-streams 09 and 12 and checks: exact node
(574,391) / module (8,287) / area (32) counts and unique names;
ΣoutRefs = total multiplicity = ΣinRefs + external; ΣoutNeighbors = 09 row
count; multiplicity ≥ distinct neighbours everywhere; type+value and
role-bucket decompositions re-sum to outRefs; the module partition
internal+cross+external and area partition internal+cross-area+external both
equal total multiplicity; module/area nDecls sum to the node count;
ΣstructLinks = independently counted Mathlib link endpoints (97,118).
Result: **VERIFICATION OK**.

## Caveats / non-scope

* Multiplicity counts term occurrences and is dominated by repeated coercion
  projections; `*Neighbors` (distinct counterparties) is the robust degree for
  structural comparison — both are provided.
* "Area" is a coarse, name-derived grouping of *modules* for navigation; it is
  not yet an inferred mathematical theory (that inference is a later target).
* Exact betweenness/centrality on 574k nodes/16M edges is intentionally not
  computed; bridge signals here use breadth of area/module reach. Weighted
  centrality and community detection are candidates for a follow-up.

## Reproduce

```
python script\python\14_graph_analysis.py
python script\python\verify_graph.py
```
