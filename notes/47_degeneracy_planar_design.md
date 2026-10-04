# 47 — Second-level frontier: graph degeneracy vs planar graphs

## Goal
Script 46's build order for the Erdős unit-distance bound starts with
(1) graph degeneracy, then (2) planar graphs. This script goes one level deeper
inside `SimpleGraph` and classifies each as an **assembly gap** (every primitive
exists, only the theorem must be put together) or a **layer gap** (a whole
conceptual layer is missing). Same name-regex + expected-module method; scope is
`Mathlib.Combinatorics.SimpleGraph` / `Graph`.

## Graph degeneracy — an ASSEMBLY gap (5/7 present)

| sub-prerequisite | verdict | evidence |
|---|---|---|
| per-vertex degree | present | `SimpleGraph.degree`, `Subgraph.degree` |
| neighbour set, card = degree | present | `neighborSet`, `card_neighborSet_eq_degree` (229) |
| induced subgraph / peel a vertex | present | `Subgraph`, `induce`, `Subgraph.deleteVerts` (1,311) |
| finite graph has a min-degree vertex | present | **`exists_minimal_degree_vertex`**, `le_minDegree_induce_of_support_subset` (82) |
| coloring machinery (deg+1 corollary) | present | `Coloring.Vertex`, `colorable_of_fintype` (209) |
| elimination/peeling ordering | **absent** | no graph ordering (generic Fintype/WellFounded only) |
| degeneracy definition + edge bound + equivalence | **absent** | the theorem itself |

**Reading.** The single hardest lemma a degeneracy proof needs — "every finite
graph has a vertex of minimum degree" — already exists
(`exists_minimal_degree_vertex`), as do induced subgraphs, vertex deletion,
neighbour-cardinality and coloring. What is missing is purely the assembly: an
inductive elimination ordering (peel a min-degree vertex via `deleteVerts`,
repeat on the induced subgraph) and from it the k-degeneracy definition, the
edge bound `|E| ≤ k|V| − C(k+1,2)`, and the (deg+1)-colorability corollary.
This is a small, self-contained, near-term contribution — the closest buildable
step on the whole unit-distance path, and independently useful graph theory.

## Planar graphs — a LAYER gap (3/6 present)

| sub-prerequisite | verdict | evidence |
|---|---|---|
| cycles / closed walks | present | `Walk.IsCycle` (218) |
| connectedness / components | present | connectivity suite (411) |
| trees / acyclic | present | `IsTree`, Acyclic, `maximal_isAcyclic_iff_isTree` (173) |
| geometric plane drawing | **absent** | 206 "embed" hits are graph-homomorphism embeddings (false friend), not plane drawings |
| faces / regions | **absent** | 0 |
| planar Euler formula V−E+F=2 | **absent** | 0 after excluding `IsEulerian` trails (another false friend); only abstract homological EulerCharacteristic elsewhere |

**Reading.** The purely combinatorial prerequisites (cycles, connectivity, trees)
exist, but the *topological* core — drawing an abstract graph in the plane,
defining faces, and deriving V−E+F=2 — is entirely absent and cannot be assembled
from SimpleGraph primitives; it needs a plane/topological embedding layer. This
is why the degeneracy route (pure combinatorics) is the right first target and
the planar/crossing route is a larger project.

## Consequence for the unit-distance path
The 46 build chain can start immediately at graph degeneracy: it is an assembly
gap whose central existence lemma is already in the library. Planar graphs, the
crossing lemma and then incidence/Szemerédi–Trotter remain layer-gap work. A
practical sequencing is therefore: **assemble degeneracy (small) → decide
whether the unit-distance bound can be reached via the K_{2,3}/Zarankiewicz
combinatorial route before investing in the planar/incidence layer.**

## Verification & files
`verify_degeneracy_planar_frontier.py` independently recomputes every hit count
and module list inside SimpleGraph, enforces present⇒hits>0 / absent⇒0 (with the
documented graph-homomorphism "embed" false friend excepted), and checks the
assembly/layer gap classification and summary → VERIFICATION OK.
* `script/python/47_degeneracy_planar_frontier.py`, `verify_degeneracy_planar_frontier.py`
* `data/degeneracy_planar_frontier.jsonl` (13 rows), `data/degeneracy_planar_summary.json`
