# 39 — Typeclass bridge structure (instance graph as theory glue)

## Question
14/15 found bridges on the **reference-edge** graph and 38 found cross-cutting
**namespaces**; this script measures a third, distinct conduit — the **instance
graph**. An abstract class is a *typeclass bridge* when concrete instances of it
are declared across many top-level areas. Such classes are the abstract
vocabulary that lets one area reuse another's machinery. Inputs:
`atlas_instances.jsonl` (className/targetHead/module), `atlas_classes.jsonl`
(parent count = hierarchy-depth signal).

## Scale
* 43,221 instances total, **33,215 Mathlib** (all area-tagged), over **2,002
  classes that have ≥1 instance**.
* **532 bridge classes** span ≥3 of the 32 areas; **452 area pairs** share at
  least two classes.

## Two bridge archetypes
**(a) Foundational root plumbing (parents = 0).** Hundreds of carriers, present
everywhere, low mathematical content per instance:

| class | areas | instances | carriers |
|---|---|---|---|
| Inhabited | 30/32 | 1,074 | 1,030 |
| SizeOf | 29 | 1,572 | 1,571 |
| Decidable | 23 | 563 | 270 |
| Zero | 22 | 245 | 199 |
| Add | 22 | 195 | 170 |

**(b) Algebraic workhorse structures (mid-hierarchy, parents ≥ 1).** Fewer
*canonical* carriers but very wide area reach — these are the real conceptual
glue, with a high reach-per-carrier ratio:

| class | areas | instances | carriers | parents |
|---|---|---|---|---|
| PartialOrder | 20 | 276 | 240 | 1 |
| Unique | 20 | 250 | 148 | 1 |
| Module | 17 | 284 | **43** | 1 |
| AddCommGroup | 17 | 200 | 165 | 2 |
| CompleteLattice | 17 | 101 | 88 | 4 |
| Monoid | 16 | 108 | 90 | 5 |
| Algebra | 14 | 220 | **33** | 1 |
| MulAction | 14 | 177 | 44 | 1 |

`Module` and `Algebra` are striking: they span 17/14 areas on only 43/33
carriers — a small set of canonical module/algebra carriers carries linear
machinery into Analysis, Geometry, RepresentationTheory, etc. Of the 532 bridge
classes, 342 are hierarchy roots and 190 are derived; derived classes have a
slightly *higher* mean area spread (2.99 vs 2.37 areas), so bridge-ness is not
just "being a primitive root".

## Which areas the instance graph glues most
Area pairs ranked by number of shared abstract classes:

| shared classes | area pair |
|---|---|
| 234 | Algebra ↔ Topology |
| 222 | Algebra ↔ CategoryTheory |
| 214 | Algebra ↔ RingTheory |
| 209 | Analysis ↔ Topology |
| 204 | Algebra ↔ Data |
| 189 | Algebra ↔ Order |
| 172 | Data ↔ Order |
| 169 | Algebra ↔ Analysis |

Algebra is the hub of the typeclass graph (it appears in 6 of the top 8 pairs),
and the Algebra–Topology / Analysis–Topology couplings quantify where the
ordered/topological-algebraic fusion lives. This is a *different* bridge ranking
from raw reference edges (14): it weights shared abstractions rather than call
volume, so it highlights conceptual rather than implementation coupling.

## Consequence for Atlas
* The 532 bridge classes — especially the 48 substantive ones (parents ≥ 1,
  ≥8 areas) — are a high-priority "abstraction vocabulary" list for analogy and
  conjecture work: a structure that appears across many areas is exactly where a
  cross-area analogy is most likely to be valid.
* Reach-per-carrier (areas / carriers) flags abstractions that punch above their
  instantiation count (`Module`, `Algebra`, `MulAction`) — candidates for
  "small carrier set, huge leverage" theory cores.
* Three independent bridge views now exist and should be kept as separate edge
  labels rather than merged: reference edges (14), namespaces (38), instances
  (39). Their agreement and disagreement is itself signal.

## Verification & files
`verify_typeclass_bridge.py` independently rebuilds class and area-pair
aggregations, checks headline counts, instance conservation (33,215), class and
pair bijections, area-breakdown summation and deterministic order →
VERIFICATION OK.
* `script/python/39_typeclass_bridge_structure.py`
* `script/python/verify_typeclass_bridge.py`
* `data/typeclass_bridge_summary.json`, `data/typeclass_bridge_classes.jsonl`
  (2,002 rows), `data/area_class_bridges.jsonl` (452 rows)
