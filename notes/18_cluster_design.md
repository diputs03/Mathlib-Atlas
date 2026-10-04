# 18 — Clustering the embedding similarity graph into analogy communities

**Status: run + independently verified (VERIFICATION OK).**
Script `script/python/18_cluster_analogies.py`; verifier
`script/python/verify_clusters.py`; logs `notes/18_cluster.log`,
`notes/18_verify.log`. Pure Python, deterministic (sorted nodes/edges, no
randomness). Builds directly on script 17.

## 1. Inputs and graph

* Nodes/edges come from `data/embedding_nearest_neighbors.jsonl` (top-8
  neighbours per declaration at cosine ≥ 0.70). Reciprocal top-K entries are
  merged into one **undirected weighted** edge whose weight is the maximum
  cosine seen. Labels (kind/module/area) come from script 13 features.
* Result: **52,959 nodes, 177,813 undirected edges**; edge cosine median 0.83.

## 2. Why connected components at a high cut

The graph is already similarity-filtered, so a deterministic, interpretable
community definition is appropriate: union-find connected components after
keeping only edges with cosine ≥ threshold (single-linkage analogy
communities). A sweep shows the trade-off:

| threshold | edges kept | communities ≥2 | clustered nodes | largest |
|---|--:|--:|--:|--:|
| 0.95 | 30,613 | 7,506 | 22,428 | 42 |
| 0.92 | 44,357 | 8,024 | 26,901 | 46 |
| **0.90** | **53,527** | **8,216** | **29,492** | **48** |
| 0.85 | 77,966 | 8,397 | 35,677 | 54 |
| 0.80 | 106,707 | 7,993 | 42,053 | 77 |
| 0.75 | 141,640 | 7,293 | 48,496 | 127 |
| 0.70 | 177,813 | 6,203 | 52,959 | 372 |

**Primary threshold 0.90**: communities stay tight (largest 48, no chaining
blob) while covering 29,492 declarations. The full sweep is stored in the
summary so the cut can be changed without rerunning discovery.

## 3. Community characterization

For each community we record: size; area/module/kind distributions; internal
edge count, mean and min cosine; number of fuzzy internal edges (endpoints
differ in a discrete 15-B field) and which fields differ; the most common
shared anchors (`H:` conclusion head / `C:` constraint class); the dominant
declaration suffix (when ≥ half the members share it); a representative
(highest summed internal similarity); and up to 40 sample members (full
membership is in the assignment file). Label rule: a dominant shared suffix →
"`<suffix> family`"; else strongest shared anchor; else representative.

Size distribution (8,216 communities): 4,582 pairs, 2,133 of 3–4, 982 of 5–8,
406 of 9–16, 105 of 17–32, 8 of 33+. **606 communities span ≥2 areas**
(the cross-area analogies); 7,610 are within one area.

## 4. Results

### 4.1 The case-study-B family, recovered as communities
The FunLike apply API separates by operation into crisp cross-area communities
at cosine 1.000, exactly matching the formalized `Is*Apply` story:

| id | community | size | areas | anchor |
|---|---|--:|--:|---|
| 22 | `coe_smul family` | 19 | 7 | `C:FunLike, C:SMul` |
| 23 | `smul_apply family` | 19 | 6 | **`C:IsSMulApply`** |
| 81 | `neg_apply family` | 10 | 5 | — |
| 83 | `sub_apply family` | 10 | 5 | — |
| 113 | `coe_neg family` | 8 | 5 | — |
| 114 | `coe_sub family` | 8 | 5 | — |

Members span ContinuousLinearMap, ContinuousMultilinearMap, MultilinearMap,
QuadraticMap, VectorMeasure, OuterMeasure, SchwartzMap, TestFunction,
GroupSeminorm/AddGroupSeminorm, ModularForm, CuspForm, SlashInvariantForm,
UniformConvergenceCLM across Analysis/LinearAlgebra/MeasureTheory/Topology/
NumberTheory/Probability — the same set B formalized, reached unsupervised.

### 4.2 Other cross-area families (new candidates)
* **Pointwise algebraic structure** on containers: paired `Filter`/`Set`/
  `Equiv`/`Finset`/`Ultrafilter` communities for `add/zero/neg/sub`,
  `addMonoid/addCommMonoid/addCommSemigroup/addSemigroup/addZeroClass/…`
  across Algebra ↔ Order ↔ Combinatorics (many at cosine 1.000) — another
  "same construction repeated per carrier" family, distinct from FunLike.
* **Structural** communities: `H:Equivalence` (26 members, **10 areas**),
  `H:GaloisInsertion` (16, 7 areas), `H:AddHom` (26, 4 areas),
  `H:Set.InvOn` (15, 6 areas), `C:BEq/LawfulBEq` (36, 3 areas).
* Same-area "generalization ladders" are captured too, e.g. the
  `HasFDerivAt/HasFDerivAtFilter/HasFDerivWithinAt/HasStrictFDerivAt.isTheta_sub`
  quartet (Analysis), and `Function.Injective/Surjective.<algebra-class>`
  pairs (Algebra).

The summary ranks all 606 cross-area communities by `size × nAreas` (top 30
included) as a prioritized missing-abstraction worklist.

## 5. Outputs (`data/`)

| file | rows | content |
|---|--:|---|
| `analogy_clusters.jsonl` | 8,216 | one community per row (label, size, areas/modules/kinds, internal cosine stats, anchors, suffix, representative, ≤40 sample members) |
| `analogy_cluster_assignment.jsonl` | 29,492 | full node → cluster assignment with area/module/kind/size/crossArea |
| `analogy_cluster_summary.json` | 1 | graph stats, 7-cut sweep, size histogram, top-30 cross-area communities |

## 6. Verification (`verify_clusters.py`, VERIFICATION OK)

Rebuilds the graph and union-find independently and:
* reproduces the **entire threshold sweep** (community count and clustered
  nodes at all 7 cuts);
* reproduces every primary community: size equals the recomputed component,
  stored members belong to it, area counts, cross-area flag, dominant suffix
  and coverage, and the size histogram all match;
* proves the assignment is an exact partition of all 29,492 clustered nodes
  (no missing/duplicate/extra, each points to the correct component);
* confirms every edge ≥ 0.90 lies inside one component.

## 7. Limits / next steps

* Single-linkage components can chain across a weak bridge; the 0.90 cut keeps
  the largest community at 48, but a modularity/density clustering could be
  compared later.
* A handful of communities are labelled by a shared *proof* head
  (`V:ite`, `V:Inhabited.default`) or reference elaborator/pretty-printer
  names; these are proof-shape twins rather than mathematical analogies and
  can be demoted by ignoring `V:`-only labels in a downstream ranking.
* Communities are one-hop similarity structure (no transitive closure beyond
  the similarity edges themselves); naming/proposing a generic abstraction
  for each cross-area community, then kernel-verifying it as in case study B,
  is the next loop stage.
