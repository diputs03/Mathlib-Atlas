# 17 — Embedding / fuzzy similarity over type skeletons and features

**Status: run + independently verified (VERIFICATION OK).**
Script `script/python/17_embeddings.py`; verifier
`script/python/verify_embeddings.py`; logs `notes/17_embeddings.log`,
`notes/17_verify.log`. Pure Python (numpy is not installed), deterministic.

## 1. Why

Script 15-B groups declarations only when their **discrete** signature matches
exactly (conclusion head + multiset of constraint classes + binder counts).
That misses *near* analogues that differ in one constraint or a binder yet have
the same mathematical shape. Script 17 adds a soft TF-IDF embedding so such
fuzzy analogies — especially cross-area ones — are recovered, and records
precisely which discrete fields differ.

## 2. Population

From the 574,391 Mathlib declarations (script 13 features joined to script 09
type skeletons by name), keep **human-authored mathematical statements**:

* kind ∈ {theorem, definition, opaque}; exclude `isGenerated`, `isInstance`,
  `isClass`;
* exclude non-mathematical areas `Tactic` / `Lean` / `(root)`, `_private.*`
  names, `.Meta.` modules, and auto congruence lemmas `<f>.hcongr_N`.

Result: **298,701 embedded declarations**, vocabulary **66,676** tokens.

## 3. Token model (domain-agnostic by construction)

Module, namespace and declaration name are **never** vector tokens (metadata
only), so a declaration in one area can be nearest neighbour to another area.
Each document carries:

* kind;
* **conclusion head** — full token `H:<head>` and its name segments;
* **type-class constraints** — full `C:<class>` + segments, repeated by
  multiplicity (capped);
* **value head** `V:<head>` when a trustworthy, non-truncated value exists;
* **structural shape**, log2-bucketed: number of Pi / implicit / strict /
  inst-implicit / default binders, number of constraints, and type node count /
  depth / distinct-constant count. Bucketing makes size a soft signal.

Weighting: sublinear tf (capped at 4) × idf `ln((N+1)/(df+1))+1`; vectors are
L2-normalised (CSR-compact `array` storage).

## 4. Scalable nearest neighbours (no all-pairs, no numpy)

* **Anchor** terms = full conclusion head `H` and full constraint class `C`.
  A pair is a candidate only if it shares an anchor with `2 ≤ df ≤ 80`
  (inverted index; 5,365 generating anchors). Value head and shape/segment
  tokens re-rank but never alone propose a pair, so two unrelated theorems that
  merely share a proof tactic cannot match.
* Candidate generation accumulates the anchor-weight dot product
  (**988,877** candidates).
* An idf upper bound prunes hopeless pairs; survivors get the **exact** cosine
  over the full vector (two-pointer CSR intersection; the non-generating
  complement includes value head, segments, shape and out-of-band anchors).
* Keep cosine ≥ **0.70**; retain top **8** neighbours per declaration.

## 5. Outputs (`data/`)

| file | rows | content |
|---|--:|---|
| `embedding_nearest_neighbors.jsonl` | 52,959 | top-8 neighbours per declaration, with cosine, differing discrete fields, shared anchors |
| `embedding_cross_area_analogies.jsonl` | 32,366 | cross-area pairs, fuzzy-first then cosine desc (cap 40,000) |
| `embedding_summary.json` | 1 | parameters, vocab, candidate/kept counts, top area-pairs |

Totals: **265,371** kept pairs, of which **235,857 are fuzzy** (differ in ≥1
discrete field — i.e. invisible to exact 15-B) and 29,514 exact-already;
**32,366 cross-area**, 233,005 same-area. Most common fuzzy differences are
constraint-list and binder-count variations — exactly the near-misses intended.

## 6. Convergence with case study B

The embeddings independently re-cluster the B apply-API family across areas at
cosine 1.000, e.g. `UniformConvergenceCLM.sub_apply` ↔
`MultilinearMap.sub_apply` / `VectorMeasure.sub_apply` / `SchwartzMap.sub_apply`
/ `QuadraticMap.sub_apply` / `ModularForm.sub_apply` / `CuspForm.sub_apply`
across Topology, LinearAlgebra, MeasureTheory, Analysis and NumberTheory —
even though their discrete constraint lists differ. The soft and exact methods
thus corroborate each other on a known family, while the soft method adds
near-miss reach.

Other genuinely novel cross-area analogies recovered (differ in discrete
fields): the "pi fan / limit fan" construction across `CommRingCat`, `TopCat`,
`ωCPO` and `Grpd`; `Filter.giGenerate` ↔ `MeasurableSpace.giGenerateFrom`;
the homology functors of `CategoryTheory.Abelian` ↔ `ShortComplex`.

## 7. Verification (`verify_embeddings.py`, VERIFICATION OK)

Rebuilds the entire token/df/idf/norm model independently and:

* reconciles scanned/embedded/vocab counts with the summary;
* re-derives the cosine of **all 32,366** cross-area pairs by direct two-pointer
  intersection — matches stored value within 1e-4, all ≥ threshold, area labels
  and `diffFields` recomputed and equal, all genuinely cross-area;
* samples 52,959 NN rows (7,851 re-derived edges): cosine, threshold, ordering
  (≤ topK, sorted desc) and diffFields all correct;
* confirms the cross-area file is ordered fuzzy-first;
* NN row count equals `docsWithNeighbor`.

## 8. Limits / next steps

* Recall is deliberately bounded by the anchor df-cap (≤80): a pattern shared by
  thousands of declarations is treated as background and is not a candidate;
  raise the cap to study ubiquitous patterns at higher compute cost.
* This is structural/lexical similarity, not a neural semantic embedding; it
  cannot yet see that two *different* head names play the same role. A later
  pass could learn embeddings of head/constraint tokens from the 08/09 graph.
* Outputs are one-hop similarity only (consistent with the project's
  no-transitive-closure rule); clustering/community detection over these edges
  is a downstream experiment.
