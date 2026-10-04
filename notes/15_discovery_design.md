# 15 — Discovery experiments

Script 15 closes the Atlas loop described at the project's outset: it treats the
formalized corpus as data and surfaces **candidate mathematical patterns** —
repeated constructions, cross-area analogies, generalization families, bridge
declarations and structural anomalies — for a human/AI to turn into hypotheses
that Lean would then formalize and the kernel verify. Nothing here is asserted
as a theorem; every output is a ranked, reproducible structural hypothesis.

* Engine:    `script/python/15_discovery.py` (pure Python, deterministic)
* Verifier:  `script/python/verify_discovery.py`
* Report:    `notes/15_discovery_report.md` (top candidates)

## Inputs (all produced upstream)

13 features (intrinsic type/value shape, `isGenerated`, truncation flags),
09 type skeletons (binder counts and **typeclass-constraint multiset**),
14 node graph stats (degrees), and a single streamed pass of the 09 reference
edges for area-reach masks. Joined node set: **574,391** Mathlib declarations.

### The generated-declaration filter (essential)

A first pass clustered all declarations and the signature space was dominated
by elaborator-generated terms (`_simp_N`, `._proof_N`, `.match_N`,
`Lean.Macro` / `ParserDescr` / `TrailingParserDescr`, `macroRules`
`_aux_…`). The mathematical-construction experiments A/B/C therefore run on
the **357,553 human-authored** declarations after excluding the **216,838**
flagged by 13's `isGenerated` (the count matches 13 exactly). Bridges (E) and
anomalies (D) retain all declarations, since generatedness is itself relevant
there.

## The five experiments

### A — Repeated type signatures → candidate missing abstractions
Signature = (kind, exact binder counts, multiset of typeclass constraints,
conclusion head). Clusters with ≥6 members across ≥3 namespaces are kept;
constraint-bearing / non-`Eq`-`Iff` clusters rank first. **4,738 clusters.**
Examples: the same `Category`-constrained `Quiver.Hom`/`Functor`/`Iso`
construction rebuilt in dozens of category namespaces; `Inhabited`/`DecidableEq`
/`LinearOrder` instance shapes repeated across 5–11 areas.

### B — Cross-area structural twins → candidate analogies
Signature drops names and the conclusion head but keeps arity, the typeclass
constraint multiset, log2-binned type/value size and proof style (rfl, recursor
/`casesOn` use). Groups spanning ≥2 areas and namespaces: **5,557**. The
strongest hits are independently re-implemented API surfaces — e.g. the
`FunLike` evaluation API `zero_apply / add_apply / sub_apply / neg_apply /
smul_apply / coe_zero` repeated across `Seminorm`, `GroupSeminorm`,
`SchwartzMap`, `MultilinearMap`, `QuadraticMap`, `VectorMeasure`, `CuspForm`
in six areas; and the parallel category constructions `AlgCat / BialgCat /
CoalgCat / CommAlgCat / CommBialgCat / CommHopfAlgCat`. These are direct
seeds for a shared abstraction.

### C — Generalization families
Same namespace + conclusion head + constraints with an arity ladder
(≥2 distinct `nPi`): **10,924 families** (e.g. the `Set`/`Nat`/`Real`/
`Complex` equality-lemma ladders), candidates to unify under a more general
statement.

### E — Bridge declarations
A single streamed edge pass builds two 32-bit area masks per declaration (areas
of its dependencies and of its dependents). Declarations whose combined area
reach is ≥8: **16,464**. The top connectors are foundational instances and
coercions — `Nat.instLinearOrder`, `Equiv.instEquivLike`,
`Preorder.toLE`, `SetLike.instMembership`, `DFunLike.coe` — quantifying, at
declaration granularity, the same hierarchy-backbone finding that 14 showed at
module/area level.

### D — Anomalies
Categories with defining predicates: **107** reduction-heavy rfl proofs and
**26,801** other terms whose value walk hit the 50,000-node cap (together
26,908 = 13's value-truncation count exactly), **46** recursion-heavy terms
(recRefs+caseRefs ≥ 200), and the top 200 human theorem hubs by distinct
dependents (led by `RingHomInvPair.ids`, `smulCommClass_self`,
`CategoryTheory.Category.assoc`). Files cap each category at 200 rows.

## Outputs (`data/discovery_*.jsonl`)

| file | rows | content |
|---|---|---|
| `discovery_type_clusters.jsonl` | 4,738 | A: signature, size, namespace/area spread, exemplars |
| `discovery_cross_area_twins.jsonl` | 5,557 | B: shape signature, areas, per-area exemplars |
| `discovery_generalization_families.jsonl` | 10,924 | C: family key, arity set, members |
| `discovery_bridge_declarations.jsonl` | 16,464 | E: area masks/reach + degrees |
| `discovery_anomalies.jsonl` | 553 | D: capped top anomalies by category |

## Verification

`verify_discovery.py` rebuilds the A/B signature functions independently from
13+09 and proves **every stored exemplar re-derives its claimed cluster
signature**; checks all thresholds and spreads, that bridge `areaReach =
outAreaCount + inAreaCount` and mask lists match, and that each anomaly
satisfies its defining predicate; and cross-checks the generated count and the
value-truncation split against 13. Result: **VERIFICATION OK**.

## Caveats and next steps

* Signatures are intentionally coarse and syntax-structural (no definitional
  equality or semantic embedding); clusters are candidates to *read*, not
  proven duplicates. Exact size/arity matching is loosened for B by log bins.
* "Area" remains a module-name grouping, not an inferred theory.
* Natural follow-ups: fuzzy/embedding similarity over type skeletons for
  analogies the discrete signatures miss; community detection on the 14 graph;
  and promoting a B twin group (e.g. the `FunLike` evaluation API) into a
  concrete proposed abstraction to formalize and verify — the Atlas loop's
  hypothesis→formalization→kernel step.

## Reproduce

```
python script\python\15_discovery.py
python script\python\verify_discovery.py
```
