# 52 — Semantic donor-transfer map for incompletely-formalized frontier material

Status: **DONE — `python script/python/52_frontier_semantic_donors.py` and the
independent `verify_frontier_semantic_donors.py` both run clean; verifier prints
VERIFICATION OK** (it rebuilds document-frequency in its own corpus pass with a
re-implemented tokenizer and recomputes the meaning cosine for 39 sampled pairs
from the raw feature rows).

## Why a new matcher (part (b))

Script 28's semantic track hunts hidden abstractions between two *mature*
theorems: both sides must be theorems with a real conclusion head, the blocking
anchor is a shared conclusion-*head* word, and only structurally *divergent*
pairs survive. That biases toward abstractions which already exist. The user's
point, taken as the design driver: **when a structure is genuinely
undiscovered / incompletely formalized, its structural signature is not
complete, so AST-shape matching under-recalls exactly the interesting cases.**

Script 52 therefore makes the search **asymmetric and meaning-first**:

```
frontier target (thin / near a famous open problem, proof possibly opaque)
        -- semantic nearest neighbour -->  MATURE CORE-AREA donor
```

A mature donor that plays the same mathematical *role* as an under-developed
frontier statement is a **transfer candidate** (machinery/abstraction the
frontier could import or that has been re-derived and could be genericized).

## Method (pure stdlib, deterministic)

- Two TF-IDF channels over the same identity-free vocabulary used by 28:
  - **meaning** — concept words from the declaration name + conclusion head +
    value head (never the concrete constructor identity);
  - **role** — conclusion predicate-role `P`, proof-value role `V`,
    constraint-**area** profile `R`, proof-strategy flags `S`, coarse shape.
- `sim = 0.65·meaningCos + 0.35·roleCos`; the *gate* is meaning (≥2 shared
  meaning words, meaning cosine ≥ 0.30, sim ≥ 0.42). Structural divergence is
  **reported** (`structuralGap`), never required, and a target with an opaque
  value still matches on name + type.
- **Targets** = declarations in the 14 frontier-bucket areas (script 40) that
  either (A) sit in a curated famous-problem / missing-ingredient neighbourhood
  (unit-distance, planar, crossing, incidence, Szemerédi–Trotter, degeneracy,
  graph coloring, Jacobian, Ramsey, Collatz/Hailstone, Navier–Stokes) or (B) are
  "thin" (missing/opaque/truncated value or ≤12 value nodes) in the
  highest-opportunity-pressure frontier areas, capped at 100/area.
- **Donors** = declarations in the 10 mature core areas.
- Tractable without numpy: pass 1 builds global document frequency and the
  targets; pass 2 streams core donors and scores each only against targets
  reached through a **distinctive** shared word (df ≤ 2000 inverted index), so
  glue words (finite/measurable/continuous/…) cannot blow up the fan-out.
- Two noise filters, added after the first run surfaced them:
  - notation/constructor boilerplate (`term_…`, `ctorIdx`, `quot`, `macro`, …)
    is excluded;
  - **same-concept-family** pairs — sharing a *rare* word (df ≤ 400), i.e.
    prime/module variants or the same namespace API — are dropped (17,167 pairs).
    An analogy shares role/mid-level meaning but has a different distinctive
    concept stem.

## Results (pinned corpus, 574,391 decls)

- 287,173 eligible docs; **1,781 frontier targets**; 186,207 core donors;
  **703/1,781 targets (39.5%) have a strong mature donor**; 3,698 donor pairs
  (3,251 with a structural gap).
- **Independent confirmation of the famous-problem footprint (scripts 45–47).**
  Named targets / targets with a mature donor:

  | seed | named | with donor |
  |---|---:|---:|
  | jacobian | 309 | 117 |
  | degeneracy | 125 | 60 |
  | graph_coloring | 134 | 27 |
  | incidence | 107 | 23 |
  | szemeredi_trotter | 68 | 8 |
  | crossing | 41 | 16 |
  | unit_distance | 15 | 12 |
  | **planar** | **0** | **0** |
  | **ramsey** | **0** | **0** |
  | **collatz_hailstone** | **0** | **0** |
  | **navier_stokes** | **0** | **0** |

  A pure semantic/name pass over the whole corpus, with no module anchoring,
  still finds **zero** named planar-graph, Ramsey, Collatz/Hailstone, or
  Navier–Stokes material — the same layer gaps diagnosed by formal matching.
- **Donor flows are mathematically coherent**, and independently re-derive where
  each frontier concept's machinery actually lives:
  - Jacobian ← RingTheory (219) + LinearAlgebra (102): concrete donors
    `MvPolynomial.eval₂_C_mk_eq_zero`, `LinearMap.baseChange_baseChange` —
    consistent with script 45's "the Jacobian hypothesis is exactly
    `Algebra.SubmersivePresentation.jacobian_isUnit`".
  - unit-distance ← Topology (19): `UnitDistEmbedding.mk.sizeOf_spec` mirrors
    `IsometryEquiv.mk` / `ContinuousMap.mk` / `Path.mk` size-of specs
    (role cosine 1.00) — the embedding object is correctly built on the
    isometry/continuous-map layer.
  - graph coloring ← Order/Data: `chromaticNumber_le_of_forall_imp` mirrors the
    `le_of_forall_gt_imp_ne` family; `Coloring.colorClass` mirrors
    **`Set.image2`** — the pointwise-image pattern from the PointwiseLift
    finding reappears independently.
  - degeneracy ← Analysis/Algebra/RingTheory/Order: but the named "degeneracy"
    material is **simplicial** `ExtraDegeneracy` (homotopy theory), not graph
    degeneracy — a clean semantic demonstration of the false friend that made
    47 flag graph degeneracy as an assembly gap (and motivated scripts 48–50).
  - "crossing" donors come from martingale `upperCrossingTime`, not graph
    crossings — the upcrossing false friend again.
- Top transfer candidates are mostly **frontier specializations re-deriving a
  core generic pattern** (e.g. `SSet.ιChainComplex_d` ↔ `ChainComplex.mk_d`;
  `IsOpen.exists_contMDiff_support_eq` ↔ `…contDiff…`;
  `LipschitzWith.norm_compLp_sub_le` ↔ `LipschitzWith.norm_sub_le`). These are
  abstraction-*reuse / genericization* candidates, the semantic analogue of the
  PointwiseLift result, rather than cross-field novelties.

## Interpretation (honest)

- The matcher is a **donor-routing and coverage instrument**, not a conjecture
  generator. Its strongest, most reliable outputs are (1) coverage zeros for
  whole layers, and (2) the precise mature area/decl a frontier concept should
  import from.
- The same-family and boilerplate filters are essential; without them the head
  of the ranking is prime-variant duplicates and notation constructors.
- High word-overlap pairs are usually closely related (specialization vs
  generic), which is expected for a donor map; genuinely *distant* analogies
  share few words and sit below the meaning floor — reaching those needs the
  role-only channel (script 28) or a learned embedding, a later step.

## Verification

- `verify_frontier_semantic_donors.py`: file/count/coverage/TOPK/seed-coverage
  consistency; per-pair invariants (donor core, target frontier, distinct
  areas, ≥2 shared words, floors, `sim = 0.65m+0.35r`, no boilerplate, global
  sort); and an independent full-pass TF-IDF recomputation of meaning cosine for
  39 sampled pairs (tolerance 5e-3). Prints **VERIFICATION OK**.

## Outputs

- `data/frontier_semantic_donors.jsonl` (3,698 ranked donor pairs)
- `data/frontier_semantic_targets.jsonl` (1,781 per-target donor summaries)
- `data/frontier_semantic_summary.json` (counts, seed coverage, donor flows,
  top transfer candidates)
- logs `notes/52_frontier_semantic.log`, `notes/52_verify.log`.
