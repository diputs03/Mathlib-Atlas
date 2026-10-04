# Mathlib Atlas — Analogy Discovery Track (scripts 16–33), consolidated memo

This memo consolidates the complete "find a missing abstraction" sweep over the
Mathlib corpus. Two complementary methods were run end-to-end, every candidate
family was triaged, and every positive-looking family was either grounded in
Mathlib source or kernel-checked by a Lean probe. All counts below are taken
from the delivered `data/*_summary.json` files; all Lean probes compile with
exit 0, no warnings, no `sorry`; every Python stage has an independent verifier
printing `VERIFICATION OK`.

**Headline result.** Across ~300k embedded declarations and two independent
search methods, exactly **one** genuinely missing abstraction was found and
kernel-constructed: **case E, `PointwiseLift`** (scripts 23–25). Every other
analogy is an abstraction Mathlib already has, a strength/arity or local/global
variant, a notation/naming twin, a categorical dual, or role-only noise.

---

## 1. Corpus baseline (scripts 01–15)

- 574,391 Mathlib declarations across 8,287 modules / 32 top-level areas.
- 16,316,230 distinct reference edges; 357,553 human-authored, 216,838 generated;
  1,991 classes, 33,215 instances, 27,185 rfl-closed, 26,908 value-truncated.
- Largest areas: Algebra 101,414; CategoryTheory 77,929; Analysis 51,069;
  Topology 48,514; Data 44,751.
- Provenance always taken from the environment (`getModuleIdxFor?`), never from
  name prefixes.

## 2. Method

Two methods, deliberately different in what they can see:

- **Structural (17–27): TF-IDF over declaration shape.** Tokenize type/value
  structure, embed, cluster by cosine, then read cross-area clusters. It finds
  analogies that share a visible structural signature.
- **Semantic/role (28–33): role vector with identity stripped.** Vectorize only
  kind, conclusion predicate-role, proof-strategy-role, constraint-area profile,
  and concept words; block on role signature + one shared conclusion word. It
  finds analogies whose *mathematical job* matches even when the structural head
  differs — essential because **an as-yet-undiscovered abstraction has an
  incomplete structural signature** (the standing methodological directive).

Every candidate then goes through the same closed loop:
mechanical triage → source grounding → Lean kernel probe → verifier → note.

---

## 3. Structural sweep (16–27)

### Funnel (authoritative counts)

| stage | number | source |
|---|---:|---|
| declarations embedded (theorem/definition/opaque, non-generated) | 298,701 | embedding_summary |
| vocabulary / strong terms / anchor terms | 66,676 / 59,671 / 8,982 | embedding_summary |
| kept cosine pairs (≥0.70) | 265,371 | embedding_summary |
| — cross-area pairs | 32,366 | embedding_summary |
| union-find clusters (threshold 0.90) | 8,216 | analogy_cluster_summary |
| — cross-area clusters | **606** | analogy_cluster_summary |

### Triage of the 606 cross-area clusters (community_triage_summary)

| status | count | disposition |
|---|---:|---|
| shared_head_analogy | 348 | split in script 21 → mixed 244 / head_api 85 / repeated_proof 19; all reuse an existing head API |
| generic_api_exists | 144 | a generic class/lemma already exists (case B is the prototype) |
| structure_lifted_per_carrier | 29 | already lifted per carrier (case C family) |
| weak | 66 | script 27 → generic_reuse 49 / mechanical_shape 15 / unrelated 2; **0 opportunities** |
| pointwise_repeated | 11 | script 26 → shared_generic_core 6 / generic_type_construction 3 / shared_strategy_only 2; **0 opportunities** |
| infra | 8 | infrastructure/metaprogramming, not mathematics |

### Cases examined kernel-side

- **Case B (16) — FunLike / Is*Apply.** Generic `FunLike` (and friends) already
  exist; fixed one straggler (`NormedAddGroupHom`). Already abstracted.
- **Case C (20) — pointwise binary lift.** `Set.image2` / `Filter.map₂` /
  Finset constructions share a shape; led directly to case E.
- **Case D (22) — Equivalence witnesses.** The widest community, `Equivalence`
  (26 witnesses across 10 areas), is the trivial bundle
  `Equivalence.mk refl symm trans` repeated — irreducible multiplicity, not a
  missing abstraction.
- **Case E (23–25) — `PointwiseLift` — THE POSITIVE.** A binary operation on a
  carrier lifts pointwise to a container:
  - `23`: class `PointwiseLift T {lift2, liftAssoc}` with generic
    `PointwiseLift.semigroup/commSemigroup` written once; realized for
    `Set.image2` and `Filter.map₂`.
  - `24`: subclass `PointwiseLiftOne {pure, liftLeftId, …}` gives the monoid
    ladder; the DivInvMonoid ladder lifts the same way.
  - `25` (boundary): **`Group` does NOT lift** — `inv_mul_cancel` is a diagonal
    law that fails pointwise; an empty-set counterexample was kernel-checked.
    The construction is valid exactly through `DivInvMonoid`.

---

## 4. Semantic/role sweep (28–33)

### Funnel (authoritative counts)

| stage | number | source |
|---|---:|---|
| scanned / embedded theorems | 574,391 / 285,823 | semantic_summary |
| role vocabulary / word-anchored blocks | 5,018 / 33,341 | semantic_summary |
| block pairs scored (0 oversized blocks skipped) | 20,068,370 | semantic_summary |
| hidden candidates at cosine ≥ 0.80 | **627** | semantic_summary |

### Ledger of the 627 (semantic_ledger_summary; 0 unresolved)

| family | count | disposition (kernel probe) |
|---|---:|---|
| F_locus — global/on-set/at-point/within/AE/eventually | 365 | **case F (29):** one generic `Filter.Eventually`; order predicates need the α×α product filter; AE/QMP are quotient/measure-level |
| G_smooth — real vs manifold differentiability | 126 | **case G (30):** manifold notion is the generic; iff/equality bridges exist at every level |
| strength_arity — strict/local/arity/point-global | 57 | one definition + stronger hypothesis or extra argument |
| cat_dual — Limit/Colimit, Exact, Left/Right, Epi/Mono, Injective/Surjective | 54 | standard categorical dual/exactness vocabulary |
| add_mul_twin | 13 | one declaration duplicated by `to_additive` |
| num_domain | 8 | same predicate over Nat/Int/Rat/NNRat carriers |
| bundled_concept | 4 | `Is…` predicate vs `…Category` bundled class / naming |
| **unresolved** | **0** | — |

### Weak band [0.70, 0.80) (script 32; verify_weak_band VERIFICATION OK)

Re-ran at threshold 0.70: 1,809 loose − 627 tight = **1,182 weak-band pairs**.
After two classification stages only **71** rows are irreducible
(`semantic_weak_band_residual.jsonl`); read by hand, they are local/filter
reformulations, Archimedean/Lp/order-dual variants, and role-only coincidences —
no coherent novel analogy.

- **Candidate case H — "independence" cluster (11 pairs), probe 33: NEGATIVE.**
  `LinearIndependent` and `AlgebraicIndependent` are both `rfl`-equal to
  `Function.Injective` of the structure map; algebraic independence is linear
  independence of the free monomial basis (`basisMonomials`, `aevalEquiv`);
  `AffineIndependent 𝕜 p ↔ LinearIndependent 𝕜 (p i -ᵥ p i₀)`; `sSupIndep` is
  already generic over any `CompleteLattice`; the combinatorial generic
  `Matroid.Indep` exists; `ConvexIndependent` obeys the opposite anti-exchange
  law (convex geometry, not a matroid), so a single unified class would be
  mathematically false.

---

## 5. Master disposition table

| candidate family | method | verdict | where |
|---|---|---|---|
| FunLike / Is*Apply | structural | already abstracted | 16 |
| pointwise binary lift | structural | **NEW: PointwiseLift** | 20, 23–25 |
| Equivalence.mk bundles | structural | irreducible repetition | 22 |
| 348 shared-head communities | structural | existing head API | 21 |
| 66 weak / 11 pointwise-repeated | structural | 0 opportunities | 26, 27 |
| filter-relative predicates | semantic | already `Filter.Eventually` | 29 |
| real/manifold smoothness | semantic | already abstracted (charts) | 30 |
| strength/arity, dual, add/mul, numeric, bundled | semantic | variants of one definition | 31 |
| weak band 1,182 + independence | semantic | 0 new; case H false | 32, 33 |

## 6. Conclusions

1. **Yield is deliberately rare and that is the correct outcome.** A mature
   library like Mathlib has already harvested most repeated shapes; a sweep that
   produced many "new abstractions" would be producing false positives. The
   funnel (hundreds of thousands of embeddings → tens of thousands of cross-area
   pairs → 606 structural + 627 semantic candidates → one positive) is the
   expected shape of a high-precision discovery process.
2. **The two methods are complementary and both necessary.** Structural matching
   surfaced case E (a visibly repeated lift); semantic matching reached
   structurally-incomplete analogies (cases F/G/H) that head-matching discards —
   confirming the directive — but those turned out to be already-unified, which is
   itself informative.
3. **Cutoff validation.** Below cosine ≈0.80 the semantic signal is dominated by
   proof-role coincidence (the 71-row noise tail), so 0.80 is the right operating
   point.
4. **The kernel is the final judge.** Every "this looks like a missing class"
   hypothesis was decided by a compiling Lean probe, including the precise
   boundary of the one positive (Group fails to lift; convex independence is not
   a matroid).

## 7. Reproduction index

- Structural: `17_embeddings.py` → `18_*cluster*` → `19_*triage*` →
  20/22/23/24/25 Lean probes → `21/26/27` triages; verifiers alongside.
- Semantic: `28_semantic_analogy.py` (env: `ATLAS_SEM_THRESH`, `ATLAS_OUT_TAG`) →
  29/30/33 Lean probes → `31_semantic_ledger.py` → `32_weak_band_scan.py`;
  verifiers `verify_semantic.py`, `verify_semantic_ledger.py`,
  `verify_weak_band.py` (all VERIFICATION OK).
- Design/case notes: `notes/16_…`, `20_…`, `22_…`, `23/24/25_…`,
  `28_semantic_design.md`, `29_filter_relative_case.md`,
  `30_smoothness_manifold_case.md`, `31_semantic_ledger_design.md`,
  `32_weak_band_design.md`; running log `notes/execution.txt`.

## 8. Parked (await direction)

- 07 full-proof-term persistence (~70+ GB) — intentionally left.
- Production integration of `PointwiseLift` into Mathlib (`external/mathlib4`
  stays read-only).
- Plan items 10 (typeclass/instance structure), 11 (namespace/theory),
  12 (theorem-generalization links).
