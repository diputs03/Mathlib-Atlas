# 64 — Semantic-first, two-channel analogy scan over the mature stdlib

Date: 2026-09-22
Script: `script/python/64_stdlib_semantic_analogies.py`
Verifier: `script/python/verify_stdlib_semantic_analogies.py` (ALL CHECKS PASSED)
Helper: `script/python/65_resolve_modules.py`
Data: `data/stdlib_semantic_pairs.jsonl`, `data/stdlib_semantic_clusters.jsonl`,
`data/stdlib_semantic_summary.json`
Log: `notes/64_stdlib_semantic.log`

## 1. Purpose

Generalize script 52's semantic donor matcher from the 1,781 frontier targets to
the **whole mature standard library** (10 core areas), semantic signals leading
with structural graph as reranker, to hunt a **second PointwiseLift-class
missing abstraction**. Standing directive honored: genuinely undiscovered
structure is structurally incomplete, so semantic matching must lead; the
mature stdlib, not the frontier, is the discovery target.

## 2. Why two channels (the key design decision)

The confirmed PointwiseLift result (`Set.image2` ~ `Filter.map₂`) has **no
shared name vocabulary whatsoever** — "image" vs "map", "set" vs "filter"
(measured `meaningCos = 0.000` between the two definitions). Its signal lives
entirely in the type: the two definitions have byte-identical type skeletons
(`nPi=6, nImplicit=3, nDefault=3, typeNodes=23, typeDepth=8, typeConsts=3,
constraints=[]`). A purely semantic blocker literally cannot see it. The scan
therefore runs two channels and unions their evidence:

- **Semantic channel (leads).** Three sparse TF-IDF vectors per node —
  `meaning` (concept words from name + conclusion head + value head), `role`
  (kind / predicate-role P / value-role V), `struct` (constraint-area profile,
  coarse shape buckets, proof-strategy flags). `sim = 0.70·meaningCos +
  0.30·roleCos`; `structCos` is computed but never enters the semantic floor.
  Candidate generation is streaming: each node fans out through its 3 rarest
  anchor-word postings (anchor = meaning word, DF ∈ [2, 600]), intersects on
  the fly, requires ≥2 shared anchors, drops pairs sharing a word rarer than
  DF 50 (same concrete concept family), requires different areas **and
  different namespace roots**, then floors meaningCos ≥ 0.32, sim ≥ 0.45.
- **Structural channel (reranks / corroborates).** Block on an **exact**
  coarse type-shape signature `(kind, P, V, nPi, nImplicit, nDefault,
  nInstImplicit, typeNodes, typeDepth, typeConsts, exact constraint-class
  multiset)` — PointwiseLift matches on every field. Only signatures of
  moderate complexity (`nPi ≥ 4`, `typeNodes ≥ 15`) are tested, which removes
  coincidental collisions of tiny definitions (`Nat.fib ~ Complex.cos`).
  Keep cross-area/cross-namespace pairs with `structCos ≥ 0.80` and
  `roleCos ≥ 0.85`; tag `to_additive` twins.

Pairs from either channel feed one union-find. Semantic cluster edges require
both `sim ≥ 0.55` and `structCos ≥ 0.50`; structural edges require
`0.5·roleCos + 0.5·structCos ≥ 0.825`. A reported cluster must have ≥3
members, ≥2 areas, **and ≥2 namespaces**. Components >90 are flagged diffuse.

Filtering: theorems/definitions/opaques only; instances/classes/generated
recursors/casesOn/quotient/internal names excluded; notation and elaboration
machinery excluded (`_aux_`, `macroRules`, `…Stx`, `termε`/`termπ`-style
syntax decls, auto-generated `congr_simp` lemmas).

## 3. Final full-run funnel (commit bbcd1968, 574,391 declarations)

- Eligible core nodes: **183,271** (10 core areas).
- Semantic: 2,538 anchor words; 9,827,527 candidate visits; 236,116 with ≥2
  anchors; 4,822 same-concept-family dropped; 453,328 same-namespace dropped;
  77,516 below floor; **130,268 kept**.
- Structural: 148,259 exact-shape groups (23,490 too-simple groups skipped);
  2,606 cross-area/namespace pair tests; **1,973 kept** (zero `to_additive`
  twins at definition level).
- Union-find: 23,743 cluster edges (21,770 semantic, 1,973 structural).
- **549 clusters (542 nondiffuse, 7 diffuse); 58,967 pairs emitted.**

Positive control (verifier-enforced): the definitions `Set.image2` and
`Filter.map₂` co-cluster with `structCos = 1.000, roleCos = 1.000,
meaningCos = 0.000`; **30 cross-family lemma pairs co-cluster** (assoc/comm,
bot/empty, sup/union, pure/singleton, map/image, neBot/nonempty, vadd/smul/add/
sub/mul/div, curry, mono…), recovering the entire PointwiseLift lemma family as
~20 micro-components. This validates the structural channel end to end and
proves the semantic channel alone is structurally blind to this abstraction.

## 4. Adjudication against real Mathlib source (read-only greps)

Top pairs/clusters were checked against `external/mathlib4` and classified into
genuine missing-abstraction signal vs already-factored/generated patterns.

### 4.1 NEW FINDING — the "orphan functor" family (unregistered functorial
### constructions)

The structural channel found that the unary pointwise lift
`map : (α → β) → F α → F β` and, in several cases, the binary lift
`map₂/zipWith : (α → β → γ) → F α → F β → F γ`, are hand-written across a
large family of type constructors with **identical type shapes**, but the
typeclass integration (`Functor`/`Applicative`/`Monad`) is patchy. Census from
source:

| Constructor | `map` definition | Functor/Monad registered? |
|---|---|---|
| `Set` | `Set.image` | **yes** — `Functor Set`, `LawfulFunctor Set`, `CommApplicative Set`, `LawfulMonad Set` (Data/Set/Defs.lean:268, Data/Set/Functor.lean) |
| `Multiset` | `Multiset.map` | **yes** — Functor/LawfulFunctor/Monad (Data/Multiset/Functor.lean) |
| `Filter` | `Filter.map` | `Functor Filter` global (Order/Filter/Defs.lean:483); `Monad Filter` only as `protected def monad`, made `local instance` per file (Order/Filter/Map.lean:193) |
| `Ultrafilter` | `Ultrafilter.map` | **yes** — Functor + Monad + LawfulMonad |
| `Part` | `Part.bind` | **yes** — Monad Part |
| `Trunc` | `Trunc.map` | **yes** — Monad/LawfulMonad Trunc (Data/Quot.lean:519) |
| `Erased` | `Erased.map` | **yes** — Monad Erased |
| `Stream'.Seq` / `Seq1` / `WSeq` | `Seq.map` etc. | **yes** — Functor Seq, Monad Seq1, Monad WSeq |
| `Computation` | `Computation.map` | **yes** — Monad + LawfulMonad |
| `WithOne`/`WithZero` | `WithOne.map` | **yes** — Monad via `inferInstanceAs (Monad Option)`, `@[to_additive]` (Algebra/Group/WithOne/Defs.lean:58) |
| **`Sym2`** | `Sym2.map := Quot.map (Prod.map f f) …` | **NO** — yet `map_id`, `map_comp` are already proved and the docstring says "The functor `Sym2` is functorial" (Data/Sym/Sym2.lean) |
| **`WithBot`/`WithTop`** | `map := Option.map`, `map₂ := Option.map₂` | **NO** — yet `map_id`, `map_map`, `map_comp_map` are proved (Order/WithBot.lean:142–154); types are `def … := Option α` (Order/TypeTags.lean:22) |
| **`OnePoint`** | `map := Option.map` | **NO** — yet `map_id`, `map_comp` are proved (Topology/Compactification/OnePoint/Basic.lean:178–182) |
| **`Stream'`** | `map f s n := f (get s n)` | **NO** — yet `map_id`, `map_map` are proved (Data/Stream/Init.lean:156–160) |
| **`Cycle`** | `map := Quotient.map' (List.map f) …` | **NO** — only `map_nil/map_coe/map_eq_nil`; the id/comp laws are not even proved |
| **`Filter.Germ`** | `Germ.map` and `Germ.map₂` | **NO** (Order/Filter/Germ/Basic.lean:192,209) |
| `CompactCoherentification.map`, `SummationFilter.map` | hand-written | **no** — correctly: these require extra hypotheses / are subtype-restricted pushforwards, not plain functors |

The binary lift family is correspondingly larger than PointwiseLift:
`Set.image2`, `Filter.map₂`, `Filter.Germ.map₂`, `WithBot.map₂`,
`WithTop.map₂`, `WithOne.map₂`, `WithZero.map₂` (all `Option.map₂`),
`Stream'.WSeq.zipWith`. Of these, Set and WSeq have Applicative/Monad
instances; WithOne/WithZero have Monad; **Filter (global), WithBot, WithTop,
Germ have the binary lift but no Applicative instance**.

Interpretation. This is a **single, coherent, actionable consistency gap**
discovered exactly the way PointwiseLift was: quotient/newtype type
constructors that are mathematically functorial carry hand-written lifts and
often the already-proved functor laws, but were never registered as
`Functor`/`Applicative` (Sym2 even documents its own functoriality in prose).
It is weaker than PointwiseLift in one respect — the abstraction
(`Functor`/`Applicative`) already exists and 12+ sibling constructions use it;
the gap is integration/omission rather than a missing concept. It is stronger
in another: the result is directly PR-shaped (register the instances; for
Cycle prove the two laws first), and every claim above is source-verified.
Possible reasons for omission that must be checked before a PR (not assumed
away): instance-search/diamond costs, deliberate avoidance of monad notation
in order-theoretic files, and continuity being a separate concern for
OnePoint. None of these applies to plain data-level `Functor Sym2`/`Cycle`/
`Stream'`, which are the strongest candidates.

### 4.2 Secondary repetition families (already-handled patterns, classified)

- **Bundled-hom API duplication** (the largest structural clusters, score
  1.000): `zero_apply/add_apply/smul_apply/sub_apply/coe_zero/coe_smul`
  repeated across Seminorm, GroupSeminorm, MultilinearMap, QuadraticMap,
  ContinuousLinearMap, ContinuousMultilinearMap, SchwartzMap, TestFunction,
  UniformConvergenceCLM (M≈7–12 each); `Hom.ext/Hom.ext_iff/hom_comp/hom_ext`
  repeated across MagmaCat/AddMagmaCat, SemiNormedGrp, HeytAlg, Lat, Preord,
  TopCat (M≈7–8); `mk.inj` across 34 bundled concrete categories;
  `coeFnAddMonoidHom/coeHom` across 7 bundled map types. Root cause: the
  unifying machinery (`FunLike`/`ConcreteCategory`/`BundledHom`) lives in
  CategoryTheory/Tactic areas and is not propagated as generic lemmas into
  these core bundled types. This is propagation debt, not a missing concept.
- **Subobject `.pi`**: `Submonoid.pi`, `AddSubmonoid.pi`, `Sublattice.pi`,
  `Ideal.pi`, `AddCon.pi`, `Con.pi` — the same pointwise subobject
  construction re-derived per bundled set type; no generic `SetLike.pi`.
- **Cross-module re-exports** (top semantic pairs, m≈0.97–1.00):
  `TensorProduct.lidOfCompatibleSMul_tmul` vs
  `Algebra.TensorProduct.lidOfCompatibleSMul_tmul`; `LinearMap.*` vs
  `ContinuousLinearMap.*` (map_smul_of_tower, intrinsicStar_*,
  IsIdempotentElem.*); `AffineEquiv`/`AffineIsometryEquiv`/
  `ContinuousAffineEquiv` pointReflection lemmas; `iterateFrobenius` vs
  `iterateFrobeniusEquiv`; `DirectedSystem` vs `Module.DirectedSystem`.
  Same-theory API propagation split across area buckets.
- **to_additive / opposite triples**: OreLocalization/AddOreLocalization,
  MulOpposite/AddOpposite/Opposite, FreeMonoid/FreeAddMonoid/List — systematic
  generated duplication, correctly handled by `to_additive`.
- **Pointed newtype family**: WithOne/WithZero/WithBot/WithTop/OnePoint/Option
  share `coe_injective`/`map_coe`; semantically clustered but correctly
  distinct constructions (different instance lattices).
- **Area-bucket artifacts**: Filter/Tendsto lemmas physically split between
  Order and Topology files; Matrix PosSemidef between LinearAlgebra and
  Analysis — one theory, two area labels.

### 4.3 The semantic-channel null result

Across 183k mature nodes, the semantic-led channel produced **no
semantic-only missing-abstraction candidate** that survives source
adjudication: every high-scoring semantic cluster is a re-export, a
bundled-hierarchy propagation, a generated twin, or a bucket artifact. The one
genuine abstraction family (pointwise/functorial lifts) is **invisible to
meaning vocabulary** (`meaningCos = 0`) and was recovered by exact type-shape
blocking. This nuances the standing hypothesis: semantic vocabulary diverges
*precisely when* a construction is independently re-derived under a different
name (image vs map), so for the mature, already-named stdlib the structural
channel carries the missing-abstraction signal, while the semantic channel
excels at mapping propagation debt and re-export families (and remains the
expected leader for under-developed frontier corpora, per script 52).

## 5. Method notes / pitfalls fixed during development

- Full-corpus DF bands must be wider than smoke-test bands: cap 120 admitted
  only 2,019 anchor words at full scale (mid-level vocabulary has DF in the
  hundreds); cap 600 + 3 rarest anchors gives 2,538 anchors and 236k ≥2-anchor
  candidates while staying tractable (9.8M visits, ~30 s).
- Log-bucketed structural blocking merged unrelated tiny defs into a 5.5k-node
  blob; **exact** type signatures plus a complexity floor fixed it.
- The positive-control stem must use the Unicode subscript `Filter.map₂`.
- Notation/elaboration boilerplate (`macroRules` auxiliaries, `termπ`/`termφ`
  — note Greek lowercase passes Python `islower`, so the filter tests ASCII
  `a–z` — and `congr_simp` generated lemmas) must be excluded explicitly.
- Structural cluster edges still require `structCos ≥ 0.50` corroboration;
  without it semantic chains form diffuse blobs.
- Pure stdlib Python (no numpy); streaming candidate generation, no global
  pair table; deterministic.

## 6. Deliverables and next steps

Closed loop: full run exit 0; verifier exit 0; this note; `[64]` execution
entry; memo section.

Candidates for follow-up (not yet done):
1. **Orphan-functor PR scoping** (highest-value): attempt `Functor Sym2`,
   `Functor Cycle` (+ prove `map_id`/`map_comp`), `Functor Stream'`,
   `Functor WithBot/WithTop`, `Functor OnePoint` in a downstream (non-Mathlib)
   Lean experiment first, to surface any diamond/instance blockers; only then
   decide which are genuine omissions vs deliberate.
2. Re-run with a value-shape-free structural distance (type-only) to measure
   orphan-family recall precisely.
3. Promote the structural channel's orphan-map detector into a named-family
   watchlist report (unary `map`, binary `map₂/zipWith`, `bind`, `pure`) with
   instance-presence flags, for longitudinal tracking across Mathlib versions.
4. Semantic channel: enrich meaning tokens from type-skeleton class
   constraints (currently only the struct vector uses them) and re-test on
   frontier areas where semantic leadership is expected.
