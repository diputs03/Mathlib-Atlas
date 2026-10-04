# Mathlib Atlas — Discovery & Structure Track (scripts 16–44), consolidated memo

This memo supersedes `discovery_track_16_33.md` and consolidates the full
"find a missing abstraction / map the formal corpus" sweep through script 44.
Every count is taken from a delivered `data/*_summary.json`; every Lean probe
compiles with exit 0, no warnings, no `sorry`; every Python stage has an
independent verifier printing `VERIFICATION OK`.

**Headline.** Across ~300k embedded declarations, two independent analogy
methods, a generalization sweep, the typeclass hierarchy, the namespace layer,
three bridge views, an area-maturity profile and two area-stratified follow-ups,
exactly **one** genuinely new abstraction was found and kernel-constructed —
**`PointwiseLift`** (23–25). The mature stdlib core is almost fully abstracted;
frontier areas repeat more (4.4× shape-group pressure, 42) but that repetition is
concrete fact/instance accumulation on already-generic machinery, not duplicated
abstractable lemmas (42/43). Three independent missing-abstraction detectors
(36/37 named theorems, 42 area-stratified, 43 class-fact derivations) now agree
the corpus is tightly factored.

---

## 1. Corpus baseline (01–15)

- 574,391 Mathlib declarations, 8,287 modules, 32 top-level areas.
- 16,316,230 distinct reference edges; 357,553 human-authored, 216,838 generated;
  27,185 rfl-closed, 26,908 value-truncated.
- Largest areas: Algebra 101,414; CategoryTheory 77,929; Analysis 51,069;
  Topology 48,514; Data 44,751.
- Provenance always from the environment (`getModuleIdxFor?`), never name prefix.

## 2. Two analogy methods (16–33)

- **Structural (17–27):** TF-IDF over type/value shape, cosine clustering.
  298,701 embedded → 265,371 pairs → 8,216 clusters, 606 cross-area.
- **Semantic/role (28–33):** identity-stripped role vectors (kind, conclusion
  role, proof-strategy role, constraint-area profile, concept words).
  285,823 embedded → 20,068,370 block pairs → 627 hidden candidates ≥0.80.
- Weak band [0.70,0.80) = 1,182 pairs → 71 irreducible noise rows; 0.80 is the
  right cutoff.

### Structural triage of the 606
shared_head_analogy 348 (→ mixed 244 / head_api 85 / repeated_proof 19, all reuse
an existing head API); generic_api_exists 144; structure_lifted_per_carrier 29;
weak 66 (0 opportunities); pointwise_repeated 11 (0); infra 8.

### Kernel-decided cases
- **B (16) FunLike/Is*Apply** — generic already exists.
- **C (20) pointwise lift** — led to case E.
- **D (22) Equivalence witnesses** — 26 trivial `Equivalence.mk refl symm trans`,
  irreducible repetition.
- **E (23–25) `PointwiseLift` — THE ONE POSITIVE.** Generic binary pointwise
  lift class with semigroup/comm-semigroup/monoid and DivInvMonoid ladders,
  realized for `Set.image2` and `Filter.map₂`. **Boundary: `Group` does NOT
  lift** (diagonal `inv_mul_cancel`; empty-set counterexample kernel-checked);
  valid exactly through DivInvMonoid.

### Semantic ledger of the 627 (0 unresolved)
F_locus 365 → one generic `Filter.Eventually` (29); G_smooth 126 → manifold is
the generic, bridges at every level (30); strength_arity 57; cat_dual 54;
add_mul_twin 13; num_domain 8; bundled_concept 4.
- **H (33) "independence" cluster — NEGATIVE.** Linear/AlgebraicIndependent are
  both `rfl`-equal to `Function.Injective` of the structure map; affine reduces
  to linear; `sSupIndep` is generic over CompleteLattice; `Matroid.Indep`
  exists; `ConvexIndependent` is anti-exchange (not a matroid), so unification
  would be false.

---

## 3. Structural layers (34–39)

### 34/35 — Typeclass hierarchy & instance gaps (NEGATIVE)
2,300 classes; 557 extend, 274 multiple inheritance, 87 diamonds, max main-line
depth 9. A peer-relative gap detector flagged 54 carriers missing a cross-rung
parent; Lean probe 35 assumed only `[C α]` and built every parent by
`inferInstance` → **all synthesize via structure projection**. The 54 are
redundant-instance *style*, not missing instances; the hierarchy is closed under
cross-rungs by projection.

### 36/37 — Generalization/specialization links (NEGATIVE)
Generic = forall prefix binds a sort-typed type variable. 330,601 theorems →
80,747 shape groups (76,932 pure-generic, 763 covered, 3,052 specialized-only) →
348 raw opportunities → −152 class/prop-fact heads, −191 bare-logical/artifact →
**5 survivors**. The only repeated statement, `*.isZero_of_subsingleton` (6
concrete categories), is not a missing generic: probe 37 shows `IsZero` needs
unique homs in/out while `[Subsingleton X]` only equates elements; each concrete
category bridges via its own `ext`/`map_one`. **0 missing generalizations.**

### 38 — Namespace ≠ module ≠ theory
10,972 root namespaces vs 8,287 modules (100,229 full namespaces); 368 namespaces
span ≥3 areas — most cross-cutting: Function (19), Nat (18), Finset/Equiv/Fin
(17), Set (15). Most-mixed module mixes 95 namespace roots. Area regimes differ:
Algebra 2,252 roots/1,344 modules vs CategoryTheory 115 roots/1,099 modules.
Confirmed `Nat.one_mem_properDivisors…` (ns Nat) lives in
`Mathlib.NumberTheory.Divisors`.

### 39 — Typeclass bridges (instance graph)
33,215 Mathlib instances over 2,002 classes; **532 bridge classes** span ≥3
areas; 452 area pairs share classes. Two archetypes: root plumbing
(`Inhabited` 30/32 areas, 1,030 carriers; `SizeOf` 29) vs mid-hierarchy
workhorses with high reach-per-carrier (`Module` 17 areas/43 carriers,
`Algebra` 14/33). Derived classes have slightly higher mean area spread than
roots (2.99 vs 2.37). Top glued pairs: Algebra–Topology 234,
Algebra–CategoryTheory 222, Algebra–RingTheory 214.

---

## 4. Frontier vs core (40), bridge reconciliation (41), and the two area-stratified follow-ups (42–43)

### 40 — Area abstraction-maturity profile
Per-area proxies (concrete-theorem fraction, instance-constraint density,
rfl-closed share, instance density) combined as a percentile maturity score.
Declared buckets core(10)/frontier(14)/infra(8):

| bucket | generic share | concrete frac | mean constraints | maturity | opportunity |
|---|---|---|---|---|---|
| core | 0.950 | 0.050 | 2.35 | **0.654** | 0.346 |
| frontier | 0.889 | **0.111 (2.2×)** | 1.86 | **0.513** | **0.502** |
| infra | 0.591 | 0.284 | 0.44 | 0.285 | 0.684 (metaprogramming) |

Frontier hunting order: SetTheory 0.79, Dynamics 0.69, Combinatorics/NumberTheory
0.66, Condensed 0.58, Probability 0.57, AlgebraicTopology 0.50. Within-core
exceptions: Data 0.59, Analysis 0.54. (Prioritization heuristic, not a claim;
each candidate still needs a kernel probe.)

### 41 — Combined theory-bridge ranking
Three independent coupling views (R reference edges, N shared namespaces,
I shared classes), each normalized to [0,1] and averaged. 461 area pairs:
**256 robust in all three views**, 107 in two, 98 in one.
- Top combined pairs: Algebra–RingTheory 0.849 (R=1.0,I=0.91), Analysis–Topology
  0.673 (low R=0.12 but N=1.0,I=0.89 — conceptual fusion, not call volume),
  Algebra–Analysis 0.669.
- Mechanism-specific coupling is informative: Algebra–CategoryTheory is almost
  purely a **typeclass** bridge (I=0.95, R=0.26, N=0.15).
- Bridge-area centrality: Algebra 1.000 (universal hub), Topology 0.925, Data
  0.914, Analysis 0.903, RingTheory 0.893; best-connected frontier hubs:
  MeasureTheory 0.753, CategoryTheory 0.742, Geometry 0.699, NumberTheory 0.688.

### 42 — Frontier-stratified generalization scan (NEGATIVE, pressure confirmed)
Same classifier/filters as 36, area-tagged. 330,601 theorems → 635 specialized-only
repeated shape groups; post-filter survivors = **5**, exactly reproducing 36
(built-in consistency). Missing-generalization **pressure** (specialized-only
groups / 1k theorems): core 1.06 vs **frontier 4.69 (4.4×)**; hottest Condensed
27.7, AlgebraicGeometry 25.3 (125 groups), NumberTheory 9.2, SetTheory 8.0,
AlgebraicTopology 7.3 — an independent confirmation of 40. But the rejection
breakdown shows frontier extra repetition is 50.3% per-carrier class/prop-fact
heads + 27.5% bare logical heads; the named-operator candidate *share* is lower
in frontier (0.7%) than core (1.0%). So frontier immaturity is concrete
fact/instance accumulation, not a stock of duplicated abstractable named lemmas.

### 43 — Class-fact derivation detector (NEGATIVE, detector inverts)
The "different detector" 42 called for, distinct from 35's projection check.
47,342 theorems whose conclusion head IS a class/prop → 211 specialized-only
groups → **39 shared-strategy candidates** (core 27 / frontier 11 / infra 1),
where ≥60% of members use one common proof-strategy head. Every candidate is
already factored: **20 ownConstructor** (the class's own `.mk` = irreducible
per-carrier record assembly) and **19 reusesGeneric** (the shared head is an
existing carrier-agnostic lemma/instance — `NeZero.of_gt'`,
`NormedSpace.toIsBoundedSMul`, `normal_of_isAddCommutative`,
`Nat.instAtLeastTwoHAddOfNat` over 152 carriers). **0 genuine gaps.** Structural
reason (no Lean probe needed): an identical constant closing the goal over
*distinct* carriers is necessarily polymorphic, i.e. it IS the generic being
reused; a carrier-specific proof would have a different head per carrier and
could never dominate. With 35 (projection cross-rungs) this closes class-level
derivation gaps from both directions.

### 44 — Frontier-restricted analogy map (NEGATIVE, donor map)
Reuses 17/28 pair artifacts (no re-embedding). Frontier-involved cross-area
pairs: frontier↔core 1,791 / frontier↔frontier 392 / frontier↔infra 230; the
shortlist keeps frontier↔core **different-head** groups → **73** (structural 17,
semantic 56). Auto-triage: 17 wrapperVariant (Eq/Iff/Mono/Epi around one
construction), 56 sharedHeadFamily (manifold `M`-prefix/locality `ContMDiff`↔
`ContDiff` = case G, `Filter.Eventually*` = case F, `PreservesHomology`,
`SplitEpiCategory`↔`IsSplitEpi`, `Injective`↔`Injective2`), **unresolved 0**.
Unlike `PointwiseLift` (two constructions with no shared generic), every pair
already shares its unifying generic as a constraint class or head family.
Descriptive donor map: Geometry is overwhelmingly structured by Analysis (104
pairs), MeasureTheory by Analysis (26)/Order (19); the thin columns
(Dynamics/Combinatorics, one analog link each) are where a future hunt has
headroom.

---

## 5. Master disposition table

| family / layer | method | verdict | scripts |
|---|---|---|---|
| FunLike / Is*Apply | structural | already abstracted | 16 |
| pointwise binary lift | structural | **NEW: PointwiseLift** (Group fails) | 20,23–25 |
| Equivalence.mk bundles | structural | irreducible repetition | 22 |
| 348 shared-head / weak / pointwise | structural | existing API, 0 opportunities | 21,26,27 |
| filter loci / smoothness / duals / numeric / independence | semantic | already unified or false unification | 29–33 |
| typeclass cross-rung gaps | hierarchy | all synthesize by projection | 34,35 |
| theorem generalization families | generic/specialized | 0 missing generics | 36,37 |
| namespace/theory layering | provenance | quantified mismatch, 368 cross-cutting | 38 |
| instance graph bridges | typeclasses | 532 bridge classes, two archetypes | 39 |
| area maturity | profile | frontier less abstracted (2.2× concrete) | 40 |
| three bridge views | reconciliation | 256 robust pairs, Algebra hub | 41 |
| frontier generalization pressure | area-stratified | 4.4× pressure, but concrete growth; 0 gaps | 42 |
| class-fact derivations | shared-strategy | 39 candidates all own-.mk/reuse-generic; 0 gaps | 43 |
| frontier analogy map | reused pairs, different-head | 73 groups all wrapper/shared-family; 0 gaps | 44 |

## 6. Conclusions

1. **High-precision yield is the correct shape.** Hundreds of thousands of
   embeddings and six structural lenses produce exactly one new abstraction; a
   sweep yielding many "new abstractions" would be manufacturing false positives.
2. **Negative results are load-bearing and kernel-decided.** Every candidate was
   decided by a compiling Lean probe, including the precise boundary of the one
   positive (Group fails to lift; convex independence is not a matroid;
   Subsingleton cannot imply categorical IsZero).
3. **Structural and semantic methods are both necessary** — undiscovered
   abstractions have incomplete structural signatures, so role matching reaches
   what head-matching cannot; in the mature core those turned out unified, which
   is itself a result.
4. **Maturity is spatially uneven — but the frontier gap is concrete growth, not
   duplicated lemmas.** Frontier areas carry 2.2× the concrete-statement rate
   (40) and 4.4× the repeated-shape pressure (42), so they remain the right place
   to watch; however 42/43 show that backlog is per-carrier facts/instances built
   on already-generic machinery, with 0 missing named lemmas or class-fact
   derivations. The next frontier lens should therefore be *analogy* (semantic /
   structural cross-area matching), not another missing-lemma detector.
5. **Four independent missing-abstraction detectors now agree the corpus is
   tightly factored** — named-theorem generalization (36/37, 0), area-stratified
   (42, 0), class-fact derivations (43, 0), frontier different-head analogy
   (44, 0). This convergence is itself strong evidence that the one positive
   (`PointwiseLift`) is not a false negative of a permissive filter.
6. **Keep the three bridge views as separate labeled relations.** Their
   agreement (256 robust pairs) identifies genuine theory fusion; their
   disagreement (e.g. typeclass-only Algebra–CategoryTheory) identifies the
   *mechanism* of coupling, which is signal a merged graph would erase.

## 7. Reproduction index
- Analogy: 17→18→19→20/22/23/24/25→21/26/27; semantic 28→29/30/33→31→32;
  verifiers alongside (all VERIFICATION OK).
- Structure: `34_typeclass_structure.py` + Lean `35`; `36_generalization_links.py`
  + Lean `37`; `38_namespace_theory_structure.py`; `39_typeclass_bridge_structure.py`;
  `40_area_maturity_profile.py`; `41_combined_bridge_ranking.py`;
  `42_frontier_generalization_scan.py`; `43_class_fact_derivations.py`;
  `44_frontier_analogy_map.py`; each with a `verify_*.py`.
- Design/case notes: `notes/{16..44}_*.md`; running log `notes/execution.txt`.

## 8. Parked (await direction)
- 07 full-proof-term persistence (~70+ GB).
- Production integration of `PointwiseLift` into Mathlib (`external/mathlib4`
  stays read-only).
- Named-lemma / class-fact / frontier-analogy detectors are exhausted (0 gaps);
  any further discovery needs a genuinely new signal — e.g. the thin-donor
  frontier columns Dynamics/Combinatorics, proof-term-level (07) structure, or
  graph-anomaly rather than similarity search.

---

# 9. Frontier pivot (scripts 45–49): famous open problems and kernel-verified contributions

This section extends the memo beyond script 44. The lens changed on explicit
direction: "frontier" no longer means Mathlib's internal area buckets (Dynamics,
Combinatorics, …). It means **Fields/Abel/Clay-level famous open problems that
already have Lean code**, and the goal is no longer only to *map* the corpus but
to **build and kernel-verify missing mathematics** toward those problems — "do
everything the hard way."

A standing methodological note from this arc: **semantic similarity can be more
valuable than structural similarity when the target structure does not yet
exist.** If an abstraction is genuinely undiscovered, its formal realization is
incomplete, so structural (shape) matching systematically under-recalls it;
role/meaning-based matching is then the stronger signal.

## 9.1 Script 45 — research-problem footprint

Five famous open problems plus Fermat (a partly-proved control) were matched by
**both** name regex **and** expected module (a hit must satisfy both; raw name
hits alone are not counted).

| Problem | Named material | Support machinery | Readiness |
|---|---|---|---|
| Erdős unit-distance `u(n)=O(n^{4/3})` | **present** — `SimpleGraph.UnitDistEmbedding` (31 direct) | 258 | highest |
| Jacobian conjecture | 0 named | 2,513 — `Algebra.SubmersivePresentation.jacobian_isUnit` is essentially the exact hypothesis | high (machinery) |
| Multicolor Ramsey `R_r(k)` | 0 named (no Ramsey module at commit) | 837 | mid |
| Collatz / 3x+1 | 0 named (no `Hailstone`) | 303 | low |
| Navier–Stokes | 0 named — ODE only, no PDE layer | — | lowest |
| *control:* Fermat | partly proved — `FLT.Three` (191), `FLT.Four` (28) | — | — |

Conclusion: the unit-distance problem is the most buildable target; the Jacobian
conjecture has deep algebraic machinery but no named theorem; Navier–Stokes is
blocked upstream by the absence of a PDE layer.

## 9.2 Script 46 — unit-distance ingredient frontier

The Spencer–Szemerédi–Trotter proof of `u(n)=O(n^{4/3})` was decomposed into 10
ingredients, each matched by name **and** expected module.

- **Present (4):** the unit-distance object itself; the Euclidean / inner-product
  plane; Turán's theorem (126 hits); the Zarankiewicz `K_{s,t}` bound (31).
- **Partial (1):** homological Euler characteristic exists, but there is no
  planar `V−E+F`.
- **Absent (5):** point–line incidence, Szemerédi–Trotter, crossing number,
  planar graphs, graph degeneracy.

**Key methodological result — the false-friend problem is severe and is solved
by module anchoring.** The five absent ingredients have large *raw* name-hit
counts (327 / 171 / 125 / 18 / 446) but **zero** hits in their expected modules:
martingale *upcrossing* vs graph crossing; Szemerédi *regularity* vs
Szemerédi–*Trotter*; *nondegenerate* matrices vs graph *degeneracy*; *coplanar*
vectors vs *planar graphs*; `IncidenceAlgebra` vs geometric incidence. Keyword
search alone would report all five as present.

Build order identified: **degeneracy → planar+Euler → crossing lemma →
point–line incidence → Szemerédi–Trotter → the bound.**

## 9.3 Script 47 — second-level frontier inside `SimpleGraph`

- **Graph degeneracy = assembly gap, 5/7 present.** `degree`, `neighborSet` with
  `card_neighborSet_eq_degree`, subgraph/`induce`/`Subgraph.deleteVerts`
  (1,311), the key lemma **`exists_minimal_degree_vertex`**, and coloring
  (`Coloring.Vertex`, 209) all exist. Missing: only the elimination ordering and
  the degeneracy theorem / edge bound.
- **Planar graphs = layer gap, 3/6.** Cycles (`Walk.IsCycle`, 218),
  connectedness (411), trees / `Acyclic` / `IsTree` (173) are present; plane
  drawing (the 206 "embed" hits are graph-homomorphism embeddings — another false
  friend), faces (0), and planar Euler `V−E+F` (0 after excluding `IsEulerian`
  trails) are absent.

Conclusion: degeneracy is a small, near-term, *buildable* contribution; planar
needs a whole topological-embedding layer.

## 9.4 Scripts 48–49 — the gap is now filled, kernel-verified ("the hard way")

These are the **first Atlas outputs that add a theorem to the formal corpus
rather than map it.** Both compile under `leanprover/lean4:v4.34.0-rc2` with
exit 0, empty logs, no warnings and no `sorry`; the Lean kernel is the
correctness boundary. `external/mathlib4` was only read.

**48 — `48_degeneracy.lean`.** Defines
`SimpleGraph.DegeneracyAtMost k` by the vertex-peeling / elimination-ordering
inductive (`bot` for the empty graph; `peel` deleting a vertex of degree ≤ k).
Proves the sharp edge bound `Set.ncard G.edgeSet ≤ k · Set.ncard G.support` and
the textbook corollary `Finset.card G.edgeFinset ≤ k · Fintype.card V`. Peeling
arithmetic reuses Mathlib's `card_edgeFinset_deleteIncidenceSet` and
`card_support_deleteIncidenceSet`; the isolated-vertex and support-shrink cases
are closed explicitly (the nonlinear `k·(f−1)+k = k·f` step uses
`Nat.mul_add`/`Nat.sub_add_cancel`, not `omega`). Sanity `example`s include
`completeGraph (Fin 3)` having exactly 3 edges by `decide`.

**49 — `49_degeneracy_coloring.lean`.** Proves the coloring-number bound
`DegeneracyAtMost.colorable_succ`: a `k`-degenerate finite graph is properly
`(k+1)`-colorable, together with `chromaticNumber_le_succ` (`χ(G) ≤ k+1`). The
proof is the classical greedy algorithm along the reverse peeling order: color
the graph left after peeling `v`, then assign `v` a color not used by its at most
`k` neighbors (a free color exists by
`Finset.exists_mem_notMem_of_card_lt_card`). A search for `coloringNumber`,
`degenera`, and `greedy` under `SimpleGraph` confirms the result is genuinely
absent from Mathlib at this commit.

**Settled Lean-API facts (4.34.0-rc2):** there is no `Set.card` (finite set
cardinal is `Set.ncard`; the Finset-coercion lemma is lowercase
`Set.ncard_coe_finset`); statements that must survive induction over a
`DecidableRel`-carrying constructor are phrased instance-independently
(`Set.ncard`, `Colorable`) so the motive does not mention an instance; rewrite
`edgeSet`, never the instance-dependent `edgeFinset`, across `G = ⊥`; do not
`subst x = v` when later terms mention `v`; `if_pos/if_neg` are deprecated in
favor of `ite_eq_left/ite_eq_right`.

**Net effect on the unit-distance chain:** its first missing ingredient
(degeneracy) now has both standard elementary consequences — the edge bound and
greedy coloring — formally proved. The frontier moves to the planar/Euler layer.

## 9.5 Updated conclusions

7. **Keyword footprinting must be module-anchored at every level.** Across 45–47
   every absent ingredient had abundant misleading raw name hits; a hit counts
   only when name regex and expected module agree.
8. **The mature stdlib is tightly abstracted (sections 1–8), and the genuinely
   open frontier is at the boundary of what Mathlib has formalized at all** —
   famous problems whose *layers* are missing (planar topology, PDEs) versus
   small *assembly gaps* (degeneracy) that are immediately buildable.
9. **Atlas has moved from analysis to verified synthesis.** Beyond detecting
   `PointwiseLift` (the one positive abstraction in the stdlib sweep), it now
   produces standalone, kernel-verified Lean developments that fill diagnosed
   gaps. This validates the loop map → identify gap → construct → kernel-verify.

## 9.6 Reproduction index (45–49)

- `45_research_problem_footprint.py` + `verify_research_problem_footprint.py`
  (VERIFICATION OK); `data/research_problem_footprint.jsonl` (6 rows),
  `data/research_problem_summary.json`.
- `46_unit_distance_frontier.py` + `verify_unit_distance_frontier.py`
  (VERIFICATION OK); `data/unit_distance_frontier.jsonl` (10 rows), summary JSON.
- `47_degeneracy_planar_frontier.py` + `verify_degeneracy_planar_frontier.py`
  (VERIFICATION OK); `data/degeneracy_planar_frontier.jsonl` (13 rows), summary.
- Lean (verification = kernel compile, exit 0, empty log, no sorry):
  `script/lean/48_degeneracy.lean`, `script/lean/49_degeneracy_coloring.lean`;
  design notes `notes/48_degeneracy_design.md`,
  `notes/49_degeneracy_coloring_design.md`; logs `notes/48_degeneracy.log`,
  `notes/49_degeneracy_coloring.log`.

## 9.7 Next steps and parked items (updated)

- **Next "hard way" target (recommended):** construct the peeling ordering for an
  arbitrary finite graph from `exists_minimal_degree_vertex` (equivalence with
  "every nonempty subgraph has a vertex of degree ≤ k") by well-founded recursion
  on support size; then begin the **planar/Euler layer** (plane embedding, faces,
  `V−E+F`), the next missing ingredient of the unit-distance chain.
- Second frontier target: apply the 45–47 treatment to the **Jacobian
  conjecture** (rich machinery, no named theorem).
- Still parked: 07 full proof-term persistence (~70+ GB); production integration
  of `PointwiseLift` into Mathlib (`external/mathlib4` read-only).

## 9.8 Script 50 — existence of the elimination ordering (kernel-verified)

Script 48–49 *consume* a `DegeneracyAtMost` derivation; script 50
(`50_degeneracy_elimination.lean`, exit 0, empty log, no `sorry`) *constructs*
one, completing the fixed-type degeneracy theory:

- `of_forall_exists_low_degree k`: if every nonempty graph on `V` has a vertex
  **in its support** of degree ≤ k, every graph is `k`-degenerate. The proof is
  `Nat.strong_induction_on` on `Fintype.card support`: peeling a support vertex
  strictly shrinks the support (`card_support_deleteIncidenceSet`), so the
  recursion terminates at `⊥`.
- `degenerate_card_sub_one`: **every finite `n`-vertex graph is
  `(n-1)`-degenerate** (`support_eq_bot_iff` gives a support vertex;
  `degree_lt_card_verts` gives the degree bound).

Together 48–50 form a coherent kernel-verified package: existence of an
ordering (50) → edge bound `|E| ≤ k·|V|` (48) → greedy `(k+1)`-coloring and
`χ(G) ≤ k+1` (49); instantiating 50 with `k = n−1` recovers the universal
`|E| ≤ (n−1)n` and `χ(G) ≤ n` constructively. The only piece not yet proved is
the tight **induced-subtype** equivalence "k-degenerate iff every nonempty
*induced subgraph* has a vertex of degree ≤ k", because `G.induce` returns a
graph on a subtype rather than on `V`.

New settled API facts: `rec` is a reserved keyword; `Nat.strong_induction_on`
takes no named `motive` argument (carry `DecidableRel` explicitly and install it
with `letI`, scope-disabling `linter.style.haveILetI`); project an implicit-graph
iff as `(support_eq_bot_iff (G := H)).mp`.

**Updated unit-distance chain status:** degeneracy is now a finished kernel
building block (existence + edge bound + coloring). The next missing ingredient
is the planar/Euler *layer* (plane embedding, faces, `V−E+F`).

## 9.9 Script 51 — planar edge bounds from Euler (kernel-verified)

`51_planar_edge_bounds.lean` (exit 0, empty log, no `sorry`) supplies the two
estimates the crossing-lemma / unit-distance chain actually consumes from
planarity, in namespace `SimpleGraph.PlanarBounds`:

- `planar_edge_bound`: from Euler `n − e + f = 2` and the face-degree fact
  `3f ≤ 2e` (every face boundary has length ≥ 3, total boundary length `= 2e`),
  **`e ≤ 3n − 6`** for `n ≥ 3`;
- `bipartite_planar_edge_bound`: triangle-free faces have length ≥ 4,
  `4f ≤ 2e`, giving **`e ≤ 2n − 4`**;
- `PlaneData G` / `BipartitePlaneData G` interfaces and graph-level corollaries
  over `Fintype.card V` / `Finset.card G.edgeFinset`; the triangle and `K₄`
  saturate `e = 3n − 6` (`norm_num`).

**Scope, stated honestly:** this is the *downstream* half of the planar layer.
`euler` and `faceBoundary` are hypotheses — the exact data a plane embedding
produces — and no graph is asserted planar. The missing *layer* is a
combinatorial embedding (rotation system/map on the sphere) whose face orbits
satisfy `V−E+F = 2`. A rotation system encodes any orientable surface
(`χ = 2−2g`); permutation-sign arguments recover only the parity of `V−E+F`, and
the constant `2` requires a genus/topological argument, which is precisely why
47 flagged planar as a layer gap rather than a missing lemma. Once that
embedding exists, the crossing-lemma edge estimates now follow with no further
work.

**Unit-distance build-chain status:** degeneracy is finished (48–50); the
planar *edge estimates* are finished against the Euler interface (51). The
remaining combinatorial prerequisites toward `u(n) = O(n^{4/3})` are the
embedding→Euler construction, the crossing lemma, point-line incidence, and
Szemerédi–Trotter.

Lean facts settled: prove the Euler arithmetic in `ℤ` (`linarith` after casting
the Nat face inequality by `exact_mod_cast`) and align Nat casts with
`rw [Nat.cast_sub (by omega), Nat.cast_mul]; norm_num` — neither `zify; linarith`
nor `ring` closes it directly; a doc comment directly before `omit … in` is a
parse error (use a `--` comment).

## 9.10 Script 52 — semantic donor-transfer map for the frontier (part (b))

Part (b) points **semantic** (not structural/AST-shape) matching at
incompletely-formalized material, on the principle that an undiscovered
structure has an *incomplete* structural signature and so is under-recalled by
shape matching. `52_frontier_semantic_donors.py` (independent verifier prints
**VERIFICATION OK**, rebuilding document frequency and recomputing the meaning
cosine for 39 pairs from raw rows) makes the search asymmetric and
meaning-first:

```
frontier target (famous-problem seed, or a thin/opaque decl)
        -- 0.65·meaning + 0.35·role TF-IDF nearest neighbour --> mature core donor
```

Meaning = identity-free concept words (name + conclusion head + value head);
role = conclusion/value/proof roles and the constraint-*area* profile. The gate
is shared meaning (≥2 words, meaning cosine ≥ 0.30, sim ≥ 0.42); structural
divergence is *reported*, never required, so opaque/partial targets still match.
Notation boilerplate and same-concept-family pairs (sharing a rare word,
df ≤ 400; 17,167 dropped) are removed.

Results on 287,173 eligible declarations: 1,781 frontier targets, 186,207 core
donors, **703 targets (39.5%) with a strong mature donor**, 3,698 pairs.

- **Independent confirmation of the layer-gap zeros** from scripts 45–47: a
  purely semantic pass still finds **0 named** planar-graph, Ramsey,
  Collatz/Hailstone, or Navier–Stokes declarations. Jacobian (309 named / 117
  with donor), degeneracy (125/60), coloring (134/27), incidence (107/23),
  unit-distance (15/12) are populated.
- **Donor routing is coherent and re-derives where the machinery lives**:
  Jacobian ← RingTheory/LinearAlgebra (`MvPolynomial.eval₂…`,
  `LinearMap.baseChange`); unit-distance ← Topology
  (`IsometryEquiv.mk`/`ContinuousMap.mk`, role cosine 1.00); coloring ←
  Order/Data, with `Coloring.colorClass` ↔ **`Set.image2`** (the PointwiseLift
  pattern recurring independently).
- **False friends reproduced semantically**: the corpus's "degeneracy" is
  simplicial `ExtraDegeneracy` (homotopy), not graph degeneracy — the exact gap
  scripts 48–50 had to fill; "crossing" donors are martingale
  `upperCrossingTime`, not graph crossings.
- The highest-similarity genuine pairs are frontier specializations re-deriving
  a core generic (`ιChainComplex_d`↔`ChainComplex.mk_d`,
  `contMDiff`↔`contDiff`, `norm_compLp`↔`norm_sub`) — genericization candidates.

Scope: this is a donor-routing and coverage instrument (and a second,
methodologically independent witness for the footprint map), not a conjecture
generator; distant analogies that share few words still need the role-only
channel or a learned embedding.

**Arc status (45–52).** Frontier map (45–47) → kernel-verified gap-fill: graph
degeneracy existence/edge-bound/coloring (48–50) and the planar edge estimates
behind the Euler interface (51) → semantic donor routing for the frontier (52).
The remaining planar *embedding→Euler* layer, the crossing lemma, point-line
incidence and Szemerédi–Trotter are the open combinatorial build toward
`u(n) = O(n^{4/3})`; the Jacobian conjecture is the richest algebraic frontier
target (its hypothesis is literally `jacobian_isUnit`).

## 9.11 Script 53 — the crossing lemma (kernel-verified)

`53_crossing_lemma.lean` (exit 0, empty log, no `sorry`) proves the workhorse
estimate behind the Erdős unit-distance / incidence bounds, in namespace
`SimpleGraph.CrossingLemma`:

- `crossing_number_linear`: deleting one edge per crossing leaves a plane graph
  with `≤ 3n−6` edges (script 51), so **`c ≥ e − 3n + 6`**;
- `crossing_number_linear'`: the sampling form **`c ≥ e − 3n`**;
- `crossing_lemma`: with `0 < n`, `e ≥ 4n`, and the random-sampling inequality
  `∀ p ∈ (0,1], p⁴ c ≥ p² e − 3 p n`, **`c ≥ e³/(64 n²)`** — the sharp
  constant `1/64`, obtained at the optimal retention probability `p = 4n/e`
  (survival probabilities `p`, `p²`, `p⁴` for vertices / edges / crossings;
  closed by `field_simp; ring`).

As with 51, the two non-arithmetic inputs are isolated and stated honestly:
(1) a plane-drawing/crossing model in which deleting one edge per crossing
planarizes (the shared embedding layer), and (2) the linearity-of-expectation
wiring that produces `p⁴ c ≥ p² e − 3 p n`. Given those, the crossing lemma
itself is fully proved; it is the exact estimate that converts a point-line
incidence count into `u(n) = O(n^{4/3})`.

**Unit-distance chain:** degeneracy (48–50) ✓, planar edge estimates (51) ✓,
crossing lemma (53) ✓ — all the *numerical/combinatorial* consequences are now
kernel-verified behind a single shared geometric/probabilistic interface. The
remaining builds are that interface itself (plane embedding/drawing + finite
expectation), then point-line incidence and Szemerédi–Trotter.

---

# 10. Closing the unit-distance arithmetic spine and building the planar-map layer (scripts 54–55)

Both files are kernel-verified (`lake env lean`, exit 0, empty log, no `sorry`, no
warnings); they continue the "hard way" leg of scripts 48–53.

## 10.1 Script 54 — incidence, Szemerédi–Trotter, `u(n) = O(n^{4/3})`

`SimpleGraph.Incidence`, self-contained.

* **Multigraph crossing lemma.** Multiplicity `≤ s`, `e ≥ 4 s n` ⇒
  `c ≥ e³/(64 s² n²)`, from the sampling expectation `p⁴c ≥ p²e − 3 s p n` at
  `p = 4 s n/e`. `s = 1` recovers the script-53 simple-graph lemma. The `s²`
  denominator is the honest consequence of the `e ≤ 3 s n` plane-multigraph
  bound; it is slightly non-sharp and sufficient.
* **Bounded-intersection incidence bound.** Curves meeting at most `t` times
  (`c ≤ (t/2) m²`), `I ≤ e + m`, any `K³ ≥ 32 t s²` ⇒
  `I ≤ K n^{2/3} m^{2/3} + 4 s n + m`. Dense case joins the crossing lemma to
  the crossing upper bound; sparse case is `e < 4 s n`.
* **Szemerédi–Trotter (lines, s=t=1, K=4):**
  `I ≤ 4 n^{2/3} m^{2/3} + 4 n + m`.
* **Unit distance (unit circles, s=t=2, K=8, m=n, I=2u):**
  **`u(n) ≤ 9 n^{4/3}` for `n ≥ 1`**, with the constant *derived*
  (`2u ≤ 8 n^{4/3} + 9n`, then `n ≤ n^{4/3}` folds the linear term into
  `17/2 n^{4/3} ≤ 9 n^{4/3}`).

The only un-proved inputs are genuine plane/probability facts, isolated as
hypotheses: bounded curve intersections, edge multiplicity, `e = I − m'`, and
the sampling expectation. No points, lines or circles are asserted to exist.

**Significance.** Scripts 46/47 listed point-line incidence, Szemerédi–Trotter
and the crossing-number consequence among the *absent* ingredients of the
unit-distance chain; with 53 and 54 every *combinatorial/arithmetic* ingredient
is now kernel-verified. The single residual gap is geometric (the plane
embedding / unit-circle intersections), which 55 begins.

## 10.2 Script 55 — combinatorial planar maps, Euler *proved* not assumed

`SimpleGraph.PlanarMaps`, self-contained. This is the start of the missing
plane layer that script 47 flagged as a **layer gap** and that script 51 hid
behind the `PlaneData` interface.

* `inductive IsPlanarMap (v,e,f)` with constructors `point (1,0,1)`,
  `addVertexEdge` (subdivide / attach leaf: `(v+1,e+1,f)`), `addFaceEdge`
  (split a face: `(v,e+1,f+1)`).
* **Euler's formula `v + f = e + 2` is proved by induction**, together with
  `1 ≤ v`, `1 ≤ f`, connectedness `v ≤ e + 1`, and the signed `ℤ` form.
* `IsSimplePlanarMap` (triangle base; diagonal allowed only under the guard
  `3f+1 ≤ 2e`, the count-level statement "a face of boundary length ≥ 4 exists")
  proves `3f ≤ 2e` and hence **`e ≤ 3v − 6`**.
* `IsBipartitePlanarMap` (quadrilateral base; guard `4f+2 ≤ 2e`) proves
  `4f ≤ 2e` and hence **`e ≤ 2v − 4`**.
* Triangle and quadrilateral are constructed from `point`; all sharpness and
  base-map Euler checks pass.

The edge bounds are therefore **unconditional for the inductive class** —
script 51's Euler/face hypotheses are now derivable. The single cited (not
proved) fact is the topological **realization/characterization theorem**: a
bare rotation system encodes an orientable surface of genus `g` with
`v−e+f = 2−2g`, and identifying `g = 0` is the genuinely topological step the
inductive predicate packages. Building the dart/rotation-system model and that
genus-zero proof is the remaining layer work; 55 is its combinatorial
foundation and the exact interface it must inhabit.

## 10.3 Revised status of the unit-distance chain

| ingredient | status after 54–55 |
|---|---|
| graph degeneracy (edge bound, coloring, existence) | **proved** (48–50) |
| planar edge bounds `3v−6`, `2v−4` | proved from an Euler **interface** (51); now also from a combinatorial planar-map class with Euler **proved** (55) |
| crossing lemma `e³/(64n²)` | **proved** behind sampling interface (53) |
| multigraph crossing lemma | **proved** (54) |
| Szemerédi–Trotter incidence bound | **proved** behind geometry interface (54) |
| unit distance `u(n) ≤ 9 n^{4/3}` | **proved** behind geometry interface (54) |
| plane embedding / rotation system → genus-zero Euler | combinatorial core built (55); topological realization cited, not proved |
| unit-circle intersection facts / expectation wiring | interface only |

The project can now state precisely that the Erdős unit-distance theorem is
complete up to one geometric layer (plane embeddings with `g=0` and elementary
unit-circle geometry), every downstream combinatorial step being
kernel-verified.

## 11. Script 56 — rotation systems / combinatorial maps from permutations

script/lean/56_combinatorial_maps.lean (namespace SimpleGraph.CombiMap,
structure Map) replaces the geometric *drawing* hypothesis of 51/53/54 with a
purely algebraic object on a finite type of **darts**:

* edge involution τ (fixed-point-free, τ² = 1), vertex rotation σ,
  face permutation φ = τ·σ⁻¹;
* V / E / F are **orbit counts** of permutations. Mathlib has no numCycles, so
  orbits α p = Multiset.card p.cycleType + (Fintype.card α - p.cycleType.sum)
  (nontrivial cycles plus fixed points).

Kernel-verified results (exit 0, empty log, no sorry / warnings):

* orbits α 1 = card α; orbits α (swap a b) = card α - 1;
* **2·E = #darts** — a fixed-point-free involution is all 2-cycles with full
  support;
* **Even (V - E + F) for every combinatorial map**, from
  sign φ = sign τ · sign σ and the sign_of_cycleType exponent parity;
* hence an integer genus with **χ = 2 - 2·genus**;
* two genus-zero seeds on Fin 2: the link (V2 E1 F1) and the loop (V1 E1 F2),
  both χ = 2.

### 11.1 What 56 does and does not settle

56 proves the part of the orientable classification that is **pure algebra and
holds for every map**: evenness of χ and existence of an integer genus, plus
the genus-zero base cells. It deliberately does **not** prove (design note
§5):

1. connectedness (transitivity of the subgroup generated by τ, σ);
2. genus ≥ 0 / χ ≤ 2 for a connected map — this needs the lemma that a
   transposition changes a permutation's cycle count by exactly ±1 (a swap
   splits or joins one cycle), for which Mathlib offers no ready-made lemma;
3. genus-zero *realization* of a connected rotation system by a plane/sphere
   drawing — the remaining topology that would make the PlaneData interfaces
   of 51/53/54 concrete.

### 11.2 Updated position of the plane-embedding layer

| ingredient | status after 54–56 |
|---|---|
| combinatorial planar-map class, Euler v+f=e+2 by induction | **proved** (55) |
| dart / rotation-system model, V/E/F as permutation orbit counts | **proved** (56) |
| 2E = #darts, χ even for every map, integer genus χ=2−2g | **proved** (56) |
| genus-zero seeds (link, loop) | **proved** (56) |
| swap split/join cycle-count lemma; connectedness; χ ≤ 2 | **not proved** (next combinatorial step; no Mathlib lemma exists) |
| genus-zero topological realization | cited, not proved (the genuine layer gap) |

The geometric layer has therefore narrowed to a precise frontier: one
combinatorial lemma (transposition changes cycle count by ±1) plus connectedness
gives χ ≤ 2, and one topological realization theorem connects rotation
systems to the PlaneData interfaces. Everything on either side is
kernel-verified.
## 12. Script 57 — the transposition split/join lemma (the primitive 56 was missing)

Script 56 proved that the Euler characteristic of every combinatorial map is even
and that an integer genus exists, but left χ ≤ 2 (genus ≥ 0) for connected maps
to the classical lemma that a transposition changes a permutation's cycle count by
exactly one. Mathlib has no such lemma and no `numCycles`, so script 57
(`script/lean/57_swap_split_join.lean`, namespace `SimpleGraph.OrbitSplit`,
kernel-verified: exit 0, empty log, no sorry) constructs both.

- **Split (+1):** for a cycle `f` and `f x ≠ x`, `g = swap x (f x) * f` fixes `x`
  and is otherwise one cycle; `orbits g = orbits f + 1`. The length-2 case is
  `f = swap` (so `g = 1`); the length ≥ 3 case uses `IsCycle.swap_mul` and
  `support_swap_mul_eq` (`g.support = f.support \ {x}`).
- **Join (−1):** for a cycle `f` fixing `z` with `x` on the cycle,
  `h = swap z x * f` is one cycle through `z` and the whole support,
  `h.support = insert z f.support`, and `orbits h = orbits f − 1`. The joined
  `IsCycle` is built directly (there is no absorbing Mathlib lemma): minimal
  period at `x` from `pow_eq_one_iff'` + `orderOf_dvd`, the enumeration
  `(h^(j+1)) z = f^j x` for `j < orderOf f`, and `SameCycle.exists_pow_eq'`
  covering the support.

The join is the exact algebraic inverse of the split. The fully general same-cycle
cut and the join of two nontrivial cycles follow by the same `f^i x` enumeration
and are noted, not written.

### 12.1 Updated position of the plane-embedding layer

| ingredient | status after 54–57 |
|---|---|
| combinatorial planar-map class, Euler v+f=e+2 by induction | **proved** (55) |
| dart / rotation-system model, V/E/F as permutation orbit counts | **proved** (56) |
| 2E = #darts, χ even for every map, integer genus χ=2−2g | **proved** (56) |
| genus-zero seeds (link, loop) | **proved** (56) |
| transposition split/join cycle-count lemma (±1) | **proved** (57) |
| connectedness of a map (transitivity of ⟨τ, σ⟩) | not proved (next combinatorial step) |
| edge-insertion induction → connected χ ≤ 2 / genus ≥ 0 | not proved (now unblocked by 57) |
| genus-zero topological realization | cited, not proved (the genuine layer gap) |

The geometric frontier has narrowed again: with the ±1 lemma in hand, connected
χ ≤ 2 is a pure edge-insertion induction once connectedness (transitivity of the
subgroup generated by the edge involution and vertex rotation) is established.
Only genus-zero realization remains as an actual topological theorem; everything
combinatorial on either side of it is kernel-verified.
## 13. Script 58 — connectedness of combinatorial maps

Script 57 supplied the transposition ±1 primitive; script 58
(`script/lean/58_map_connectedness.lean`, namespace `SimpleGraph.MapConnected`,
kernel-verified: exit 0, empty log, no sorry, no warnings) supplies the other
hypothesis that χ ≤ 2 for a surface component needs — connectedness — and states
it in the form the edge-insertion induction of 59 will consume.

- **Primal–dual group identity.** `vertGroup = closure {τ, σ}` and
  `faceGroup = closure {τ, φ}` (φ = τσ⁻¹) are equal: φ = τσ⁻¹ lies in the vertex
  group and σ = φ⁻¹τ (using τ² = 1) lies in the face group, both via the
  `Subgroup.closure_le` iff. Connectedness is therefore invariant under the
  primal/dual (V ↔ F) swap, exactly as Euler's formula suggests.
- **Explicit walk characterization.** An inductive `Reachable` relation (single
  τ/σ steps in both directions, reflexivity, transitivity; with `symm`) is proved
  equivalent to membership in the orbit of `closure {τ, σ}`:
  `y ∈ orbit vertGroup x ↔ Reachable M x y`, in both directions. Orbit-to-walk
  builds the subgroup of permutations that preserve reachability in both
  directions and shows it contains the generators; walk-to-orbit inducts on the
  walk and composes subgroup witnesses. `Connected` (every orbit the whole type)
  is thus `∀ x y, Reachable M x y`, and checking from one base dart suffices.
- **Genus-zero seeds are connected:** the one-edge link and loop of 56 on
  `Fin 2` both satisfy `Connected` (`fin_cases` + `decide`).

### 13.1 Updated position of the plane-embedding layer

| ingredient | status after 54–58 |
|---|---|
| combinatorial planar-map class, Euler v+f=e+2 by induction | **proved** (55) |
| dart / rotation-system model, V/E/F as permutation orbit counts | **proved** (56) |
| 2E = #darts, χ even for every map, integer genus χ=2−2g | **proved** (56) |
| genus-zero seeds (link, loop) | **proved** (56) |
| transposition split/join cycle-count lemma (±1) | **proved** (57) |
| connectedness = transitivity of ⟨τ,σ⟩, with explicit walk relation; primal–dual identity; seeds connected | **proved** (58) |
| edge-insertion / spanning-tree induction → connected χ ≤ 2 / genus ≥ 0 | not proved (script 59; needs the *general* ±1: non-adjacent same-cycle cut and two-nontrivial-cycle join, then a walk-based induction using 58) |
| genus-zero topological realization | cited, not proved (the genuine terminal layer gap — real topology, not permutation combinatorics) |

Everything combinatorial needed to state and run the χ ≤ 2 induction is now
kernel-verified except the two fully general transposition forms (the adjacent
split and fixed-point join of 57 are the hard representative cases; the rest is
the same cycle enumeration). After 59, the only thing standing between the dart
model and a concrete plane/sphere is a genuine topological realization theorem,
which should be cited as topology rather than asserted from permutations.
## 14. Script 59 — connected maps satisfy χ ≤ 2 and genus ≥ 0

Script 59 (`script/lean/59_connected_euler_bound.lean`, namespace
`SimpleGraph.SwapOrbit`, kernel-verified: exit 0, empty
`notes/59_connected_euler_bound.log`, no sorry, no warnings) closes the
combinatorial Euler-characteristic spine. For every connected combinatorial map
(`closure {τ, σ}` transitive on the darts) it proves, entirely inside the
permutation model with no topological hypothesis beyond the dart data:

- **`Map.connected_euler_bound`**: `(V : ℤ) − E + F ≤ 2`;
- **`Map.connected_genus_nonneg`**: `0 ≤ (2 − (V − E + F)) / 2`.

The proof is the spanning-tree argument promised in 56–58, done "the hard way":

1. **General ±1 lemmas (stage 2).** Multiplying a permutation on the left by a
   transposition whose points lie on the same cycle splits it (orbit count +1,
   `orbits_swap_same_cycle`); points on different cycles join them (−1,
   `orbits_swap_different_cycles`); universally the change is at most +1
   (`orbits_swap_le`). These are the general forms 57 flagged as missing
   (non-adjacent cut, two nontrivial cycles).
2. **Involution factorization (stage 3a).** Every involution is a product of
   pairwise support-disjoint transpositions (`involution_swap_factor`), with
   support-card and list-length identities. The fixed-point-free edge
   involution τ therefore factors into exactly E transpositions
   (`#darts = 2E`).
3. **Spanning-tree growth (stages 3c–3d, `connected_growth`).** Connectedness
   guarantees that, until all darts are covered, some edge transposition crosses
   from the covered vertex cycles to a disjoint σ-cycle (`crossing_pair`);
   multiplying by it is a JOIN (−1 orbit). After V − 1 such pairwise-disjoint
   "tree" transpositions, `p = T * σ⁻¹` has exactly one orbit and
   `tree.length + 1 = orbits σ = V`.
4. **Face bound (stage 3e).** The residual involution `τR = τ * T` (tree edges
   removed) factors into `R.length = E − V + 1` transpositions; the face
   permutation is `φ = τR * p` (using T² = 1), and the fold bound
   `orbits_prod_swap_le` gives `F ≤ orbits p + R.length = 1 + E − V + 1`,
   i.e. `χ ≤ 2`. The empty-dart case gives V = E = F = 0.

### 14.1 Updated position of the plane-embedding layer

| ingredient | status after 54–59 |
|---|---|
| combinatorial planar-map class, Euler v+f=e+2 by induction | **proved** (55) |
| dart / rotation-system model, V/E/F as permutation orbit counts | **proved** (56) |
| 2E = #darts, χ even for every map, integer genus χ=2−2g | **proved** (56) |
| genus-zero seeds (link, loop), χ = 2 attained | **proved** (56, connected in 58) |
| transposition split/join cycle-count lemma (±1), general forms | **proved** (57 adjacent/fixed; 59 general S/J/U) |
| connectedness = transitivity of ⟨τ, σ⟩, walk relation, primal–dual identity | **proved** (58) |
| connected χ ≤ 2 / genus ≥ 0 via spanning-tree growth | **proved** (59) |
| planar edge bounds e≤3v−6, e≤2v−4; crossing lemma; Szemerédi–Trotter; u(n) ≤ 9n^(4/3) | **proved** behind PlaneData (51,53,54), now backed by the full combinatorial spine |
| genus-zero topological realization (rotation system ↔ sphere cell decomposition) | cited, not proved — the genuine terminal layer gap (real topology, not permutation combinatorics) |

The entire combinatorial spine of the planar/frontier thread is now
kernel-verified: orbit-count V/E/F, parity and integer genus for all maps,
connectedness, the χ ≤ 2 bound for connected maps, and, downstream of the
PlaneData interface, the edge bounds, crossing lemma, Szemerédi–Trotter and the
unit-distance bound. The single remaining gap is not combinatorics but
topology: proving (or citing the standard rotation-system embedding theorem)
that a connected χ = 2 rotation system is realized by a cell decomposition of
the sphere, which would make PlaneData concrete. Equality χ = 2 is attained
(56's connected genus-zero seeds) but not classified here; parity/integrality
of the genus for all maps rests on 56.
## 15. Note 60 — genus-zero realization scoped; the frontier section closes combinatorially

`notes/60_genus_zero_realization_layer_gap.md` closes the frontier thread honestly.
The one remaining item after 59 is the **Heffter–Edmonds–Youngs rotation-system
embedding theorem**: a rotation system (τ fixed-point-free edge involution, σ vertex
rotation) determines a 2-cell embedding in a closed orientable surface whose faces
are the φ = τσ⁻¹ orbits, with χ = V − E + F and genus g = (2−χ)/2; connected χ = 2
is the sphere (classification of surfaces), and stereographic projection gives the
plane. Its arithmetic is kernel-verified in 55–59; its topology is not.

A direct inventory of the pinned Mathlib (`bbcd1968`) records what a formal
realization could stand on: `SimpleGraph.Dart` (half-edges, no rotations), classical
and abstract CW complexes with finite complexes and a 1-skeleton-as-graph file
(2024–2026 additions), `TopCat.Sphere`, manifolds/Whitney, and an abstract
homological Euler characteristic (2025). Missing: the rotation-system→surface
(gluing/ribbon) construction and its 2-manifold proof, orientability from rotations,
classification of compact surfaces (no surface theory at all; "Planar graphs" is
only a TODO header), the CW cell-count ↔ homological Euler-characteristic formula,
planarity/Kuratowski, and sphere↔plane transfer. The note stages the work (CW Euler
formula; gluing construction; orientability; classification or weak χ=2 lemma; graph
correspondence; stereographic transfer), flagging the gluing and classification
stages as research-grade multi-PR efforts — which is why the theorem is cited
(Heffter 1898; Edmonds, Notices AMS 7 (1960), 646; Youngs, J. Math. Mech. 12 (1963),
303–315; Ringel; Gross–Tucker; Hatcher) rather than asserted.

**Frontier status.** Every combinatorial claim the layer-gap analysis of 45–47
identified — parity/integer genus (56), connectedness (58), connected χ ≤ 2 /
g ≥ 0 (59), and the conditional extremal chain e≤3v−6 / crossing / Szemerédi–
Trotter / u(n) ≤ 9n^(4/3) (51,53,54) — is kernel-verified. The single residual
hypothesis is a named, textbook topological realization theorem, explicitly cited.
The frontier section is finished to the boundary the project set itself: Atlas
proposes and proves combinatorially; the Lean kernel disposes; the remaining
topology is named, not faked.
## 16. Script 62 — incidence chain complex, Betti ranks, and the algebraic χ ≤ 2 proof

`script/lean/62_incidence_chain_complex.lean` (namespace `SimpleGraph.MapChain`,
exit 0, empty log, no `sorry`) builds the cellular chain complex over ℚ for the
combinatorial-map model of 55–59,

    C₂ = ℚ^F ──∂₂──▶ C₁ = ℚ^E ──∂₁──▶ C₀ = ℚ^V,

with V/E/F the vertex/edge/face orbit counts and proves, independently of the
combinatorial spanning-tree argument in 59:

- `∂₁ * ∂₂ = 0` (face boundary walks are closed): each corner’s signed ∂₁ column
  telescopes to one directed face step (`corner_column`), and summing around a
  face carrier cancels by permutation of the carrier.
- Euler–Poincaré: `V − E + F = b₀ − b₁ + b₂` with
  `b₀ = |V| − rank ∂₁`, `b₁ = |E| − rank ∂₁ − rank ∂₂`,
  `b₂ = |F| − rank ∂₂`; rank–nullity gives `b₁ ≥ 0`.
- **b₀ = 1** for connected maps: `ker ∂₁ᵀ` is exactly the constant vertex
  functions (endpoint equality per edge, propagated from edge representatives to
  all darts and along vertex rotations); `rank ∂₁ = |V| − 1`.
- **b₂ = 1** for connected maps: `ker ∂₂` is exactly the constant face functions.
  Each edge has two oppositely signed corners; ∂₂-closedness plus the face-carrier
  partition forces equality across every edge, the conjugated relation
  `τ′ d = σ(τ(σ⁻¹ d))` propagates it to all darts, and the identities
  `φ(τ′(φ⁻¹ d)) = τ d` and `σ = φ⁻¹ τ` recover invariance under both generators
  from face invariance; connectedness then forces one value. `rank ∂₂ = |F| − 1`.
- Hence **χ = 2 − b₁ ≤ 2** for connected nonempty maps (`euler_le_two`), with a
  separate empty-map corollary (`V = E = F = 0`, χ = 0).

This is a **second, purely linear-algebraic proof** of the terminal planar bound of
the frontier thread, and it produces the Betti data that a future homology
identification would consume. What remains is exactly the cited topology of note
60 (Heffter–Edmonds–Youngs rotation-system realization): script 62 is the chain
complex such a realization theorem connects to surface homology; it adds no new
combinatorial hypotheses and discharges the entire algebraic half. The planar
frontier therefore now has both proofs of its terminal inequality kernel-verified
(59 combinatorial, 62 algebraic), with the single topological realization theorem
named and cited rather than faked. Option C of note 61 is complete; options B
(general CW Euler formula) and D (full realization) remain parked as multi-month/
year upstream campaigns.
## §17 — Script 64: semantic-first whole-stdlib analogy scan and the "orphan functor" family (2026-09-22)

Generalizing script 52 from frontier targets to the whole mature stdlib: a two-channel scanner over 183,271 eligible declarations in the 10 core areas. Semantic channel (meaning+role TF-IDF, rarest-anchor blocking, cross-area/cross-namespace) kept 130,268 pairs; structural channel (exact type-shape blocking with a complexity floor) kept 1,973; union-find yields 549 clusters (542 nondiffuse). Verifier enforces the PointwiseLift positive control: Set.image2 and Filter.map2 co-cluster with structCos=1.000 / meaningCos=0.000, and 30 parallel lemma pairs across the PointwiseLift family co-cluster — demonstrating that the known abstraction is invisible to name semantics.

**New result — the orphan-functor family (second PointwiseLift-class signal, weaker conceptually but directly actionable).** The unary lift map : (alpha->beta) -> F alpha -> F beta (and binary map2/zipWith) recurs with identical type shapes across the corpus, but Functor/Applicative/Monad integration is patchy. Fully integrated: Set, Multiset, Filter (Functor global; Monad only protected/local), Ultrafilter, Part, Trunc, Erased, Stream'.Seq/Seq1/WSeq, Computation, WithOne/WithZero. Hand-written lifts with proved functor laws but NO registered instance: Sym2 (map_id/map_comp proved; docstring literally says "the functor Sym2 is functorial"), WithBot/WithTop (map:=Option.map, map2:=Option.map2, map_id/map_map/map_comp_map proved), OnePoint (map_id/map_comp proved), Stream' (map_id/map_map proved), Cycle (map exists; id/comp laws not even proved), Filter.Germ (map and map2, no instances). The binary-lift family is correspondingly larger than the original PointwiseLift finding (adds Germ.map2, WithBot/WithTop/WithOne/WithZero.map2, WSeq.zipWith). CompactCoherentification.map and SummationFilter.map were checked and correctly excluded (extra hypotheses). This is integration/omission debt against an existing abstraction rather than a missing concept; it is PR-shaped (register instances; prove Cycle's two laws), pending downstream checks for diamond/notation reasons.

**Classified non-findings:** bundled-hom API propagation (zero_apply/add_apply/Hom.ext/hom_comp/mk.inj/coeFnAddMonoidHom repeated across Seminorm..ContinuousLinearMap and concrete category Homs; FunLike/BundledHom machinery lives in CategoryTheory and is not propagated to core), Subobject.pi across six bundled set types, cross-module re-exports (TensorProduct vs Algebra.TensorProduct, LinearMap vs ContinuousLinearMap, AffineEquiv hierarchy, iterateFrobenius, DirectedSystem), to_additive twins, pointed-newtype family, area-bucket artifacts (Filter/Tendsto and Matrix PosSemidef split across areas).

**Semantic-channel null result:** no semantic-only missing-abstraction candidate survives source adjudication over the mature stdlib — high-scoring semantic clusters are re-exports, propagation, generated twins, or label artifacts. Because independently re-derived constructions are renamed (image vs map), meaning vocabulary diverges exactly at the missing-abstraction boundary; exact type-shape blocking carries the signal in the mature corpus, while semantic leadership remains expected for under-developed frontier corpora. Artifacts: script/python/64_stdlib_semantic_analogies.py + verifier, 65_resolve_modules.py, data/stdlib_semantic_*, notes/64_stdlib_semantic_analogies_design.md.
## §18 — Script 66: orphan-functor falsification, 6/6 clean omissions, and the four-gate omission template (2026-09-23)

The script-64 orphan-functor candidates were falsified the hard way in a downstream-only Lean experiment (Mathlib untouched): for Sym2, WithBot, WithTop, OnePoint, Stream', Cycle the experiment registers Functor via the existing hand-written lift and LawfulFunctor. **All six compile, EXIT=0, zero-byte log, no sorry.** Five reuse functor laws already proved in Mathlib (Sym2.map_id/map_comp; WithBot/WithTop map_id/map_map; OnePoint map_id/map_comp; Stream' map_id/map_map); Cycle had a lift but no laws, and the two laws are proved in the experiment in six lines (Quotient.inductionOn', Cycle.map_coe, List.map_id/map_map). Probes ruled out diamonds: no reader Functor un alpha => Nat -> alpha exists at this toolchain; the Option aliases are semireducible defs (instance search cannot see Option's hierarchy through them, branches defeq); OnePoint continuity is orthogonal to a data-level Functor. The result is the second kernel-verified integration gap after PointwiseLift, now with a PR-shaped proposal (notes/66_pr_candidate.md, split PRs A-D, not submitted).

**False positives are the second output of the campaign and define what Atlas must not abstract:** (1) hypothesis-constrained lifts (CompactCoherentification.map, SummationFilter.map) are not plain functors; (2) alias-of-integrated-type (def F := Option) is conditional, not an automatic omission; (3) a lift without proved laws (Cycle pre-experiment) is an incomplete claim; (4) elaboration lookalikes (macroRules, Stx syntax decls, congr_simp) must be pre-filtered; (5) same-theory duplicates (cross-module re-exports, to_additive twins) are propagation/generation. These yield the **four-gate omission template** for future class-integration candidates: no instance already present; signature matches including universe levels; class laws present in source or proved; no extra hypotheses and no active diamond.

The map-family scan is frozen (notes/66_scan_freeze.md): no further map/map2/bind/pure family searches. The mature-stdlib result now stands on two adjudicated pillars — PointwiseLift (missing binary-lift concept) and the orphan-functor family (missing integration of an existing concept) — plus the semantic-channel null result (missing-abstraction signal in the mature corpus is structural; semantics carries propagation/renaming and leads for under-developed corpora). Next: discovery of a different phenomenon over the enlarged adjudicated dataset. Artifacts: script/lean/66_orphan_functor_falsification.lean, 66b_pi_functor_probe.lean, notes/66_orphan_functor_case_study.md, 66_pr_candidate.md, 66_scan_freeze.md.
## §19 — Scripts 67/68/69: vertical generalization ladders falsified; the instrumentation map (2026-09-23)

After the horizontal findings (PointwiseLift §17, orphan functors §18), the vertical axis was tested: same statement proved at redundant typeclass-strength levels. A coarse feature-based pass (67) produced 12,480 weakening pairs / 610 candidate ladders, but adjudication showed these are coarse-shape coincidences between unrelated statements — node counts cannot distinguish "same statement, weaker hypotheses" from "different statements of the same shape". The minimal instrumentation to close that boundary was built the hard way (Lean 68): a standing **conclusion-term layer** — forall prefix (binder tag + type term) plus conclusion as S-expressions, no proofs — 225,535 core-area rows, 0.55% flagged truncated, ~1.16 GB (roughly 60x smaller than full proof persistence 07).

The term-precise pass (69; verifier ALL CHECKS PASSED) canonicalizes statements by replacing instance-binder types with fixed holes (positions/de Bruijn indices preserved): 170,579 canonical theorem statements, 3,158 groups with multiple members, and **7 candidate ladders — every one an expected pattern after source adjudication**: parent projection constants (toNontrivial/toZPow), private implementation aliases of the same declaration (NormalBasis, Unramified), subclass dot-notation convenience lemmas (IsCancelSMul extends IsLeftCancelSMul, proved from the parent), a same-file local let (Krasner), and same-named theorems under genuinely different hypothesis regimes (FiniteDimensional E vs Finite index). **Null result: zero unclassified vertical ladders in the mature stdlib** — the assumption-weakening axis is already closed, reinforcing the "almost perfectly factored" headline.

The lasting artifact is the **instrumentation map**: horizontal parallel analogies detectable at coarse+semantic layers (PointwiseLift confirmed); class-integration gaps at coarse structural layer (6/6 orphan functors confirmed); vertical subsumption only at the conclusion-term layer (now built; null); proof-strategy convergence only with proof terms (07, not built); semantic leadership for incomplete frontier corpora (52). Atlas's false-positive ledger grows with six new classes (coarse-shape coincidence; sort-conclusion constructors; hierarchy projections; private aliases; subclass convenience lemmas; different-hypothesis same-name). Artifacts: script/python/67,69 + verifier, script/lean/68, notes/67_69_generalization_ladders_design.md, data/atlas_conclusion_terms.jsonl, data/{generalization,precise}_ladder_*. Next discovery must leave the "same shape" family — candidates: Equiv/transport gaps, proof-strategy skeletons on targeted slices, within-theory anomalies.
## §20 — Scripts 70–74: Equiv/transport decision gate — second audited null; declaration/API level provisionally saturated (2026-09-24)

The equivalence/transport axis was tested as a decision gate: where Mathlib already knows e : A ≃ B, does it fail to transport structure, and is a generic transport abstraction missing? Built entirely on the standing conclusion-term layer plus the edge file (no step-07 proof persistence): 1,135 plain-Equiv witnesses; 492 with two constructor carriers; 276 constructor pairs; 253 eligible after footprint/gap floors. The transported counterpart test holes instance-binder types and the two carrier constants and compares canonical keys; coverage = matched/min(keys). **232 of 253 pairs have coverage below 0.10 and only 9 exceed 0.35; none exceed 0.85 and there are no exact API mirrors** — Mathlib's Equivs are overwhelmingly one-off encodings/unpackings, not API identifications.

All nine gated pairs were Lean-falsified (script 72: EXIT=0, zero-byte log) and source-adjudicated: CStarMatrix is a defeq type copy of Matrix (ofMatrix = Equiv.refl, the copy exists to attach the operator norm; Matrix lemmas apply by conversion); ConnectedComponents/ZerothHomotopy coincide only under LocallyPathConnected (the Homeomorph was derived downstream in six lines — a convenience alias, not a missing mechanism); MaximalSpectrum is literally the subtype of maximal ideals, with its PrimeSpectrum Equiv conditional on Artinian and transport lemmas already present; the wreath product Equiv is an unpacking for cardinality; the remaining gated pairs are order/to_additive duals. **Adjudication of all 253: 124 representation_boundary, 122 false_positive, 7 intentional_asymmetry, zero missing_transport_lemma, zero missing_generic_abstraction.** A generic "transport everything" theorem cannot exist — every structure transport requires preserved-property proofs, necessarily class-by-class.

**Decision-gate outcome: no new kind of incompleteness; the Equiv axis is mostly null/existing machinery.** This is the second well-audited null at the declaration/type/API level (the first being vertical ladders §19). Per the two-positive/two-null rule — two positives (PointwiseLift §17; orphan Functors §18), two nulls (vertical §19; Equiv §20) — **declaration/type/API-level discovery over the mature stdlib is provisionally saturated**. Atlas's false-positive ledger gains five classes (defeq type copies; conditional quotient-relation equivalences; unpacking Equivs; head-constructor over-attribution; dual-side lemmas). Artifacts: script/python/70,71,73 + verify_equiv_experiment (ALL CHECKS PASSED), script/lean/72, notes/70_74_equiv_transport_case_study.md, notes/74_equiv_scan_freeze.md, data/equiv_*. The roadmap now climbs the representation ladder: targeted proof-strategy pilot on one mature area with a known shared-strategy positive control → strategy anomalies → within-theory anomalies → hypotheses → Lean verification.
## §21 — Scripts 75–76: proof-strategy pilot on Order — instrumentation validated, positive control recovered (2026-09-24)

Following the null Equiv gate (§20) and the provisional saturation of declaration/type/API-level discovery, Atlas climbed to the proof representation. The pilot tests whether "different theorem statements → same underlying proof strategy" is detectable from Lean's elaborated proof terms, with a known shared-strategy positive control required before scaling. Script 75 (one Mathlib load; theorems in Mathlib.Order; proof terms under 50k nodes) emits normalized skeletons whose vocabulary is derived from the terms themselves: leaves B/F/M/T and Ln/Ls; constants bucketed into REC (recursors/casesOn — induction/match), TOPROJ (toX parent projections), INST (instances), PRIV, and K(short name); structure A/L/Q/E/J; metadata dropped. EXIT=0; 26,828 skeletons (191 oversized proofs truncated), 140 MB — no step-07 full proof persistence needed.

The first clustering exposed an instrumentation-level phenomenon worth recording: 8,864 generated proof helpers (private _simp_1_n lemmas, inst _proof_n sub-proofs) independently re-prove the same small facts and create illusory mega-groups; they are filtered downstream with the raw data preserved. Over the remaining **17,964 real theorems**, two-level grouping (coarse tree shape with lemma identity, variables, instances and projection indices erased; named-lemma sub-keys within groups) yields 11,623 coarse groups, 3,285 multi-member. **The positive control is recovered: all 41 Fin interval lemmas — Set image, Finset image, Finset map, preimage; intervals Icc/Ico/Ioc/Ioo/Ici/uIcc; maps succ/castSucc/succEmb — land in a single coarse group**; source adjudication confirms every proof delegates to the generic addNat/castAdd/addNatEmb interval lemma (image_addNat_Ico .. etc.), so statements differ on five axes while the strategy is one. A secondary control (28 dualEquiv_functor/_inverse lemmas across the bundled order categories) is also recovered. The Order landscape itself: dominant shapes are one-line field extractions (95 members, 14 modules) and their two-hypothesis variant (69, 25 modules); REC induction is rare in Order; 8,338 singleton shapes show proof-term diversity is high — the opposite extreme from the near-perfect factoring at declaration level.

**Result: proof-strategy convergence is detectable; the instrumentation is accepted and Atlas now covers three representations (declarations, relations, proofs).** Next, per the pre-authorized roadmap: extract skeletons for all ten core areas in a single Lean compile and run cross-area strategy-anomaly ranking (exported strategies, cross-area shape overlap, within-area outliers), then within-theory anomaly ranking → hypotheses → Lean verification. Artifacts: script/lean/75, script/python/76 + verify_proof_strategy_pilot (ALL CHECKS PASSED), notes/75_76_proof_strategy_pilot.md, data/proof_skeletons_order.jsonl, data/proof_strategy_*_order.*.## 搂22 鈥?Scripts 77鈥?9: cross-area proof-strategy anomaly campaign 鈥?audited null; detectability boundary mapped (2026-09-24)

The validated Order instrumentation (搂21) was scaled to all ten core areas and pointed at the cross-area question: does a strategy common in one area appear anomalously inside another? Script 77 (one Mathlib load; resume support with append mode and name HashSet; flush every 2000 rows) extracts **282,971 theorem skeletons, 3.59 GB; 14,324 oversized proofs truncated**. Per area: Algebra 76,830; Analysis 40,027; Data 35,274; Topology 38,161; RingTheory 28,702; Order 26,828 (exactly cross-validates script 75); LinearAlgebra 16,887; GroupTheory 13,261; FieldTheory 4,126; Logic 2,875. Accepted EXIT=0 with zero warnings (String.trim deprecation fixed to trimAscii.toString; a resume rerun skipped all rows). A census finding: **116,023 of the raw rows are generated helpers** (private, ._proof_n, ._simp_n, instX.eq_n 鈥?the eq_n filter was added when instance sub-proofs dominated the first anomaly pass), leaving 166,948 real theorems.

Two granularities were tested. **Coarse (78):** 130,381 groups; gates size 鈮?2, one area 鈮?0% pure, spanning >1 area produce 40 exported-strategy groups and 50 outliers; source adjudication shows every one is a generic-shape coincidence (multi-lambda constructor/application shapes shared by unrelated lemmas 鈥?e.g. pointwise set-subset lemmas with interval membership lemmas 鈥?plus residual OrderDual instance derivations). Erasing named-lemma identity makes the coarse signature blind to strategy. **Fine (79):** full tree and all K tokens kept verbatim; 164,816 groups, only 108 spanning areas. All 108 were manually adjudicated with zero residual: 35 defeq copies or expected generics, 27 bundled-hom API propagation (add_apply/coe_zero/smul_apply/forget_map/鈥?across Seminorm/CLM/MultilinearMap/QuadraticMap/SchwartzMap/TestFunction), 17 private decidability fragments, 13 relation-class propagation, 7 instance fragments, 5 generated equation fragments (new patterns: sizeOf_spec, match congr_eq_n, sparseCases else_eq), 4 generic shape coincidences 鈥?**zero new exported strategies**.

**Verdict: one well-audited null at the cross-area exact-signature level.** Cross-area strategy borrowing does not surface beyond already-classified API propagation and generated fragments; the proof representation is not frozen (within-family convergence was positive). The lasting artifact is the **detectability boundary**: coarse exact signatures are too coarse (generic shapes), fine exact signatures are too strict (the Fin positive control itself has 41 distinct fine sub-keys 鈥?image_addNat_Ico vs finsetImage_addNat_uIcc); "same strategy, different lemma names" requires approximate matching (tree-edit distance, name-family stemming), which risks inventing vocabulary and was deliberately not built. Artifacts: script/lean/77, script/python/78,79 + verify_strategy_anomaly_campaign (ALL CHECKS PASSED), notes/77_79_strategy_anomaly_case_study.md, data/proof_skeletons_core.jsonl, data/strategy_*. Next decision is deliberate, not an auto-scan: within-theory anomaly ranking (roadmap Phase 4, local outliers vs mathematical neighborhood) versus building approximate skeleton matching.

## §23 — Scripts 80–85: within-theory anomaly ranking — audited null; proof representation now has two nulls; approximate matching strongly justified (2026-09-25)

Phase 4 tested the proof representation in its most favorable setting: not cross-area equivalence but *local abnormality inside a mathematically coherent neighborhood*. Scope: Order + Algebra, 62,003 real theorems after the canonical helper filter (Order 17,189; Algebra 44,814). Script 80 built five competing neighborhoods without choosing a winner: same namespace (3,016 groups), same module (1,592), (area, conclusion head, nPi/2) family (3,206), shared rare-dependency targets with document frequency 2–12 (24,432 rare targets; 14,451 theorems covered), and semantic nearest neighbors (7,165 covered). Script 81 went through three iterations: robust-z on heavy-tailed features in tiny modules produced 21k "anomalies" (rejected), and a transform-consistency bug that queried raw values against log-built percentile maps was found and fixed. The final v3 model converts heavy-tailed sizes via log1p to empirical percentiles pooled over scope and flags a dimension as locally anomalous only when the theorem percentile is ≥0.95 **and** its module peers' median percentile is ≤0.60; missing data is NA, never forced. A Stage A raw dump (23.2 MB) makes ranking reruns independent of the 3 GB edge file. Result: **2,102 theorems with any local anomaly (3.4%), 1,229 single-dimension**; per-dimension high: proof 537, dependency 426, semantic 235, type 168, generality 105, namespace 0.

Calibration (82) confirmed the detector mechanically works: known-unusual cases are recovered — Filter.map₂_assoc (PointwiseLift family) at 3.88 proof; bridge declarations MulMemClass.mul_mem 9.89 semantic, MonovaryOn.sum_smul_comp_perm… 9.48 proof, mul_lt_mul_of_pos_right 8.21, Int.cast_mul 8.15 proof, Subfield/Subring class instances 8.62/8.02 dependency — with a documented small-module false-positive rate (ordinary Fin card lemmas at 4.7–6.4). A 70-candidate single-dimension shortlist (14/dimension) was then checked against the Mathlib source (83); every candidate received a definite class, zero residual: category_api 14, expected_generic 14 (positivity/atom/involutive one-liners), bundled_equiv_api 11 (Equiv *_apply lemmas whose types must mention both carriers), generated_fragment 10 (new helper patterns: mk.inj/injEq, sizeOf_spec, hcongr, congr_simp), instance_artifact 6, legitimate_heavy_theorem 6 (MvPolynomial division-algorithm iff, fwdDiff Kronecker identity, atomise_empty, Quaternion lemmas, Fin.partialSum_contractNth), family_cluster 4 (the self-contained floor sub-family sharing its own rare lemmas), ext_api 2, class_field_api 2, expected_induction_principle 1.

**Verdict: a second well-audited null on the proof representation.** No ordinary-statement theorem hides a non-obvious connection; within-theory anomalies measure four expected things — theorem-weight peaks (the central proof of a file), family density (a self-contained sub-family inside a generic module), bundled API surface (Equiv application, instance fields, category limits, class fields), and residual generated fragments that name the next helper filters. Combined with §22, the instrumentation map is now precise: exact proof skeletons fail both globally (coarse = generic noise; fine = fragmentation — the Fin control itself splits into 41 keys) and locally (anomalies are weight and API surface, not hidden connections). The missing instrument — approximate structural matching (tree-edit distance, name-family stemming) over proof terms — is now strongly justified by two nulls rather than curiosity; it remains deliberately unbuilt and is the explicit decision for the next campaign given its engineering cost. Artifacts: script/python/80,81,83 + verify_within_theory_anomaly_campaign (ALL CHECKS PASSED), data/anomaly_{base,raw,scored}_order_algebra.*, data/anomaly_adjudication_shortlist.jsonl, data/neighborhood_summary.json, data/anomaly_ranking_summary.json, notes/80_85_within_theory_anomaly_case_study.md.
## §24 — Scripts 86–90: approximate proof-strategy matching — outcome C; structural mining of mature Mathlib closed (2026-09-26)

The last attempt to extract cross-theory proof strategies from the current proof representation was run as a hard-stop gate. Script 86 normalized the 282,971 raw skeletons (166,948 real theorems) into two layers — `norm` (leaves canonicalized, endpoint constants→P, coercion idioms→C, projection indices erased, lemma endpoint suffixes stemmed; theorem identity kept) and `core` (C/P pruned, app spines collapsed). Script 87 fixed the controls before any unknown search: 73 Fin interval wrapper proofs (the family that split into 41 fine keys in §22), 32 bundled category dualEquiv lemmas, and to_additive twins. Exact `core` match cannot reunite any family (40 distinct cores among 73; 32 among 32) with zero noise.

Two matcher designs were tested in 88. v1 blocked on ≥2 shared rare K stems (document frequency ≤20): 22,781 matches, but the gate failed (Fin 13%, Dual 3%, Twin 0.1%) — same-strategy proofs share common structure rather than rare lemmas. A direct probe then showed stemmed token-multiset cosine is 0.91–1.00 across the Fin family while fragment Jaccard splits to 0.05–0.20 across wrapper variants, so v2 blocked with a 64-bit Charikar simhash (8 bands × 8 bits; gates cos(T)≥0.80, cos(H)≥0.55). v2 produced 550,975 matches (264,035 cross-area) yet the gate still failed: Fin 20.5% coverage with the largest connected component 99.9% outsiders; Dual 6.2%; Twin 7.8%. Script 89 adjudicated 90 top/random cross-area samples plus a 400-pair census: **99.3–99.6% of shared tokens are generic idiom vocabulary**; the only rare-token matches (three pairs sharing `some_injective`) are the already-known option-tag family (OnePoint/WithTop/WithZero/WithOne from the §18 orphan-functor campaign). The concrete mechanism: small computational/decidability proofs normalize to identical generic shapes such as `(L KNat (A G V))` because the mathematical content sits in the statement and in private automation, not in the retained value.

**Verdict: outcome C — the normalized proof representation is inadequate for cross-theory strategy discovery at this extraction layer.** Rare-token views are precise but blind to shared strategy; common-token views recall slightly more only under catastrophic idiom flooding; no threshold regime separates shared mathematical strategy from shared Lean proof idiom, because that distinction requires statement semantics and the role of each referenced lemma, which the structural features do not encode. The proof representation is now exhausted at four settings (within-family positive at coarse granularity; cross-area exact signatures null §22; within-theory anomalies null §23; approximate matching outcome C here). Combined with the two-positive/two-null saturation at declaration/type/API level (§17–§20), the observability boundary of the mature, highly curated Mathlib corpus is comprehensively mapped: what humans have already factored, structural mining cannot rediscover beyond the two known families (PointwiseLift; orphan Functors/option tags).

**Strategic consequence (pre-authorized):** stop mining mature Mathlib for hidden cross-area relationships with declarations/proofs; no matcher tuning, no learned proof-tree embeddings (they would only obscure the idiom/strategy adjudication), no 70+ GB proof dump. The next campaign changes the data regime to underdeveloped/frontier corpora — where structure is unfinished and semantic methods have their predicted maximum leverage — rather than adding another representation of mature mathematics. Artifacts: script/python/86,87,88,89 + verify_approximate_strategy_campaign (ALL CHECKS PASSED), notes/86_90_approximate_strategy_case_study.md, data/proof_norm_core.jsonl, data/positive_controls.json, data/proof_matches.jsonl, data/control_gate.json, data/approx_match_*.