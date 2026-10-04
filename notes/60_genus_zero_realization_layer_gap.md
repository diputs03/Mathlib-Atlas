# Note 60 — Genus-zero topological realization: the terminal layer gap (honest scoping)

Status: **scoping / citation note, not a kernel-verified theorem.** Scripts 48–59 are
kernel-verified Lean (exit 0, empty logs, no `sorry`); the present note states exactly
where the combinatorial spine ends and genuine topology begins, what the pinned
Mathlib (`bbcd1968`, Lean v4.34.0-rc2) provides toward the missing theorem, and what a
kernel-verified realization would cost. Nothing here is asserted as proved inside
Lean beyond the explicitly listed scripts.

## 1. The theorem that remains unproved in Atlas

The **rotation-system embedding theorem** (Heffter–Edmonds–Youngs):

1. Let a finite graph (loops and multiple edges allowed) be given by a finite set of
   darts, a fixed-point-free involution `τ` pairing the two darts of each edge, and a
   permutation `σ` cyclically ordering the darts around each vertex. Then there exists
   a **2-cell embedding** of the graph in a closed orientable surface `S` whose facial
   boundary walks are exactly the cycles of `φ = τσ⁻¹` (equivalently `σ⁻¹τ`, depending
   on convention).
2. `S` is constructed by thickening the graph into an oriented ribbon surface and
   capping each boundary component with a disk (or, equivalently, by the standard
   polygon gluing determined by the rotation system).
3. For a connected embedding, `χ(S) = V − E + F`, where V/E/F are the orbit counts of
   `σ`, `τ` (half the darts), and `φ`, and `S` is the orientable surface of genus
   `g = (2 − V + E − F)/2`.
4. Conversely, every cellular embedding of a graph in an orientable surface induces
   such a rotation system, and the two constructions are inverse up to isomorphism
   (rotation systems and orientable 2-cell embeddings are in bijection).
5. By the classification of compact connected orientable surfaces, `χ = 2` iff
   `g = 0` iff `S ≅ S²`; and `S² \\ {pt} ≅ ℝ²` (stereographic projection), so a
   connected rotation system with `χ = 2` realizes a planar embedding.

Part 3's *arithmetic* is exactly what scripts 55–59 prove combinatorially (parity of
χ for every map in 56; `χ ≤ 2` for connected maps in 59). Parts 1, 2, 4 and the
topological halves of 3 and 5 are **not** proved in Atlas and are not in Mathlib at
the pinned commit.

## 2. What is kernel-verified in Atlas (the combinatorial side)

| Result | Script | Statement |
|---|---|---|
| degeneracy edge bound; greedy (k+1)-coloring; every finite n-graph (n−1)-degenerate | 48–50 | combinatorial graph theory, unconditional |
| planar edge bounds behind a `PlaneData` Euler/face interface (`e ≤ 3v−6`, `e ≤ 2v−4`) | 51 | conditional on the plane axioms |
| crossing lemma | 53 | conditional on 51's planar bound |
| multigraph crossing lemma → incidence bound → Szemerédi–Trotter → unit distance `u(n) ≤ 9 n^(4/3)` | 54 | conditional chain on `PlaneData` |
| combinatorial planar maps, Euler `v + f = e + 2` by induction; unconditional edge bounds | 55 | proved inside the map structure |
| dart/rotation-system model; V/E/F as permutation orbit counts; `2E = #darts`; **χ even for every map**; integer genus `χ = 2 − 2g`; genus-zero seeds (link, loop on `Fin 2`) | 56 | proved |
| transposition split/join orbit lemma (`±1`, adjacent split and fixed-point join) | 57 | proved |
| connectedness = transitivity of `⟨τ, σ⟩`; explicit walk relation; primal–dual group identity; seeds connected | 58 | proved |
| general same-cycle split (+1), distinct-cycle join (−1), universal `≤ +1`; involution→disjoint-transposition factorization; spanning-tree growth `connected_growth`; **connected `χ ≤ 2`**; **`genus ≥ 0`** | 59 | proved |

So: every purely permutation-combinatorial ingredient of the Euler characteristic
story — orbit counting, parity and integrality, connectedness, the genus bound — is
kernel-verified, as is the entire downstream extremal chain (edge bounds, crossing
lemma, Szemerédi–Trotter, unit distance) *modulo the standard geometric hypothesis
packaged as `PlaneData`*.

## 3. What Mathlib supplies at commit `bbcd1968` (verified by reading the files)

Present and reusable:

- `Mathlib.Combinatorics.SimpleGraph.Dart` — a dart as an ordered adjacent vertex
  pair (half-edge). This is terminology/data only: there is no edge involution acting
  on darts and no vertex rotation.
- `Mathlib.Topology.CWComplex.Abstract.Basic` — categorical relative CW complexes via
  skeleta and disk attachment (`RelativeCWComplex`, `CWComplex`).
- `Mathlib.Topology.CWComplex.Classical.Basic` / `Finite` — classical CW complexes
  with explicit cells, attaching maps from metric spheres into unions of closed
  cells, cell frontiers/closed cells, and the finite variant.
- `Mathlib.Topology.CWComplex.Classical.Graph` — the 1-skeleton of a CW complex as a
  graph (`CWComplex.OneSkeletonGraph`, 2026).
- `Mathlib.Topology.Category.TopCat.Sphere`; manifold theory including
  `Geometry.Manifold.WhitneyEmbedding`.
- `Mathlib.Algebra.Homology.EulerCharacteristic` — the Euler characteristic of a
  homological complex as an alternating `finrank` sum (2025).

Absent (grep + file inventory):

- rotation systems, combinatorial maps in the topological-graph-theory sense, ribbon
  graphs, edge involutions on darts (`SimpleGraph.Maps` is about maps *between
  graphs*, i.e. homomorphisms — unrelated);
- any polygon-gluing / disk-capping construction of a surface from permutation data,
  and any theorem that the quotient is locally Euclidean (a 2-manifold);
- orientability derived from a rotation system;
- **classification of compact surfaces** (no `Surface` theory at all; no
  "χ = 2 ⇒ sphere");
- the CW Euler formula `χ = Σ_k (−1)^k c_k` connecting finite CW cell counts to the
  homological Euler characteristic (the two halves exist independently and are not
  linked);
- planar graph theory: "Planar graphs" appears only as a TODO section header in
  `Combinatorics/SimpleGraph/Coloring/Vertex.lean`; no planarity predicate, no
  Kuratowski/Wagner criterion, no rotation-system–planarity equivalence;
- stereographic projection used as a sphere/plane embedding transfer in this setting.

## 4. What kernel-verified realization would require (staged)

1. **CW Euler formula.** For a finite CW complex, prove the alternating cell-count
  sum equals the homological Euler characteristic (finiteness, cellular homology,
  rank-nullity alternating sum). The two libraries this would connect both exist;
  this is the most tractable stage and is itself a substantial standalone Mathlib
  contribution.
2. **The rotation-system surface.** From `(τ, σ)` construct the quotient/ribbon
  space (vertex disks + edge bands + face disks, or polygon gluing), and prove it is
  a compact, connected, Hausdorff 2-manifold without boundary — the local-disk
  argument at vertices is the geometric core of the Heffter–Edmonds construction.
3. **Orientability.** Prove the rotation-system surface is orientable (consistent
  disk/band orientations from the cyclic orders); nonorientable embeddings require
  the extra "signature" data, whose absence here is what guarantees orientability.
4. **Classification, or the weak χ = 2 lemma.** Either formalize the classification
  of compact connected orientable surfaces (a large theorem), or prove just
  "connected orientable closed surface with χ = 2 is homeomorphic to `S²`" — still a
  genuine topology theorem (triangulate, reduce to polygon normal form).
5. **Graph correspondence.** Identify the embedded 1-skeleton with the original
  `SimpleGraph` (loops/multiedges via darts) and the face boundary walks with
  `φ`-orbits, so that V/E/F from script 56 equal the CW cell counts of stage 1.
6. **Plane transfer.** Stereographic projection `S² \\ {pt} ≅ ℝ²` to turn the
   sphere realization into a planar drawing, discharging `PlaneData` for 51/53/54.

Stages 2 and 4 are each research-grade formalization projects (comparable in scope
to existing multi-thousand-line Mathlib topology developments); stages 1 and 6 are
mechanical relative to them. This is not a single Atlas script, and the standing
"hard way" rule (no `sorry`, empty logs) is precisely why it should not be *asserted*
from the permutation model.

## 5. Logical status of the extremal chain after 59

- `e ≤ 3v−6`, `e ≤ 2v−4`, the crossing lemma, Szemerédi–Trotter and
  `u(n) ≤ 9 n^(4/3)` are theorems of the form **"given plane data satisfying the
  Euler/face axioms, the bound holds"** — fully kernel-verified conditional results.
- Scripts 55–59 prove that the combinatorial content of those axioms (orbit counts,
  parity, connected Euler bound) holds for every combinatorial map with no geometry.
- The only undischarged hypothesis is the geometric realization of stage 5(1)–(2)
  above — the standard, textbook Heffter–Edmonds–Youngs theorem, cited rather than
  formalized. Nothing in the chain depends on an unproved *combinatorial* claim.

## 6. Frontier-section closure statement

With script 59 green and this note on record, the frontier section's combinatorial
program is **finished**: the layer-gap classification of scripts 45–47 (planar graph
theory absent from Mathlib as a *realization* layer) has been filled everywhere it can
be filled by permutation combinatorics, and the single residual gap is identified
with a named classical theorem whose formalization is independent topology work.
Consistent with the project's correctness boundary (Atlas proposes; the Lean kernel
disposes), the realization is cited, not simulated.

## References (the realization theorem and its machinery)

- L. Heffter, *Über das Problem der Nachbargebiete auf einer Fläche*, Mathematische
  Annalen 50 (1898).
- J. Edmonds, *A combinatorial representation for polyhedral surfaces*, Notices of
  the American Mathematical Society 7 (1960), 646.
- J. W. T. Youngs, *Minimal embeddings and the genus of a graph*, Journal of
  Mathematics and Mechanics 12 (1963), 303–315.
- G. Ringel, *Map Color Theorem*, Grundlehren der mathematischen Wissenschaften 209,
  Springer, 1974.
- J. L. Gross and T. W. Tucker, *Topological Graph Theory*, Wiley-Interscience, 1987
  (Dover reprint 2001): rotation systems ↔ orientable 2-cell embeddings.
- A. Hatcher, *Algebraic Topology*, Cambridge UP, 2002: classification of compact
  surfaces and the CW Euler characteristic (§0, §2.2).
- W. T. Tutte, graph embeddings and combinatorial maps (the permutation-pair model
  `(τ, σ)` with faces as `τσ⁻¹` orbits), e.g. *Graph Theory as I Have Known It*,
  Oxford, 1998.
