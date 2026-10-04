# Frontier arc — meta-analysis and revised findings (scripts 45–53)

Scope: a critical revision of the frontier work, not new extraction. Covers the
famous-problem footprint (45), unit-distance ingredient map (46),
degeneracy/planar gap analysis (47), the kernel-verified Lean gap-fills
(48–51, 53), the frontier analogy map (44), and the semantic donor-transfer
matcher (52). Every number below is read from the emitted `data/*.json`
summaries or from kernel-verified Lean logs.

Corpus: Mathlib pinned at `bbcd1968…`, **574,391 declarations / 8,287 modules /
32 areas / 16.3M reference edges**.

---

## 1. What the arc was testing

Two questions. (i) Can the Atlas instruments look at a *famous open problem* and
say, from formal structure alone, what is present, what is missing, and what
kind of work closing it is? (ii) Can the system then *do* that work and have the
Lean kernel check it? The arc deliberately moved from mapping (read-only) to
construction (theorem-adding Lean), per the "hard way" directive.

The pipeline that emerged is:

```
famous problem
   → formal footprint (named decls vs supporting machinery)     [45]
   → ingredient decomposition + module-anchored presence         [46]
   → classify each missing ingredient: assembly gap vs layer gap [47]
   → fill assembly gaps with kernel-verified Lean                [48–51,53]
   → independently route frontier material to mature donors      [44,52]
```

---

## 2. The discoveries, ranked by strength

### D1 — A validated gap taxonomy: *assembly gap* vs *layer gap*, with keyword
surface shown to be systematically misleading (the strongest result)

A missing ingredient is one of two structurally different things:

- **Assembly gap** — every primitive exists; only the theorem that assembles
  them is missing. Graph **degeneracy** was 5/7 assembled (degree,
  `neighborSet.card = degree`, subgraph/induce/delete, a minimum-degree vertex,
  coloring; only the elimination ordering and its edge bound absent).
- **Layer gap** — the foundational *objects* do not exist. **Planar graphs**
  were 3/6 at best (cycles/connected/trees present; plane drawing 0, faces 0,
  planar Euler 0); there is no embedding layer to even state `V−E+F`.

The decisive methodological finding: **raw keyword counts are anti-correlated
with formal presence here.** The five absent planar/incidence ingredients had
large name hits — crossing 327, degeneracy 446, Szemerédi 171, incidence 125,
planar 18 — but **zero in the expected modules**, every one a *false friend*
(martingale **upcrossing** vs graph crossing; Szemerédi **regularity lemma** vs
Szemerédi–**Trotter**; **nondegenerate** matrices vs graph **degeneracy**;
**coplanar** vectors vs **planar** graphs; `IncidenceAlgebra` vs geometric
incidence). Module-anchored formal matching was required to see this; keyword
search would have reported the layer as built.

This taxonomy was then **validated three independent ways**:
1. formal module-anchored matching (46/47);
2. actual construction — the assembly gap (degeneracy) closed with three
   kernel-verified files (48–50), while the layer gap (planar embedding)
   *could not* be closed by lemma-writing, exactly as predicted (51/53 prove
   only consequences behind an embedding interface);
3. independent semantic matching (52) reproduced the same zeros and the same
   false friends with no module anchoring at all (corpus "degeneracy" =
   simplicial `ExtraDegeneracy`; "crossing" = martingale `upperCrossingTime`).

A diagnostic that predicts in advance whether a gap is "write the lemma this
afternoon" or "build a foundational theory" is, in my assessment, the most
reusable thing the project has produced.

### D2 — A grounded readiness map for famous problems (formal, not reputational)

| problem | named decls | supporting machinery | verdict |
|---|---:|---:|---|
| Erdős unit-distance | **31** | 258 | most ready; object `SimpleGraph.UnitDistEmbedding` exists |
| Jacobian conjecture | **0** | **2,513** | machinery-only; hypothesis is literally `…jacobian_isUnit` |
| multicolor Ramsey | 0 | 837 | layer-blocked (no Ramsey module) |
| Collatz / Hailstone | 0 | 303 | layer-blocked (no `Hailstone`) |
| Navier–Stokes | 0 | 208 | layer-blocked (ODE only; no PDE layer) |
| FLT (control) | 305 | 280 | partly proved (`FLT.Three`, `FLT.Four`) — sanity check |

Unit-distance decomposes into 10 ingredients: **4 present** (unit-distance
object, Euclidean/inner-product plane, Turán, Zarankiewicz K_s,t), **1 partial**
(homological Euler characteristic, no planar `V−E+F`), **5 absent** (point-line
incidence, Szemerédi–Trotter, crossing number, planar graph, graph degeneracy).

The Jacobian result is especially pointed: **2,513 supporting declarations and
zero named results**, with the conjecture's exact hypothesis
(`Algebra.SubmersivePresentation.jacobian_isUnit`) already in the library. That
is the single best "deep machinery, absent theorem" target in the corpus.

### D3 — The frontier's dominant pattern is *re-deriving core generics*, not new
structure — and it independently re-discovers `PointwiseLift`

Both analogy instruments agree that frontier-to-core similarity is almost
always the **same abstraction specialized**, not a distant analogy:

- Script 44 shortlisted 73 cross-area groups: triage found **56
  `sharedHeadFamily`** (e.g. `ContMDiff*` ↔ `ContDiff*`, `HasMFDeriv*` ↔
  `HasFDeriv*`, `ShortExact` ↔ `Exact`, `IntegrableOn` ↔ `Integrable`) and 17
  wrapper variants, with **0 unresolved** — every high-similarity pair was an
  existing generic being replayed in a frontier setting.
- Script 52's top semantic donor pairs are the same shape
  (`ιChainComplex_d`↔`ChainComplex.mk_d`, `contMDiff`↔`contDiff`,
  `norm_compLp`↔`norm_sub`), and its donor flows are textbook-correct
  (Jacobian ← RingTheory/LinearAlgebra; unit-distance ← Topology isometries).
- Conspicuously, `SimpleGraph.Coloring.colorClass` semantically matches
  **`Set.image2`**, and the `compLp` lift is a pointwise binary lift — the
  **`PointwiseLift` abstraction found earlier in the stdlib is independently
  re-surfaced at the frontier.** Cross-validation from two unrelated sweeps
  makes PointwiseLift the strongest single "Mathlib is missing a unifying
  concept" signal in the project (with the informative boundary that `Group`
  does **not** lift).

This extends the earlier **strong null result** (the mature stdlib is so tightly
factored that four independent missing-abstraction detectors found essentially
nothing) into the frontier: even under-developed areas mostly *re-instantiate*
existing generics. The mineable seam is genericization of these specializations,
not discovery of wholly new patterns.

### D4 — The map→gap→construct→verify loop now produces kernel-verified
mathematics (end-to-end demonstration)

The assembly gap D1 predicted was actually closed, all `sorry`-free, exit 0 /
empty logs:

- **48** `DegeneracyAtMost k` inductive + edge bound `|E| ≤ k·|V|`;
- **49** greedy `(k+1)`-coloring, `χ(G) ≤ k+1` (confirmed absent: Mathlib has no
  degeneracy/greedy-coloring anywhere in `SimpleGraph`);
- **50** existence: every finite `n`-graph is `(n−1)`-degenerate (well-founded
  recursion on support size);
- **51** planar edge estimates `E ≤ 3V−6` and bipartite `E ≤ 2V−4` behind the
  Euler/face interface;
- **53** the **crossing lemma `cr ≥ E³/(64 V²)` for `E ≥ 4V`** (linear crossing
  bound + the `p = 4V/E` random-sampling amplification, constant `1/64`).

So every *numerical/combinatorial* consequence the unit-distance chain needs is
now proved; the single shared thing not built is the geometric/probabilistic
**interface** (a plane embedding/drawing that supplies faces + Euler, and
finite-expectation wiring). The work also doubles as a concrete, reviewable
Mathlib contribution (graph degeneracy coloring is standard and was missing).

### D5 — Semantic vs structural: the user's hypothesis is confirmed and bounded

Structural/AST matching cleanly *classifies* assembly gaps but cannot see a
layer that does not exist; semantic (role + meaning-vocabulary) matching still
fires on incomplete/opaque frontier declarations (52 matched 39.5% of thin
targets to a mature donor, including opaque-valued ones). But semantic matching
at the frontier mostly returns genericizations (D3), not distant analogies —
high word-overlap pairs are by construction closely related. Reaching genuinely
*far* analogies (the "two unrelated areas share a structure" dream) needs the
role-only channel or a learned embedding with weak lexical anchoring; lexical
semantic similarity alone tops out at donor-routing.

---

## 3. What is explicitly *not* a breakthrough (kept honest)

- **No new-to-humanity theorem or conjecture has been produced.** Scripts
  48–53 re-prove classical results (degeneracy coloring, planar bounds, the
  crossing lemma) that are absent from Mathlib; this is library-building / a
  Mathlib contribution, not a mathematical discovery.
- 51/53 prove arithmetic **consequences** behind an embedding/drawing and an
  expectation interface; the topological layer (rotation system on the sphere,
  faces, `V−E+F=2`) and the probability wiring are un-built. A rotation system
  encodes any orientable surface (`χ = 2−2g`); permutation signs give only
  parity, so the constant `2` genuinely needs a genus argument — it cannot be
  finessed by more arithmetic.
- The semantic instruments are **triage/routing and coverage detectors**, not
  conjecture generators. Their most reliable outputs are coverage zeros and
  "import machinery from area X" pointers.
- PointwiseLift remains refactoring-scale; it is the *strongest* abstraction
  signal, not a Fields-level structure.

---

## 4. Revised model of where discovery actually lives in Mathlib

The combined evidence (stdlib null result + frontier maps + verified fills)
partitions opportunity into three disjoint kinds, each needing a different
action:

1. **Layer gaps — construct, don't mine.** Planar graph topology, a PDE layer,
   Ramsey theory, Collatz/Hailstone. No similarity search will produce these;
   they are foundational objects with zero formal presence. This is where
   theorem-adding Lean (the 48–53 mode) has real scope, and where a verified
   contribution is most likely publishable as Mathlib work.
2. **Genericization of frontier specializations — the one mineable seam.**
   `ContMDiff*`/`ContDiff*`, manifold vs plain derivatives, pointwise lifts
   (`image2`, `map₂`, `colorClass`, `compLp`). PointwiseLift is the prototype;
   the 44/52 shortlists are a queue of further candidates. This is where
   automated abstraction *can* still fire in a mature corpus.
3. **Machinery-present/theorem-absent famous targets — conjecture work.**
   The Jacobian conjecture is the exemplar: 2,513 support decls, the exact
   hypothesis already named, zero theorems. This is the natural place to point
   hypothesis-generation (and, realistically, human collaboration), because the
   formal vocabulary to even state the problem already exists.

A practical output of the arc is therefore a **triage rule**: named hits with
zero in-module presence ⇒ suspect false friend; primitives present/theorem
absent ⇒ assembly gap (write it); objects absent ⇒ layer gap (build theory);
frontier decl mirroring a core head ⇒ genericization candidate; deep support
with zero named results ⇒ conjecture-ready target.

---

## 5. Recommended next moves, in priority order

1. **Point-line incidence + Szemerédi–Trotter (script 54)** — purely
   combinatorial accounting on top of the already-proved crossing lemma (53);
   reaches `I = O(n^{4/3} m^{2/3})` and then `u(n) = O(n^{4/3})`, completing
   the entire *arithmetic* spine of the unit-distance chain behind one
   geometric interface. Highest verified-math-per-effort.
2. **The plane-embedding layer itself** (rotation system → faces → Euler) if the
   goal is a genuine layer-gap fill rather than consequences — the hardest and
   most valuable Lean construction, and a real Mathlib contribution.
3. **Jacobian conjecture neighborhood** — apply the 45–47 ingredient treatment
   to the 2,513-support algebraic machinery around `jacobian_isUnit`; best
   conjecture-readiness target.
4. **Productionize PointwiseLift** and work the 44/52 genericization queue.

---

## 6. One-line status

The instruments cannot conjure new mathematics from a mature core, but they now
reliably (a) tell a write-theorem gap from a build-theory gap, (b) name the
exact mature machinery a frontier should import, and (c) close the write-theorem
gaps with kernel-verified Lean; degeneracy is finished, the planar/crossing
*consequences* are finished, and the frontier's recurring hidden abstraction is
pointwise lifting.
