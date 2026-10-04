# Planar / combinatorial-map frontier — freeze note

**Date:** 2026-09-22.
**Decision being recorded:** option **A + C** of note 61 — accept the single cited
topological gap (A) and build the chain-level incidence layer (C, script 62) — then
**freeze** the planar frontier and return to core Atlas discovery.

This note is the terminal index for the planar/combinatorial-map thread
(scripts 48–62). It states exactly what is kernel-verified, exactly what is
discharged by citation, and why the thread stops here.

## 1. The layer table (every "proved" row is kernel-verified, empty compile log)

| Layer | Result | Script |
|---|---|---|
| Graph degeneracy API | degeneracy / k-degenerate / coloring hooks grounded in Mathlib | 48 |
| Degeneracy ⇒ colorability | k-degenerate ⇒ (k+1)-colorable | 49 |
| Peeling existence | every finite graph admits a degeneracy peeling | 50 |
| Planar edge bounds | conditional on Euler: e ≤ 3v−6, e ≤ 2v−4 (triangle-free) | 51 |
| Crossing lemma | crossing number lower bound from the planar edge bound | 53 |
| Point–line incidence | Szemerédi–Trotter-type incidence bound | 54 |
| Unit distances | u(n) = O(n^{4/3}) from incidence | 54 |
| Combinatorial maps (v1) | dart/α/σ/φ model, orbit counts V/E/F, genus-zero Euler | 55, 56 |
| Transposition orbit change | same-cycle cut (+1) and two-cycle join (−1); universal ≤ +1 | 57 |
| Map connectedness | vert group = face group; connectedness self-dual | 58 |
| Connected Euler bound (proof 1, combinatorial) | connected χ ≤ 2, genus g ≥ 0, via spanning-tree growth | 59 |
| Frontier semantic scan | 1,781 frontier targets / 3,698 stdlib donor pairs (Python, stdlib only) | 52 |
| Incidence chain complex (proof 2, algebraic) | ∂₁, ∂₂ over ℚ; ∂₁∂₂ = 0; b₀ = b₂ = 1; χ = 2 − b₁ ≤ 2 | **62** |

Scripts 45–47 are the footprint-mapping Python passes (graph degeneracy = assembly
gap; planar graphs = layer gap) that motivated the thread; 60 and 61 are scoping /
decision notes with no code by design.

## 2. What script 62 adds (option C, complete)

Over the map model (darts α; fixed-point-free edge involution τ; vertex rotation σ;
face permutation φ = τσ⁻¹ with φσ = τ), script 62 constructs

    C₂ = ℚ^F ──∂₂──▶ C₁ = ℚ^E ──∂₁──▶ C₀ = ℚ^V,

proves ∂₁∂₂ = 0 by corner telescoping, derives the Euler–Poincaré identity
χ = b₀ − b₁ + b₂ by rank–nullity, and computes for connected maps
**b₀ = 1** (left kernel of ∂₁ = constant vertex functions) and
**b₂ = 1** (kernel of ∂₂ = constant face functions, propagated across edges via
the conjugated τ′ and the group identities φ(τ′φ⁻¹) = τ and σ = φ⁻¹τ). Hence
**χ = 2 − b₁ ≤ 2**, a second, purely linear-algebraic proof of the bound of 59,
with explicit Betti ranks. The empty map is handled separately (χ = 0).

The terminal planar inequality now has **two independent kernel-verified proofs**:
combinatorial (59) and algebraic (62).

## 3. The single residual gap (option A, discharged by citation)

Nothing in 48–62 proves that a connected χ = 2 rotation system is *topologically
realized* by a cell decomposition of the sphere. That is the
**Heffter–Edmonds–Youngs rotation-system embedding theorem**: a rotation system
determines a 2-cell embedding in a closed orientable surface whose faces are the
φ-orbits, with χ = V − E + F and genus g = (2 − χ)/2; connected χ = 2 is the
sphere, and stereographic projection gives the plane.

Why it is cited rather than proved (inventory of pinned Mathlib `bbcd1968`,
details in note 60): Mathlib has classical/abstract/finite CW complexes,
`TopCat.Sphere`, manifolds/Whitney, and an abstract homological Euler
characteristic, but has **no** rotation-system→surface gluing construction, no
2-manifold proof for such a gluing, no orientability-from-rotations, no surface
classification (no surface theory at all; "Planar graphs" is a TODO header), no
CW cell-count → homological Euler formula, no planarity/Kuratowski, and no
sphere→plane transfer. Note 61 stages the work and prices it:

- **Option B** (general CW Euler formula) needs excision, the long exact sequence
  of a pair, cellular homology, and disk/sphere homology — a multi-month/year
  upstream Mathlib campaign, and it realizes nothing by itself.
- **Option D** (full realization) is B plus ribbon gluing with a local-Euclidean
  proof, orientability, surface classification or a weak χ = 2 lemma, graph
  correspondence, and stereographic transfer — year-scale.

Both are **parked**, not silently assumed. Every result in the table is conditional
only on this one named, textbook theorem, which is explicitly cited
(Heffter 1898; Edmonds, Notices AMS 7 (1960), 646; Youngs, J. Math. Mech. 12
(1963), 303–315; Ringel 1974; Gross–Tucker 1987; Hatcher 2002).

## 4. Why freeze here

1. **Both proofs of the terminal combinatorial bound are done.** Further planar
   work has diminishing discovery return for Atlas; the open surface topology is an
   upstream formalization campaign, not a discovery experiment over Mathlib.
2. **The frontier scan (45–47, 52) already delivered its strategic finding:**
   famous open problems hit *assembly* and *layer* gaps — missing glue and missing
   intermediate theories — rather than missing computational steps. The planar
   thread built one complete layer stack end to end as the reference case; that is
   enough to characterize the gap class.
3. **The user-directed center of gravity returns to the mature standard library**,
   which is far more developed than frontier areas and therefore yields denser
   structural signal, and to **semantic as well as structural** similarity
   (incomplete/undiscovered structure will not yet share complete structure).

## 5. State handed back to core Atlas discovery

- Headline positive new-abstraction signal from the stdlib thread:
  **PointwiseLift** (`Set.image2` and `Filter.map₂` are the same pointwise binary
  lift), with a strong companion null result (the mature stdlib is almost perfectly
  factored; repeated binary lifts are the one systematic duplication found).
- Corpus instrumentation in place: 574,391 Mathlib declarations, 8,287 modules,
  32 top areas, 16,316,230 distinct labeled reference edges; raw Expr preserved;
  provenance from the environment; edge labels kept separate.
- The persistent raw-corpus build (planned step 07, full proof-term persistence
  ~70+ GB) and production PointwiseLift remain the two largest parked engineering
  items; discovery experiments can extend the existing feature/edge data without
  waiting on 07.

**Frozen scope:** no new planar/frontier Lean unless explicitly reopened. Any future
work on B/D is tracked as an upstream-Mathlib effort, not an Atlas discovery task.
