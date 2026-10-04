# Note 61 — The "CW Euler formula" decision: what is on offer after script 59

This note lays out, concretely and against the **pinned Mathlib `bbcd1968`**, what
"attempting the CW Euler formula" would mean, what it would cost, what it would and
would not buy, and the alternatives. The decision is the user's; nothing in this
note presumes it.

## 1. The theorem in question

For a finite CW complex with `cₙ` cells of dimension n, the topological Euler
characteristic satisfies

```
χ_top(X) = Σₙ (−1)ⁿ cₙ,
```

and, for finite-type homology over a field, equals `Σₙ (−1)ⁿ dim Hₙ(X; k)`
(rank–nullity on the cellular chain complex). For the rotation-system surface,
`(c₀,c₁,c₂) = (V,E,F)`, which would identify our combinatorial χ with the
topological Euler characteristic of the realized surface — the missing arithmetic
bridge into note 60's realization theorem.

## 2. What the pinned Mathlib actually contains (verified by reading sources)

Present:

- **Singular chain complex and singular homology functors**
  (`AlgebraicTopology/SingularHomology/Basic.lean`, 2025); **H₀ computed**
  (`HomologyZero`, 2026, `singularHomology₀Iso` ≅ coproduct over path components);
  **homotopy invariance** (2026).
- **Eilenberg–Steenrod axiom framework** (`EilenbergSteenrod.lean`, 2026): the
  `HomologyPretheory` structure and axiom scaffolding — but singular homology is
  **not** yet shown to satisfy the axioms there.
- **Simplicial-set homology**: normalized chain complexes, homology, homotopy
  invariance, nondegenerate-simplex machinery
  (`SimplicialSet/Homology/*`), Dold–Kan.
- **Geometric realization functor** `SSet → TopCat` with its right adjoint the
  singular simplicial set (`SimplicialSet/TopAdj.lean`): `Δ[n]` homeomorphic to the
  standard simplex, `|Δ[1]| ≅ I`, counit-level API.
- **CW complexes**: abstract (categorical skeleta) and classical (explicit cells,
  attaching maps from metric spheres), finiteness classes `FiniteDimensional` /
  `FiniteType` / `Finite` with `finite_iff_finite_cells`, and the 1-skeleton as a
  graph (`CWComplex/Classical/Graph.lean`).
- **Homological Euler characteristic** of chain complexes as an alternating
  `finrank` `finsum`, with finite-support summation theorems
  (`Algebra/Homology/EulerCharacteristic.lean`, 2025).
- Fundamental groupoid and simply-connected predicates; model categories;
  abstract simplicial complexes (combinatorial only; no geometric realization
  file — geometric simplicial complexes do not exist yet).

Absent (grep-verified):

- **excision** for singular homology (the word appears only in the axiom file);
- the **long exact sequence of a pair** for singular homology;
- **cellular homology** and the cellular ≅ singular theorem;
- **homology of disks and spheres** (only H₀ exists; no suspension theorem);
- any **Euler characteristic in topology** (the chain-complex version is not
  connected to spaces or to CW cell counts);
- **surface topology of any kind**: no surfaces, no classification, no
  orientability, no triangulation-to-manifold theorem; no planar graph theory.

## 3. Three possible scopes (B, C, D) against the baseline (A)

### A. Stop at the cited gap — current state
55–59 kernel-verify the entire combinatorial spine; note 60 cites
Heffter–Edmonds–Youngs for realization. The extremal chain (51/53/54) stays a
theorem conditional on the standard, textbook geometric hypothesis.
**Cost: none. Risk: none. Paper-ready now with honest scoping.**

### B. General CW Euler formula in Mathlib
Statement: every finite CW complex satisfies `χ_top = Σ (−1)ⁿ cₙ`.
Required formalization that does not yet exist:
1. excision for singular homology (notoriously the hardest standard proof in the
   subject — barycentric subdivision / small chains), or a triangulation-based
   bypass;
2. long exact sequence for topological pairs;
3. cellular chain complex (free on n-cells) and the cellular ≅ singular homology
   theorem (uses 1+2 plus homology of `(Dⁿ,Sⁿ⁻¹)`);
4. homology of disks/spheres;
5. finite-type rank bookkeeping, then the existing chain-complex Euler theorem.
**Assessment:** stages 1–4 are a multi-author, multi-month (realistically
year-scale on a calendar) formalization campaign — the singular homology library
present today is itself a 2025–26 multi-author effort and stops exactly before
excision. It is genuine Mathlib infrastructure work, suitable as standalone PRs,
not as an Atlas script. **It does not itself realize a single rotation system as
a surface**; it only makes χ topological once such a realization exists.

### C. Chain-level Euler identity for rotation-system maps (bounded, no missing theorems)
Stay inside finite linear algebra over ℚ plus our permutation data:
1. from `(τ, σ)` and the face orbits of `φ = τσ⁻¹`, construct the **incidence
   boundary maps** ∂₁ : ℚ^E → ℚ^V (dart orientation gives head/tail) and
   ∂₂ : ℚ^F → ℚ^E (each face walk gives signed edge incidences); prove
   ∂₁∂₂ = 0 (face walks are closed) — a finite combinatorial check;
2. apply finite-dimensional rank–nullity (exists in Mathlib) to get
   `V − E + F = dim H₀ − dim H₁ + dim H₂` with Betti ranks computed by concrete
   matrices;
3. connectedness (script 58) gives `dim H₀ = 1`;
4. prove the combinatorial kernel lemma: for a connected rotation system the
   kernel of ∂₂ has dimension at most 1 (coherent orientation of all face disks
   from the cyclic rotations; this is the orientability content at the linear-
   algebra level), hence `χ = 1 − b₁ + b₂ ≤ 2`.
**Assessment:** stages 1–3 are routine matrix/finrank work; stage 4 is the one
real lemma but is elementary combinatorics over our permutations. Estimate
1–3 standalone scripts in the style of 48–59, with no missing Mathlib
prerequisites. Buys:
- a **second, independent kernel-verified proof of χ ≤ 2 / g ≥ 0** (linear
  algebra instead of transposition orbit counting);
- explicit **Betti numbers and incidence matrices per map** — new analyzable
  data for the Atlas discovery program (homological features per combinatorial
  surface);
- a ready-made **cellular chain complex** to plug into Mathlib's topology later,
  when realization/excision lands.
Does **not** buy topology: no manifold proof, no sphere, no discharged PlaneData.

### D. Full realization (note 60 stages 1–6)
B plus: triangulate the rotation gluing into a finite simplicial set (the
realization functor itself exists), prove the realization is locally Euclidean
(vertex links are circles), prove orientability, prove classification of
compact orientable surfaces or at least χ = 2 ⇒ S², identify the 1-skeleton with
the graph, stereographic transfer to ℝ².
**Assessment:** the manifold-link and classification stages are research-grade
topology formalization on top of B; year-scale, effectively contributing
surface theory to Mathlib. Not compatible with a two-month paper timeline.

## 4. Recommendation

- For the two-month paper: **A** (declare the frontier combinatorially closed,
  cite realization), optionally **C** first — C is bounded, needs no missing
  theorems, materially strengthens the results (two independent formal proofs;
  Betti/incidence features), and is the natural "hard way" extension that stays
  inside what the kernel can currently certify.
- **B and D are post-paper Mathlib-infrastructure campaigns**, worth doing as
  deliberate upstream contributions (B's first milestone, long exact sequence +
  excision for singular homology, is itself a paper-scale formalization project).
- C is also the correct substrate for B: when Mathlib later has cellular
  homology, the chain complex from C is exactly the object it computes with.

## Decision requested

1. **A only** — frontier closed at the cited boundary; move to paper/meta work.
2. **A + C** — additionally build the incidence/chain-complex layer and the
   second algebraic χ ≤ 2 proof (recommended bounded extension).
3. **B** — commit to the general CW Euler formula campaign (long; upstream
   Mathlib work; no near-term payoff to the frontier thread).
4. **D** — full topological realization (longest; includes B and surface
   classification).
