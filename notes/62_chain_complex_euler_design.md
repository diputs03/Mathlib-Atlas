# Script 62 — Incidence chain complex of a combinatorial map, Betti ranks, and the algebraic χ ≤ 2 proof

**Status:** kernel-verified, `lake env lean script\lean\62_incidence_chain_complex.lean` exits 0 with an **empty log** (no errors, no warnings, no `sorry`).
**File:** `script\lean\62_incidence_chain_complex.lean`
**Namespace:** `SimpleGraph.MapChain`
**Toolchain:** Lean `4.34.0-rc2`, Mathlib pinned at `bbcd1968ee6950abe88b85dba6995da346c4b2a8`.
**Supersedes:** the earlier draft `script\lean\62_chain_complex_euler.lean` (namespace `SimpleGraph.ChainEuler`, ~50 errors, abandoned); this file is the canonical script 62.

## 1. Purpose

Scripts 55–59 proved the genus-zero Euler bound `χ = V − E + F ≤ 2` for connected
combinatorial maps **combinatorially** (orbit counting plus a spanning-tree growth
argument). Script 62 gives a second, independent, purely **linear-algebraic** proof
by constructing the cellular chain complex over `ℚ`

```
C₂ = ℚ^F  ──∂₂──▶  C₁ = ℚ^E  ──∂₁──▶  C₀ = ℚ^V
```

and computing every Betti rank for a connected map:

| rank | value | meaning |
|---|---|---|
| `b₀ = card V − rank ∂₁` | **1** | one connected component |
| `b₁ = card E − rank ∂₁ − rank ∂₂` | `2 − χ` (≥ 0) | independent cycles / genus×2 for orientable surfaces |
| `b₂ = card F − rank ∂₂` | **1** | one 2-cycle class (the sphere) |

The Euler–Poincaré identity `χ = b₀ − b₁ + b₂` then gives `χ = 2 − b₁ ≤ 2`,
with `b₁ ≥ 0` from rank–nullity. The empty map (`IsEmpty α`) is handled
separately: `V = E = F = 0`, so `χ = 0 ≤ 2`.

This is the **algebraic half** of a future homology identification: it builds the
incidence boundary maps, proves `∂₁ * ∂₂ = 0`, and computes the ranks without any
topological realization. The remaining half (showing this chain complex computes
the homology of the realized surface — the Heffter–Edmonds–Youngs rotation-system
realization theorem) is the cited terminal layer gap scoped in note 60.

## 2. Combinatorial model

A `Map α` (finite type `α` of darts with decidable equality and a linear order)
packages:

- `edge : Perm α` (`τ`), a fixed-point-free involution (`edge ^ 2 = 1`,
  `edge x ≠ x`);
- `vert : Perm α` (`σ`), the vertex rotation.

Derived:

- `face := edge * vert⁻¹` (`φ`), with the corner identity **`φ * σ = τ`**
  (`face_mul_vert`);
- vertex orbit index type `V` over canonical `vert`-orbit representatives;
- edge index type `E` over `edgeReps := univ.filter (d ≤ edge d)` (one dart per
  edge orbit; `2 * card edgeReps = card α`);
- face orbit index type `F` over canonical `face`-orbit representatives.

`V/E/F` are `abbrev` subtypes so that `Fintype`/`DecidableEq` synthesis flows
through them; a plain `def` blocks instance synthesis.

### Orbit layer (map-independent)

`cyc f z` is the carrier of the cycle of `f` through `z`: the `cycleOf` support
for non-fixed points, and the singleton `{z}` at a fixed point, so every orbit has
a nonempty carrier with an `IsCycleOn` action. `repOf f z` is the least element of
the carrier (`Finset.min'`), giving a canonical representative per orbit;
`reps f` is the finset of fixed representatives, and `reps_card` identifies its
cardinality with the permutation orbit count (nontrivial `cycleFactorsFinset`
cycles plus fixed points).

## 3. Boundary maps

- **`d1 : Matrix V E ℚ`**: column `e` is `+1` at `vRep(edge e)` and `-1` at
  `vRep(e)`; a loop gives the zero column automatically. `d1_transpose_mulVec`
  evaluates a transpose product as a difference of the two endpoint vertex
  values.
- **Corners.** A corner is a dart `c`; `occEdge c` is the edge orbit met there
  (via `edgeRepOf (vert⁻¹ c)`) and `occSign c ∈ {+1, −1}` records orientation.
  The key local identity `corner_column c v` says the signed `∂₁` column at a
  corner equals the indicator of `vRep(face c)` minus the indicator of
  `vRep c` — i.e. one directed step along the face walk.
- **`d2 : Matrix E F ℚ`**: column `f` sums the signed edge corners around the
  face carrier `cyc face f`.

`d1_mul_d2 : d1 * d2 = 0` selects, for each corner, its unique edge column,
replaces it via `corner_column`, and telescopes: the sum of
`indicator(vRep(face c)) − indicator(vRep c)` around a face orbit equals the sum
over `Finset.image face carrier`, which is the same carrier (`cyc_image`).

## 4. Rank–nullity and the Betti ranks

`range ∂₂ ≤ ker ∂₁` follows from `∂₁∂₂ = 0`
(`Matrix.mulVec_mulVec`). Rank–nullity
(`LinearMap.finrank_range_add_finrank_ker`) plus `Submodule.finrank_mono` gives
`r₂ ≤ card E − r₁`, hence `b₁ ≥ 0`, and the Euler identity
`χ = b₀ − b₁ + b₂` is algebra.

### b₀ = 1 (left kernel of ∂₁)

`ker ∂₁ᵀ` is characterized as the constant vertex functions:

- constants lie in the kernel because each `∂₁` column sums to zero;
- a kernel element `y` gives, for every edge, equality of the values at its two
  endpoints; the relation is propagated from edge representatives to all darts
  using `edge_image_edgeReps` (τ bijects `edgeReps` with its complement), then
  along vertex rotations, and `connected_invariant_constant` forces one value.

`finrank_span_singleton` then gives `finrank ker ∂₁ᵀ = 1`; rank–nullity on
`∂₁ᵀ` and `Matrix.rank_transpose` give `r₁ = card V − 1`, so **`b₀ = 1`**.

### b₂ = 1 (kernel of ∂₂)

`ker ∂₂` is characterized as the constant face functions:

- constants are killed because each edge has exactly two corners
  (`occEdge_eq_iff`), with opposite signs (`occSign_vert_edgeRep = +1`,
  `occSign_vert_edge = −1`);
- for a kernel element `x`, set `z d := x(fRep d)` (face-invariant). The
  ∂₂-closedness, expanded over the face-carrier partition
  (`face_sum_univ`, from pairwise-disjointness and coverage of the
  `cyc face` carriers) and reduced per edge (`sum_occEdge`), forces
  `z(σ e) = z(σ(τ e))` for every edge orbit.
- This relation lives on edge representatives. Conjugating, define
  `τ' d := σ(τ(σ⁻¹ d))`; the two-dart characterization `edgeRepOf_eq_iff`
  extends `z(τ' d) = z d` to **all** darts.
- Group identities then recover invariance under both generators from face
  invariance: the conjugation identity
  `φ (τ' (φ⁻¹ d)) = τ d` (proved from `φσ = τ` and `τ² = 1`) gives
  `z(τ d) = z d`, and `σ = φ⁻¹ * τ` (from `φσ = τ`) gives `z(σ d) = z d`.
- `connected_invariant_constant` forces `z`, hence `x`, to be constant.

Thus `finrank ker ∂₂ = 1`, rank–nullity gives `r₂ = card F − 1`, and
**`b₂ = 1`**.

### Final theorems

- `euler_betti`: `card V − card E + card F = b₀ − b₁ + b₂` (all maps);
- `b0_eq_one`, `b2_eq_one`, `euler_betti_connected` (`χ = 2 − b₁`),
  `euler_le_two` (`χ ≤ 2`) for connected nonempty maps;
- `euler_le_two_empty` for `IsEmpty α`.

## 5. Lean 4.34.0-rc2 / Mathlib API notes (verified)

- `SameCycle f x y` is the integer form `∃ i : ℤ, f^[i] x = y`; adjacent points
  are witnessed by `⟨1, by simp⟩` / `⟨-1, by simp⟩`.
- Never `rw` under `Finset.min'` (the dependent `Nonempty` proof breaks); use
  `simp only [repOf, …]`.
- `Finset.sum_biUnion` takes a `Set.PairwiseDisjoint (↑s) t` hypothesis (not a
  `Finset.Pairwise`), and states union-sum = family-sum, so the partition
  identity uses `rw [← Finset.sum_biUnion …, cover]`.
- `Finset.sum_filter` converts indicator sums to filtered sums (direction
  matters; use `←`).
- `Finset.sum_mul` / `Finset.mul_sum`: sum on the left vs right of the scalar.
- `Matrix.mulVec_mulVec x A B : A.mulVec (B.mulVec x) = (A*B).mulVec x`
  (vector argument first).
- `Matrix.rank_transpose`; `Matrix.rank A = finrank (range A.mulVecLin)`;
  `LinearMap.finrank_range_add_finrank_ker` (dot notation);
  `Submodule.finrank_mono`; `finrank_span_singleton hv`;
  `Module.finrank_fintype_fun_eq_card ℚ`.
- `if_pos`/`if_neg` are deprecated: use `ite_eq_left` / `ite_eq_right`.
- `Subtype.eq` is deprecated: use `Subtype.ext`.
- `simp only […] at v.property` is illegal ("expected single reference to
  variable"): copy the hypothesis to a named `have` first.
- Structure fields must be explicit parameters; index types must be `abbrev`;
  use `e.val` for subtype projections.
- Dead `rfl`/`ring` after a closing `simp`/`rw` trigger unreachable-tactic
  warnings; `<;>` vs `;` triggers the seq-focus style linter. The acceptance bar
  is a zero-byte log, so every warning must be cleared.
- `Fintype.card_eq_zero_iff.mpr (by infer_instance)` discharges the empty
  index-type cases.

## 6. Scope and relation to the rest of the Atlas frontier thread

- What is proved here is entirely combinatorial/linear-algebraic over the map
  model: boundary maps, `∂² = 0`, ranks, Betti numbers, the algebraic Euler
  bound. No topology is assumed.
- Identifying these ranks with surface homology still requires the rotation-system
  realization theorem (note 60). Script 62 is exactly the chain-complex layer that
  such a realization theorem would connect to, and it independently re-derives the
  bound of script 59, so the planar-frontier layer table now has both a
  combinatorial and an algebraic proof of its terminal inequality.
