# Script 59 — Connected maps satisfy χ ≤ 2 and genus ≥ 0 (design note)

File: `script/lean/59_connected_euler_bound.lean`
Namespace: `SimpleGraph.SwapOrbit`
Status: **kernel-verified** — `lake env lean script/lean/59_connected_euler_bound.lean` exits `0`,
`notes/59_connected_euler_bound.log` is empty (0 bytes), no `sorry`, no warnings.

## Purpose

Scripts 55–58 built the combinatorial-map layer:

- 55: planar maps with Euler `v + f = e + 2` behind a face-count interface, and the
  unconditional edge bounds `e ≤ 3v − 6`, `e ≤ 2v − 4`;
- 56: the rotation-system / dart-permutation model (`τ` fixed-point-free edge involution,
  `σ` vertex rotation, `φ = τσ⁻¹` face permutation; V/E/F are orbit counts), with
  **χ even for every map** and an integer genus `χ = 2 − 2g`;
- 57: the transposition split/join orbit lemma (`±1`);
- 58: connectedness of a map (`closure {τ,σ}` acts transitively on the darts), with a
  walk characterization and primal–dual group identity.

What was still missing is the actual **topological inequality**: for a connected map,
`χ = V − E + F ≤ 2`, equivalently the combinatorial genus `g = (2 − χ)/2` is
nonnegative. This file proves it entirely inside the permutation model, with no
topological assumptions beyond the dart data and connectedness.

## Mathematical argument

Let `τ = M.edge` (fixed-point-free involution) and `σ = M.vert` on the finite dart set
`α`; `#darts = 2E`, so `E = card α / 2`. Connectedness says `closure {τ, σ}` acts
transitively.

**Step 1 — factor the edge involution into transpositions.**
`involution_swap_factor` (stage 3a) factors any involution `f` into a list `L0` of
pairwise support-disjoint transpositions, one per 2-cycle:
`L0.prod = f`, `f.support.card = 2 * L0.length`. Since `τ` is fixed-point-free,
`τ.support = univ`, hence `card α = 2 * L0.length` and `E = L0.length`.

**Step 2 — grow a spanning tree of vertex cycles (`connected_growth`, stage 3d).**
Starting from one `σ`-cycle and the permutation `p₀ = σ⁻¹`, connectedness guarantees
that as long as the covered darts `C` are not all of `univ`, some edge transposition
`τ a ↔ a` crosses from `C` to a disjoint `σ`-cycle (`crossing_pair`, stage 3c).
Multiplying on the left by that transposition **joins two distinct cycles**, so the
orbit count drops by exactly one (the JOIN lemma, stage 2:
`orbits (swap x y * f) + 1 = orbits f` when `x`, `y` lie on different cycles).
After `tree.length` such joins the product `p = T * σ⁻¹` (`T = tree.prod`) has exactly
one orbit, and
```
tree.length + 1 = orbits σ = V.
```
The `tree.length = V − 1` "tree" transpositions are pairwise support-disjoint, and
their supports are exactly the tree edges.

**Step 3 — the remaining edge transpositions bound the faces.**
Let `τR := τ * T`. Because the tree transpositions are pairwise disjoint, each
commutes with `τ` (a disjoint-support transposition and the edge involution commute
where they meet; proved pointwise via `mul_swap_eq_swap_mul` and `τ² = 1`), and `T² = 1`.
Hence `τR` is itself an involution. It fixes precisely the darts on tree edges and
moves every other dart (`hτRsupp : τR.support = univ \\ U`, where
`U = ⋃_{t ∈ tree} t.support` has `card U = 2 * tree.length`). Factoring `τR` into its
transpositions gives a list `R` of length
```
R.length = L0.length − tree.length = E − (V − 1) = E − V + 1.
```
The face permutation satisfies
```
φ = τ * σ⁻¹ = τR * p
```
(`hfaceeq`, using `T² = 1`). Since `p` has one orbit, the universal fold bound
`orbits_prod_swap_le` (stage 3b: multiplying a permutation by `k` transpositions
raises its orbit count by at most `k`) gives
```
F = orbits φ = orbits (R.prod * p) ≤ orbits p + R.length = 1 + (E − V + 1).
```
Therefore `F ≤ E − V + 2`, i.e.
```
χ = V − E + F ≤ 2.
```

**Step 4 — genus nonnegativity.** Casting to `ℚ`, `g = (2 − χ)/2 ≥ 0`
(`Map.connected_genus_nonneg`). The empty-dart case is handled separately
(`IsEmpty α` gives `V = E = F = 0`, and `0 ≤ 2`).

## What is proved (main results)

- `orbits_swap_same_cycle` — multiplying by a transposition whose two points lie on
  the same cycle splits it: orbit count increases by exactly 1 (stage 2, S).
- `orbits_swap_different_cycles` — points on different cycles join them: orbit count
  decreases by exactly 1 (stage 2, J).
- `orbits_swap_le` — universal one-sided bound: any transposition changes the orbit
  count by at most `+1` (stage 2, U).
- `involution_swap_factor` — every involution is a product of pairwise disjoint
  transpositions, with support-card and list-length identities (stage 3a).
- `orbits_prod_swap_le` — `k` transpositions raise the orbit count by at most `k`
  (stage 3b, Fold).
- `crossing_pair` — from a non-covered dart in a connected map, an edge transposition
  crosses to a disjoint vertex cycle (stage 3c, Crossing).
- `connected_growth` — the spanning-tree growth lemma: there is a list `tree` of
  `V − 1` pairwise-disjoint edge transpositions with `p = T * σ⁻¹` transitive
  (`orbits p = 1`) and `tree.length + 1 = orbits σ` (stage 3d).
- **`Map.connected_euler_bound`** — for every connected map, `(V : ℤ) − E + F ≤ 2`.
- **`Map.connected_genus_nonneg`** — `0 ≤ (2 − (V − E + F)) / 2`.

## What is deliberately NOT proved here

- **Parity / integrality of the genus.** That `χ` is even for *every* (not necessarily
  connected) map, so that `(2 − χ)/2` is an integer, is script 56's parity theorem.
  This script proves nonnegativity of the rational quantity for connected maps and
  relies on 56 for the statement that it is a natural number.
- **Equality `χ = 2` characterizes the sphere.** We prove only the inequality
  `χ ≤ 2` for connected maps. The genus-zero seeds of script 56 (the one-edge link and
  loop on `Fin 2`, both `χ = 2`, both connected by script 58) show the bound is
  attained; nothing here classifies equality.
- **Genus-zero topological realization.** That a connected rotation system with
  `χ = 2` is realizable as a cell decomposition of the sphere (and, more generally,
  that `χ = 2 − 2g` computes the genus of an orientable surface into which the map
  embeds) is genuine surface topology, not permutation combinatorics. It remains the
  frontier's terminal layer gap: it should be cited (rotation systems / combinatorial
  maps ↔ orientable surfaces, e.g. the standard rotation-system embedding theorem) or
  proved as topology, rather than asserted from the dart model. Consequently the
  `PlaneData` interface of scripts 51/53/54 is now backed by the full combinatorial
  spine — Euler for connected maps, parity for all maps, the edge bounds, crossing
  lemma, Szemerédi–Trotter and the unit-distance bound — but not yet by a concrete
  Euclidean/spherical realization.

## Technical notes specific to Lean 4.34.0-rc2

- The proof never unfolds `orbitsOn` and then rewrites a `cycleType` equality; it uses
  `simp only [orbitsOn, <eq>]` (unfolding first destroys the rewrite motive).
- `Commute` lives in the root namespace; with `open Equiv Equiv.Perm`, dot notation
  `t.Commute u` does not resolve. Write `Commute t u`, and since `Commute f g` is the
  equality type `f * g = g * f`, prove the equation and `exact` it — never `rw [Commute]`.
- Finset support-disjointness (`_root_.Disjoint t.support u.support`) bridges to
  pointwise `Equiv.Perm.Disjoint` (and hence `.commute`) via
  `disjoint_iff_disjoint_support`.
- Products of commuting involutions are involutions, but the square rearrangement
  `(a * b)² = a² * b²` is not found by `simp [mul_assoc]` for nested products; it is
  written as an explicit `calc` with `mul_assoc` / `←mul_assoc` steps.
- `swap a a = Equiv.refl α` (`swap_self`), closed after rewriting by `rfl`; there is
  no `Finset.eq_empty_of_forall_not_mem` or `Finset.disjoint_self.mp` — empty supports
  are derived via `Finset.not_nonempty_iff_eq_empty`.
- Nat division `(2 * k) / 2 = k` uses `Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)`;
  `0 / 2 = 0` via `Nat.zero_div`. Integer casts of compound expressions are normalized
  with `simpa using Int.cast_le.mpr …`; `exact_mod_cast` is not available in this file.
- Definitions inside `variable (M : Map α)` whose body does not mention the map name
  the parameter `_M` (e.g. `Map.E`) so that `M.E` field notation still exists without
  tripping the unused-variable linter.
- Digit-prefixed scripts cannot import one another, so the dart model and the orbit
  machinery from 56–58 are restated locally; the file is self-contained under
  `import Mathlib`.
