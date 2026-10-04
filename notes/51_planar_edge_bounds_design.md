# 51 — Planar edge bounds from Euler's formula (kernel-verified Lean)

Status: **DONE — `lake env lean script/lean/51_planar_edge_bounds.lean` exits 0
with an empty log (no errors, no warnings, no `sorry`).** Fourth theorem-ADDING
script; supplies the two estimates the crossing-lemma / Erdős unit-distance
chain consumes from planarity.

## What the chain needs

Script 47 classified planar graphs as a **layer gap** in Mathlib (no plane
embedding, no faces, no planar Euler `V−E+F`). The crossing lemma and the
unit-distance bound do not call the embedding directly; they invoke only two
arithmetic consequences of planarity:

- a simple planar graph on `n ≥ 3` vertices has **`e ≤ 3n − 6`**;
- a triangle-free (in particular bipartite) simple planar graph has
  **`e ≤ 2n − 4`**.

## What is proved

Namespace `SimpleGraph.PlanarBounds`, file
`script/lean/51_planar_edge_bounds.lean`:

- `planar_edge_bound (n e f) (hn : 3 ≤ n) (heuler : (n:ℤ) − e + f = 2)
  (hface : 3·f ≤ 2·e) : e ≤ 3·n − 6`.
- `bipartite_planar_edge_bound` with `4·f ≤ 2·e` : `e ≤ 2·n − 4`.
- Structures `PlaneData G` / `BipartitePlaneData G` carrying the face count,
  the Euler equation and the face-degree inequality, and graph-level
  corollaries `card_edgeFinset_le_three_mul_card_sub_six` /
  `card_edgeFinset_le_two_mul_card_sub_four` stated directly in terms of
  `Fintype.card V` and `Finset.card G.edgeFinset`.
- `planar_arithmetic`, the pure-ℤ core, and `norm_num` sharpness examples
  (triangle `n=3,e=3,f=2` and `K₄` `n=4,e=6,f=4` both saturate `e = 3n−6`).

## Derivation

From Euler `f = 2 − n + e`. In a simple plane graph every face has boundary
length at least 3, and summing boundary lengths counts every edge twice, so
`3f ≤ 2e`. Substituting:

```
3(2 − n + e) ≤ 2e  ⇒  e ≤ 3n − 6.
```

Triangle-free graphs have no 3-cycle, hence every face has boundary length at
least 4: `4f ≤ 2e`, giving `e ≤ 2n − 4`.

## Honest scope — what is and is not built

This file proves the **downstream consequences** of the planar layer, not the
layer itself. The hypotheses `euler` and `faceBoundary` are exactly the data a
future plane embedding supplies; nothing here asserts that a concrete graph is
planar or constructs faces. This is deliberate and non-circular:

- the missing *layer* is a combinatorial embedding (rotation system / map)
  whose induced surface is the sphere, together with a proof that its face
  orbits satisfy `V−E+F = 2`. A rotation system alone encodes **any orientable
  surface** (Euler characteristic `2−2g`); permutation-sign arguments recover
  only the parity `V−E+F ≡ 0 (mod 2)`, and the constant `2` needs a genus/
  topological argument. That is why it is a genuine layer gap rather than a
  missing lemma.
- Once such an embedding produces `f` and Euler's formula, the two edge bounds
  used by the crossing lemma follow immediately from this file with no further
  work.

So the unit-distance chain now has, kernel-verified: degeneracy (48–50) and the
planar edge estimates (51, against the Euler interface). Still ahead: the
embedding→Euler construction itself, then the crossing lemma, point-line
incidence, and Szemerédi–Trotter.

## Lean-API lessons (Lean 4.34.0-rc2)

- Prove the bound in `ℤ` (`have hf : (f:ℤ) = 2 − n + e := by linarith`, cast the
  Nat face inequality with `exact_mod_cast`, then `linarith`); do not expect
  `zify; linarith` to align a Nat subtraction `3*n-6` automatically.
- Align the final cast with
  `rw [Nat.cast_sub (by omega), Nat.cast_mul]; norm_num` — plain `ring` cannot
  see through `↑(n*3)` vs `↑n*3`.
- A doc comment `/-! … -/` or `/- … -/` directly before
  `omit [DecidableEq V] in lemma …` gives "unexpected token 'omit'"; use a
  plain `--` comment there (same gotcha as scripts 48–50).

## Verification

- Command: `lake env lean script/lean/51_planar_edge_bounds.lean`
  (toolchain `leanprover/lean4:v4.34.0-rc2`).
- Result: exit code **0**, empty log; no `sorry`/`admit` in code.
