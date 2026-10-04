# 49 — Degeneracy implies greedy (k+1)-colorability (kernel-verified Lean)

Status: **DONE — `lake env lean script/lean/49_degeneracy_coloring.lean` exits 0
with an empty log (no errors, no warnings, no `sorry`).** Second script that
*adds* a theorem to the corpus; builds on the `DegeneracyAtMost` predicate of
script 48.

## Why this script

The two headline consequences of graph degeneracy are

1. the edge bound `|E| ≤ k·|V|` (script 48), and
2. the **coloring-number bound**: a `k`-degenerate graph is `(k+1)`-colorable,
   i.e. its chromatic number satisfies `χ(G) ≤ k+1`.

A search of `Mathlib/Combinatorics/SimpleGraph` for `coloringNumber`,
`degenera`, and `greedy` returns **nothing** — Mathlib has proper colorings
(`Coloring`, `Colorable`, `chromaticNumber`) and the trivial
`colorable_of_fintype`, but no degeneracy/coloring-number theorem. So this is a
genuine missing result, supplied here and kernel-checked. `external/mathlib4` was
only read.

## What is proved

File: `script/lean/49_degeneracy_coloring.lean` (self-contained; it restates the
`DegeneracyAtMost` inductive, because standalone scripts live in files whose
names begin with digits and therefore cannot be imported as Lean modules).

- `DegeneracyAtMost.colorable_succ (k) (h : DegeneracyAtMost k G) :
   G.Colorable (k+1)` — existence of a proper coloring with `k+1` colors.
- `DegeneracyAtMost.chromaticNumber_le_succ : G.chromaticNumber ≤ k+1`.
- An `example` that the empty graph is `0`-degenerate and hence 1-colorable.

## Proof idea (greedy along the reverse peeling order)

Induct on the peeling derivation.

- **Base (`G = ⊥`):** color every vertex `0`; there are no adjacencies.
- **Step (`peel v`):** let `H := G.deleteIncidenceSet v`. By the induction
  hypothesis `H` has a proper `(k+1)`-coloring `C`. The peeled vertex `v` has
  `G.degree v ≤ k` neighbors, so the set `used = image C (G.neighborFinset v)`
  has at most `k` colors (`Finset.card_image_le` together with
  `card_neighborFinset_eq_degree`). Since `Fin (k+1)` has `k+1` elements,
  `Finset.exists_mem_notMem_of_card_lt_card` yields a free color `c ∉ used`.
  Define `color x = if x = v then c else C x`. Properness has three cases:
  endpoint `x = v`, endpoint `y = v` (use symmetry of adjacency and
  `ne_of_adj`), or neither — the edge survives in `H` and `C.valid` applies
  (`deleteIncidenceSet_adj`).

## Lean-API lessons (Lean 4.34.0-rc2)

- `G.Coloring α` is the graph-homomorphism abbreviation `G →g completeGraph α`;
  build one with `Coloring.mk (color : V → α)
  (valid : ∀ {v w}, G.Adj v w → color v ≠ color w)`.
  `G.Colorable n := Nonempty (G.Coloring (Fin n))`.
- The conclusion `Colorable` carries **no `DecidableRel`**, so the induction
  motive is instance-independent even though the peel step uses
  `G.neighborFinset` (which needs the constructor's own `DecidableRel G.Adj`).
  This is the same motive discipline as script 48, but cleaner.
- A free color comes from `Finset.exists_mem_notMem_of_card_lt_card`
  (`Data/Finset/Card.lean:628`); there is no `Finset.exists_not_mem` in this
  version.
- Do **not** `subst` the equality `x = v` in the validness proof: it removes the
  identifier `v` that later terms (`N`, `color`) depend on. Use `hx ▸ hxy` to
  transport the adjacency instead.
- `G.mem_neighborFinset` has the *center* vertex implicit; fixing the wrong
  argument yields `w ∈ neighborFinset y`. `simpa [N] using hadj` avoids naming
  the center entirely.
- `if_pos`/`if_neg` are deprecated in this toolchain; use `ite_eq_left` /
  `ite_eq_right`.

## Verification

- Command: `lake env lean script/lean/49_degeneracy_coloring.lean`
  (toolchain `leanprover/lean4:v4.34.0-rc2`).
- Result: exit code **0**, empty log; no `sorry`/`admit`. The kernel is the
  correctness boundary.

## Where this sits in the unit-distance chain

Scripts 46–47 ordered the Spencer–Szemerédi–Trotter / Erdős unit-distance build
as degeneracy → planar+Euler → crossing lemma → point–line incidence →
Szemerédi–Trotter → `u(n)=O(n^{4/3})`. Degeneracy now has both of its standard
elementary consequences (edge bound in 48, coloring in 49). Natural further
"hard way" steps:

- construct peeling for an arbitrary finite graph from
  `exists_minimal_degree_vertex` (the "every nonempty subgraph has a low-degree
  vertex" equivalence), by well-founded recursion on the support size;
- begin the planar/Euler layer, which 47 showed is a genuine *layer* gap (no
  plane drawing, faces, or `V−E+F`).
