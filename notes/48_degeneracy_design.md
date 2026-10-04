# 48 — Graph degeneracy, built the hard way (kernel-verified Lean)

Status: **DONE — `lake env lean script/lean/48_degeneracy.lean` exits 0 with an empty
log (no errors, no warnings, no `sorry`).** This is the first Atlas output that
*adds* a theorem to the formal corpus rather than mapping what is already there.

## Why this script

Scripts 45–47 located the Erdős unit-distance theorem's ingredient frontier and
classified **graph degeneracy** as an *assembly gap*: every primitive it needs
already exists in `Mathlib.Combinatorics.SimpleGraph` (`degree`, `neighborSet`,
`deleteIncidenceSet`, `exists_minimal_degree_vertex`, coloring), but the
degeneracy notion itself and its edge bound are missing. Under the directive to
do things "the hard way", this file constructs the missing mathematics on top of
Mathlib and lets the Lean kernel check it, instead of merely reporting the gap.

Everything is built on existing Mathlib lemmas; `external/mathlib4` was only
read, never modified.

## What is defined and proved

File: `script/lean/48_degeneracy.lean`

- `SimpleGraph.DegeneracyAtMost (k : ℕ) : SimpleGraph V → Prop`, the standard
  vertex-elimination (peeling) characterization, with two constructors:
  - `bot G (h : G = ⊥)`: the empty graph is `k`-degenerate for every `k`;
  - `peel G [DecidableRel G.Adj] v (hdeg : G.degree v ≤ k)
     (hrest : DegeneracyAtMost k (G.deleteIncidenceSet v))`: peel a vertex of
     degree at most `k`, leaving a `k`-degenerate graph.

  `k` is a parameter and the graph is an index because `peel` recurses at the
  different graph `G.deleteIncidenceSet v`.

- Main theorem (instance-independent statement):
  `ncard_edgeSet_le_mul_ncard_support`:
  `Set.ncard G.edgeSet ≤ k * Set.ncard G.support`.
- Corollary `card_edgeFinset_le_mul_card`:
  `Finset.card G.edgeFinset ≤ k * Fintype.card V` (the textbook `|E| ≤ k·|V|`).
- Sanity `example`s: `⊥` is `0`-degenerate; the bound holds for `⊥`; and
  `Finset.card (completeGraph (Fin 3)).edgeFinset = 3` by `decide`, confirming
  the underlying edge object is the real Mathlib one.

## Proof idea

Induct on the peeling derivation. In the `peel` step, let `H :=
G.deleteIncidenceSet v`. Mathlib supplies the exact arithmetic of one peel:

- `card_edgeFinset_deleteIncidenceSet`: `|E(H)| = |E(G)| − deg(v)`;
- `card_support_deleteIncidenceSet` (when `v ∈ G.support`):
  `|support H| ≤ |support G| − 1`.

Two cases:

- `deg(v) = 0`: the vertex is isolated, so edges and support do not grow the
  bound; use the induction hypothesis and support monotonicity.
- `0 < deg(v)`: then `v ∈ G.support`, the support drops by at least one, and
  `|E(G)| = |E(H)| + deg(v) ≤ k·(|support G|−1) + k = k·|support G|`. The final
  nonlinear step is closed with `Nat.mul_add`/`Nat.sub_add_cancel` (`omega`
  cannot do the algebra `k·(f−1)+k = k·f`).

## Lean-API lessons this version settled (Lean 4.34.0-rc2)

- **There is no `Set.card`; finite set cardinal is `Set.ncard`.** The main
  theorem is stated with `Set.ncard` on the edge and support sets so that the
  induction motive does not mention any `DecidableRel` instance. Carrying
  `[DecidableRel G.Adj]` through the motive creates two non-unifiable instances
  (the constructor's abstract instance vs an `intro`-bound one).
- Conversions used:
  - `Set.ncard G.edgeSet = Finset.card G.edgeFinset` via
    `rw [← coe_edgeFinset, Set.ncard_coe_finset]` (the lemma is lowercase
    `ncard_coe_finset`, `Data/Set/Card.lean:666`);
  - `Set.ncard G.support = Fintype.card G.support` via
    `(Set.fintypeCard_eq_ncard G.support).symm`.
- `rw [hG]` on `edgeFinset` is not motive-correct because `edgeFinset` depends
  on the `DecidableRel` instance; the empty-graph base case instead rewrites the
  instance-independent `edgeSet` (`edgeSet_bot`) and lifts through
  `Finset.coe_injective` / `coe_edgeFinset`.
- `support_deleteIncidenceSet_subset` gives `H.support ⊆ G.support \ {v}`;
  `H.support ⊆ G.support` is obtained pointwise as
  `fun x hx => (G.support_deleteIncidenceSet_subset v hx).1`.
- Section-variable hygiene: a helper that does not use the section's
  `[DecidableEq V]` must be prefixed with `omit [DecidableEq V] in`; a doc
  comment cannot sit directly between `omit … in` and `lemma`.

## Verification

- Command: `lake env lean script/lean/48_degeneracy.lean` (toolchain
  `leanprover/lean4:v4.34.0-rc2`).
- Result: exit code **0**, log `notes/48_degeneracy.log` empty; no `sorry`/`admit`
  in code (the only occurrences of the word are in this note and the header
  comment). The kernel, not a keyword scan, is the correctness boundary.

## Natural next steps (not yet started)

- Connect `DegeneracyAtMost` to `exists_minimal_degree_vertex`: construct a
  peeling for every finite graph of maximum/min-degree structure, i.e. show the
  usual equivalence "every subgraph has a vertex of degree ≤ k".
- Derive `(k+1)`-colorability from a degeneracy ordering via the existing
  `SimpleGraph.Coloring.Vertex` machinery.
- Sharpen the bound to `|E| ≤ k·|V| − C(k+1,2)` for a maximal `k`-degenerate
  graph.
- This closes the first (degeneracy) of the five absent ingredients of the
  Spencer–Szemerédi–Trotter / Erdős unit-distance build chain from script 46.
