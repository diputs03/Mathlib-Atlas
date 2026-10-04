# 50 — Every finite graph admits a degeneracy ordering (kernel-verified Lean)

Status: **DONE — `lake env lean script/lean/50_degeneracy_elimination.lean` exits
0 with an empty log (no errors, no warnings, no `sorry`).** Third script that
*adds* a theorem; it supplies the constructive-existence half that scripts
48–49 consume.

## What was missing

Scripts 48–49 start from a *given* `DegeneracyAtMost k G` derivation and derive
the edge bound and greedy `(k+1)`-colorability. They do not show that such an
ordering actually exists for the graphs of interest. This file constructs it.

## What is proved

File: `script/lean/50_degeneracy_elimination.lean` (self-contained; restates the
`DegeneracyAtMost` inductive because digit-prefixed scripts cannot be imported).

- `DegeneracyAtMost.of_forall_exists_low_degree (k)`: if every nonempty graph on
  `V` has a vertex **in its support** with degree at most `k`, then every graph
  on `V` is `k`-degenerate. This is the general elimination-ordering
  construction (the "repeatedly delete a low-degree vertex" half of the standard
  degeneracy characterization, phrased on the fixed type `V`).
- `DegeneracyAtMost.degenerate_card_sub_one`: **every finite graph on `n`
  vertices is `(n-1)`-degenerate.**
- An `example`: `completeGraph (Fin 3)` is `2`-degenerate via the construction.

## Proof idea — well-founded recursion on the support

`deleteIncidenceSet` leaves the peeled vertex on the type (it becomes isolated),
so the vertex count never shrinks; the correct termination measure is the
**cardinality of the support** (the non-isolated vertices).

`of_forall_exists_low_degree` is defined by `Nat.strong_induction_on` on
`n = Fintype.card H.support`:

- if `H = ⊥`, use the `bot` constructor;
- otherwise the hypothesis supplies `v ∈ H.support` with `H.degree v ≤ k`; set
  `H' := H.deleteIncidenceSet v`. Mathlib's
  `card_support_deleteIncidenceSet` gives
  `Fintype.card H'.support ≤ Fintype.card H.support - 1`, so the measure
  strictly decreases and the strong induction hypothesis yields a derivation for
  `H'`; finish with the `peel` constructor.

For `degenerate_card_sub_one`, `H ≠ ⊥` gives a nonempty support
(`support_eq_bot_iff`), and any support vertex satisfies
`H.degree v < Fintype.card V` by `degree_lt_card_verts`, hence
`H.degree v ≤ Fintype.card V - 1`; feed that to the general constructor.

Combined with 48–49 this recovers, constructively, the universal finite-graph
bounds `|E(G)| ≤ (n-1)·n` and `χ(G) ≤ n` (the latter is the trivial
`colorable_of_fintype`, now reached through the degeneracy/coloring-number route).

## Lean-API lessons (Lean 4.34.0-rc2)

- **`rec` is a reserved keyword** — a local named `rec` fails to parse with
  "unexpected token ':='"; use `hrec`.
- `Nat.strong_induction_on` here does **not** accept a named `(motive := …)`
  argument ("unused named arguments: [motive]"); let the motive be inferred and
  carry the `DecidableRel` instance as an *explicit* argument `i` to the
  recursive function, installing it locally with `letI := i`.
- `letI := i` for a data instance trips `linter.style.haveILetI` (it assumes a
  proposition); scope-disable it with
  `set_option linter.style.haveILetI false in` — the instance genuinely must be
  registered so the deleted graph's instance and the low-degree hypothesis can
  be synthesized.
- The support-shrinking arithmetic (`≤ card - 1`, strict decrease) is closed by
  `omega` after `Fintype.card_pos_iff` supplies positivity.
- A lemma with an implicit graph argument is projected as an `Iff` with the
  graph fixed explicitly: `(support_eq_bot_iff (G := H)).mp h`, not
  `support_eq_bot_iff.mp h` (the latter is read as a nonexistent constant
  `SimpleGraph.support_eq_bot_iff.mp`).

## Verification

- Command: `lake env lean script/lean/50_degeneracy_elimination.lean`
  (toolchain `leanprover/lean4:v4.34.0-rc2`).
- Result: exit code **0**, empty log; no `sorry`/`admit` in code.

## Remaining half of the characterization

The tight statement "a graph is `k`-degenerate iff **every nonempty induced
subgraph** has a vertex of degree ≤ k" needs `G.induce`, which produces a graph on
a **subtype** rather than `V`; transporting the peeling across that subtype is a
separate, larger construction. The fixed-type `of_forall_exists_low_degree`
proved here is the computationally useful core (it is exactly what an
elimination-ordering algorithm implements) and suffices for every universal
finite-graph bound.
