# 53 — The crossing lemma from the planar edge bound (kernel-verified Lean)

Status: **DONE — `lake env lean script/lean/53_crossing_lemma.lean` exits 0 with
an empty log (no errors, no warnings, no `sorry`).** Fifth theorem-ADDING
script; proves the quantitative engine the Erdős unit-distance / incidence
bounds rely on, with the geometric and probabilistic inputs isolated as
hypotheses.

## What is proved

Namespace `SimpleGraph.CrossingLemma`, file
`script/lean/53_crossing_lemma.lean`:

- `crossing_number_linear (n e c) (hn : 3 ≤ n)`: if, after deleting one edge per
  crossing, the remaining `e − c` edges obey the planar bound
  `(e : ℤ) − c ≤ 3n − 6` (script 51), then
  **`c ≥ e − 3n + 6`**.
- `crossing_number_linear'`: the sampling-friendly form **`c ≥ e − 3n`**
  (the constant `+6` is dropped), over `ℝ`.
- `crossing_lemma (n e c) (hn_pos : 0 < n) (he : 4n ≤ e)`: if the linear bound
  holds under every vertex-retention probability `p ∈ (0,1]`,
  `p⁴ c ≥ p² e − 3 p n`, then
  **`c ≥ e³ / (64 n²)`**.
- `norm_num` sanity checks (`4³/(64·1²) = 1`; the optimal `p = 4n/e` equals `1`
  at the threshold `e = 4n`).

## Derivation

**Step 1.** A drawing with `c` crossings: remove one edge from each crossing
(`≤ c` edges); the remaining graph is plane and so has `≤ 3n − 6` edges (script
51). Hence `e − c ≤ 3n − 6`, i.e. `c ≥ e − 3n + 6`.

**Step 2 (probabilistic amplification).** Keep each vertex independently with
probability `p`. A crossing survives only if all four of its endpoints survive
(`p⁴`), an edge if both endpoints survive (`p²`), a vertex with probability `p`,
so applying the linear bound to each realized subgraph and taking expectations
gives `p⁴ c ≥ p² e − 3 p n`. Choose `p = 4n/e` (valid and `≤ 1` when
`e ≥ 4n`):

```
p² e − 3 p n = 16 n²/e − 12 n²/e = 4 n²/e,
p⁴ c = 256 n⁴/e⁴ · c ≥ 4 n²/e
⇒ c ≥ e³/(64 n²).
```

The algebra (`p²e − 3pn = 4n²/e` and `(4n²/e)/p⁴ = e³/(64n²)`) is closed by
`field_simp; ring`, with `0 < n`, `0 < e`, `0 < p`, `0 < p⁴` discharged
explicitly; `p ≤ 1` comes from `div_le_one` and `4n ≤ e`.

## Honest scope — the two un-built inputs

This file proves the crossing lemma **as an arithmetic/algebraic consequence**
of two inputs that belong to layers not yet built:

1. `hdel` — deleting one edge per crossing leaves a graph satisfying the planar
   bound. This needs a combinatorial **plane-drawing / crossing model** (a
   drawing, its crossings, and the fact that one edge removal per crossing
   planarizes), the same embedding layer that script 51's `PlaneData` interface
   anticipates.
2. `hsample` — the post-sampling inequality for every `p`. This is the
   **expectation** computation (linearity of expectation; survival
   probabilities `p`, `p²`, `p⁴`), which needs a probability layer over finite
   vertex subsets.

Given those, the crossing lemma proper — including the sharp constant `1/64`
and the `e ≥ 4n` threshold — is fully proved here. The crossing lemma is the
exact estimate used to turn an incidence count into the unit-distance bound
`u(n) = O(n^{4/3})` (jointly with point-line incidence / Szemerédi–Trotter).

## Lean-API lessons (Lean 4.34.0-rc2)

- Keep the linear bound in `ℤ` (`linarith`) and cast to `ℝ` with
  `exact_mod_cast` before mixing; `linarith` does not silently combine a `ℤ`
  hypothesis with a `ℝ` goal.
- A hypothesis written with an internal `let p := …` is awkward to rewrite;
  quantify the sampling hypothesis `∀ p : ℝ, 0 < p → p ≤ 1 → …` and apply it at
  the chosen `p` (this is also the mathematically faithful statement).
- Division in the final step is most robustly handled by
  `field_simp [pos.ne'] at hge ⊢; linarith` rather than hunting for the exact
  `div_le_iff` lemma name.
- A binder kept for the meaningful statement but not needed by the `ℤ` proof
  (`hn : 3 ≤ n`) should still do real work (`have h3 : 6 ≤ 3*n := by
  exact_mod_cast (by omega)`) to satisfy the unused-variable linter.
- `field_simp; ring` (not `<;>`) when a single goal is produced.

## Verification

- Command: `lake env lean script/lean/53_crossing_lemma.lean`
  (toolchain `leanprover/lean4:v4.34.0-rc2`).
- Result: exit code **0**, empty log; no `sorry`/`admit` in code.

## Unit-distance chain status

Degeneracy (48–50) ✓; planar edge estimates behind the Euler interface (51) ✓;
**crossing lemma behind the drawing/expectation interface (53) ✓**. Remaining:
the plane-embedding/drawing layer and the expectation wiring (the shared
geometric/probabilistic interface), then point-line incidence and
Szemerédi–Trotter to reach `u(n) = O(n^{4/3})`.
