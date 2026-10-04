# 54 — Point/curve incidence, Szemerédi–Trotter, and `u(n) = O(n^{4/3})`

File: `script/lean/54_incidence_unit_distance.lean`
Namespace: `SimpleGraph.Incidence`
Status: **kernel-verified**, `lake env lean` exit 0, empty log (no `sorry`,
no warnings).

## What this finishes

Script 53 proved the crossing lemma `c ≥ e³/(64 n²)` for a simple graph behind a
sampling interface. This file completes the entire *arithmetic spine* of the
Erdős unit-distance chain (Székely 1997), every inequality kernel-checked:

```
multigraph crossing lemma
   → bounded-intersection incidence bound
   → Szemerédi–Trotter for lines        (s = t = 1)
   → unit-distance via unit circles     (s = t = 2):  u(n) ≤ 9·n^(4/3)
```

## Results (all proved, with explicit constants)

1. `multigraph_crossing_lemma` — multiplicity `≤ s`, `e ≥ 4·s·n`:
   `c ≥ e³/(64·s²·n²)`, from the sampling expectation
   `p⁴c ≥ p²e − 3·s·p·n` at `p = 4·s·n/e`. For `s = 1` this is exactly the
   script-53 lemma. The honest denominator is `s²` (what the `e ≤ 3·s·n`
   plane-multigraph bound yields); it is slightly non-sharp but sufficient.

2. `incidence_bound` — for `n` points, `m` curves, `e` arcs, `c` crossings,
   multiplicity `≤ s`, at most `t` intersections per curve pair, `I ≤ e + m`,
   and any `K ≥ 0` with `K³ ≥ 32·t·s²`:
   `I ≤ K·n^(2/3)·m^(2/3) + 4·s·n + m`.
   Dense case: crossing lemma meets `c ≤ (t/2)·m²`; sparse case: `e < 4·s·n`.

3. `szemeredi_trotter` — lines (`s = t = 1`, `K = 4`, since `4³ = 64 ≥ 32`):
   `I ≤ 4·n^(2/3)·m^(2/3) + 4·n + m`.

4. `unit_distance_bound` — unit circles (`s = t = 2`, `K = 8`, since
   `8³ = 512 ≥ 256 = 32·2·2²`), `m = n` circles and `I = 2·u` incidences:
   **`u(n) ≤ 9·n^(4/3)` for `n ≥ 1`**. The constant is derived, not quoted:
   `2u ≤ 8·n^(4/3) + 9n`, then `n ≤ n^(4/3)` for `n ≥ 1` folds the linear term
   into `17/2·n^(4/3) ≤ 9·n^(4/3)`.

## Geometric / probabilistic inputs left as hypotheses (the un-built layer)

Exactly as in 51/53, no Euclidean geometry is asserted:

* `hcr`     — two curves meet in at most `t` points (`c ≤ (t/2)·m²`);
  lines cross once, two unit circles meet in at most two points.
* multiplicity `s` — lines give a simple graph; two points lie on at most two
  unit circles (`s = 2`).
* `hI`/`hI_arc` — `e = I − m'` for the `m' ≤ m` nonempty curves, hence
  `I ≤ e + m`; for unit circles `I = 2·u`.
* `hsample` — the random-subgraph expectation (the probability layer).

These are the genuine plane/probability facts; everything downstream is pure
arithmetic and is what the discovery pipeline (scripts 45–47) identified as the
missing combinatorics.

## Lean notes

* `q := 2/3` must be `noncomputable` (real division). Fractional-power cube
  identities use `Real.rpow_mul` + `Real.rpow_natCast`; `x^(2/3)·x^(2/3) =
  x^(4/3)` uses `Real.rpow_add`, which needs `0 < x`, with the `x = 0` case
  handled separately via `Real.zero_rpow`.
* Cube monotonicity (`e³ ≤ R³ ⇒ e ≤ R`, both nonneg) is proved by
  contradiction + `gcongr`; no floating point anywhere.
* Numeral/cast hygiene: hypotheses use the Nat cast (`↑1`, `↑(2*u)`); the
  final constant fold is written as explicit `gcongr`/`mul_le_mul` steps rather
  than a single `linarith`, which will not combine the fractional coefficients
  reliably.

## Verification

`lake env lean script\lean\54_incidence_unit_distance.lean` → exit 0, empty
output (log `notes/54_incidence.log`). No `sorry`, no warnings.

## Relation to the discovery arc

Scripts 46/47 classified point-line incidence, Szemerédi–Trotter, crossing
number and graph degeneracy as absent ingredients of the unit-distance chain.
Scripts 48–50 built degeneracy, 51/53 the planar/crossing consequences, and
this file supplies the incidence estimates and the headline exponent
`u(n) = O(n^(4/3))`. The *only* remaining gap to a fully concrete theorem is the
geometric layer (straight arcs / unit-circle intersections / the plane
embedding), which script 55 begins to build combinatorially.
