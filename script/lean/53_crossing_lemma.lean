/-
# 53 — The crossing lemma (hard way), from the planar edge bound

The Erdős unit-distance bound `u(n) = O(n^(4/3))` is driven by the **crossing
lemma**: a simple graph on `n` vertices with `e ≥ 4n` edges, drawn in the plane
with `c` edge crossings, satisfies

    c ≥ e³ / (64 · n²).

Script 51 proved the planar edge estimate `e' ≤ 3n - 6` behind the Euler
interface. This file proves the crossing lemma in two purely arithmetic steps,
isolating exactly the geometric / probabilistic inputs (which depend on the
still-unbuilt plane-embedding layer) as hypotheses. Nothing here asserts that a
concrete graph is planar or has a drawing; every inequality below is checked by
the kernel.

Step 1 (linear crossing bound). Given a drawing with `c` crossings, delete one
edge per crossing; at most `c` edges are removed and the remaining graph is
plane, so it has at most `3n - 6` edges (script 51). Hence
`e - c ≤ 3n - 6`, i.e. `c ≥ e - 3n + 6`.

Step 2 (random-sampling amplification). Keep each vertex independently with
probability `p`. Per realized subgraph the linear bound gives
`c' ≥ e' - 3n'`; taking expectations,
    E[c'] = p⁴ c   (a proper crossing uses four distinct endpoints),
    E[e'] = p² e,  E[n'] = p n,
so `p⁴ c ≥ p² e - 3 p n` for every `p ∈ (0,1]`. Choosing `p = 4n/e ≤ 1`
(available when `e ≥ 4n`) yields `c ≥ e³/(64 n²)`.

The two un-built inputs are stated honestly:
  * `hdel` — deleting one edge per crossing leaves a graph obeying the planar
    edge bound (this is the geometric content; it needs the plane-drawing
    model);
  * `hsample` — the post-sampling inequality `p⁴ c ≥ p² e - 3 p n` at the
    optimal `p` (this is the expectation computation; it needs a probability
    layer). Given those, the crossing lemma itself is pure algebra and is what
    the incidence / unit-distance argument invokes.

No `sorry`; the Lean kernel checks every step.
-/

import Mathlib

open Real

namespace SimpleGraph.CrossingLemma

/-- Step 1: the linear crossing-number inequality `c ≥ e - 3n + 6`, from the
planar edge bound applied after deleting at most one edge per crossing.

`hdel : (e : ℤ) - c ≤ 3 * n - 6` is exactly "the graph left after removing the
`c` crossed edges obeys the planar bound of script 51". -/
lemma crossing_number_linear (n e c : ℕ) (hn : 3 ≤ n)
    (hdel : (e : ℤ) - c ≤ 3 * (n : ℤ) - 6) :
    (c : ℤ) ≥ (e : ℤ) - 3 * (n : ℤ) + 6 := by
  have h3 : 6 ≤ 3 * (n : ℤ) := by exact_mod_cast (by omega)
  linarith

/-- The weaker, sampling-friendly form `c ≥ e - 3n` (the constant `+6` is
discarded; this is what the random-subgraph expectation consumes). -/
lemma crossing_number_linear' (n e c : ℕ) (hn : 3 ≤ n)
    (hdel : (e : ℤ) - c ≤ 3 * (n : ℤ) - 6) :
    (c : ℝ) ≥ (e : ℝ) - 3 * (n : ℝ) := by
  have h := crossing_number_linear n e c hn hdel
  have h' : (c : ℝ) ≥ (e : ℝ) - 3 * (n : ℝ) + 6 := by exact_mod_cast h
  linarith

/-- Step 2: the crossing lemma. The random-sampling expectation gives the
linear bound under every retention probability `p ∈ (0,1]` (a crossing has four
endpoints, an edge two, a vertex one). At the optimal `p = 4n/e ≤ 1` (available
when `0 < n` and `4n ≤ e`) this yields `c ≥ e³/(64 n²)`. -/
lemma crossing_lemma (n e c : ℕ) (hn_pos : 0 < n) (he : 4 * n ≤ e)
    (hsample : ∀ (p : ℝ), 0 < p → p ≤ 1 →
      p^4 * (c : ℝ) ≥ p^2 * (e : ℝ) - 3 * p * (n : ℝ)) :
    (c : ℝ) ≥ (e : ℝ)^3 / (64 * (n : ℝ)^2) := by
  set p : ℝ := 4 * (n : ℝ) / (e : ℝ) with hp_def
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have he_pos : 0 < e := by omega
  have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he_pos
  have hp_pos : 0 < p := by positivity
  have hp_le_one : p ≤ 1 := by
    rw [hp_def]
    have : (4 * (n : ℝ)) ≤ (e : ℝ) := by exact_mod_cast he
    have : (4 * (n : ℝ)) / (e : ℝ) ≤ 1 := by
      rw [div_le_one he0]
      exact this
    exact this
  have hsample := hsample p hp_pos hp_le_one
  have hp4_pos : 0 < p^4 := by positivity
  -- the right-hand side at p = 4n/e equals 4 n² / e
  have hrhs : p^2 * (e : ℝ) - 3 * p * (n : ℝ) = 4 * (n : ℝ)^2 / (e : ℝ) := by
    rw [hp_def]
    field_simp; ring
  have hge : p^4 * (c : ℝ) ≥ 4 * (n : ℝ)^2 / (e : ℝ) := by
    rw [hrhs] at hsample
    exact hsample
  -- divide by p⁴, then substitute p = 4n/e
  have hquot : (4 * (n : ℝ)^2 / (e : ℝ)) / p^4 =
      (e : ℝ)^3 / (64 * (n : ℝ)^2) := by
    rw [hp_def]
    field_simp; ring
  have hdiv : (c : ℝ) ≥ (4 * (n : ℝ)^2 / (e : ℝ)) / p^4 := by
    field_simp [hp4_pos.ne', he0.ne'] at hge ⊢; linarith
  rw [hquot] at hdiv
  exact hdiv

/-- Sanity: at the threshold `e = 4n` the bound is `c ≥ 1` (for `n = 1`,
`4³/(64·1²) = 1`). -/
example : (4 : ℝ)^3 / (64 * (1 : ℝ)^2) = 1 := by norm_num

/-- The optimal retention probability is `p = 4n/e`; for `e = 4n` it is `1`. -/
example : (4 * (1 : ℝ) / (4 : ℝ)) = 1 := by norm_num

end SimpleGraph.CrossingLemma
