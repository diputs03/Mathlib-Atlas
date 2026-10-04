/-
# 54 — Point / curve incidence, Szemerédi–Trotter, and `u(n) = O(n^(4/3))`
        (hard way), on top of the crossing lemma of script 53

This file finishes the *arithmetic spine* of the Erdős unit-distance chain.
Every inequality below is checked by the Lean kernel; the Euclidean geometry
enters only through explicitly named hypotheses, exactly as in scripts 51/53.
No concrete set of points, lines, or circles is asserted to exist.

The chain (Székely's crossing-lemma proof, 1997) is

    crossing lemma  →  incidence bound for curves with bounded pairwise
                        intersections and bounded edge multiplicity
                     →  Szemerédi–Trotter for lines  (s = t = 1)
                     →  unit-distance bound via unit circles (s = t = 2).

Counts
------
`n` points, `m` curves (lines / circles), `I` point–curve incidences. On every
curve that contains `k ≥ 1` of the points, join consecutive points by an arc;
this contributes `k - 1` edges. With `m' ≤ m` nonempty curves the graph has
`e = I - m'` edges, hence the interface `I ≤ e + m`.

Geometric hypotheses (the un-built plane layer), each used once
----------------------------------------------------------------
* `hcr`  : two curves meet in at most `t` points, so the arc drawing has at most
           `t·m(m-1)/2 ≤ (t/2)·m²` crossings.
           (lines: `t = 1`; unit circles, which meet in at most two points:
            `t = 2`.)
* multiplicity: two vertices are joined by at most `s` parallel arcs.
           (lines give a simple graph, `s = 1`; two points lie on at most two
            unit circles, so `s = 2`.)
* `hsample` : the random-subgraph expectation form of the crossing lemma for a
           multigraph of multiplicity `≤ s` (the probability layer, as in 53).

Multigraph crossing lemma (proved here, generalising 53)
--------------------------------------------------------
From the plane-multigraph bound `e ≤ 3·s·n` after deleting crossed edges,
sampling vertices with retention `p` gives `p⁴·c ≥ p²·e - 3·s·p·n` for every
`p ∈ (0,1]`. At `p = 4·s·n/e ≤ 1` (i.e. `e ≥ 4·s·n`):

    c ≥ e³ / (64 · s² · n²).

(The honest, slightly non-sharp denominator is `s²`; this is what the
`e ≤ 3·s·n` multigraph planar bound yields by the sampling algebra, and it is
enough.) For `s = 1` this is exactly `c ≥ e³/(64 n²)` from script 53.

Incidence bound
---------------
If `e ≥ 4·s·n`, the crossing lemma and `c ≤ (t/2)·m²` give
`e³ ≤ 32·t·s²·n²·m²`, i.e. `e ≤ K·n^(2/3)·m^(2/3)` for any `K³ ≥ 32·t·s²`.
Otherwise `e < 4·s·n`. Together with `I ≤ e + m`:

    I ≤ K·n^(2/3)·m^(2/3) + 4·s·n + m.

  * lines   (`s = t = 1`, `K = 4`, since `4³ = 64 ≥ 32`):
        I ≤ 4·n^(2/3)·m^(2/3) + 4·n + m.                       (Szemerédi–Trotter)
  * unit circles (`s = t = 2`, `K = 8`, since `8³ = 512 ≥ 256 = 32·2·2²`),
    with `m = n` circles and `I = 2·u(n)` incidences (each unit pair is counted
    once from each endpoint):
        2·u(n) ≤ 8·n^(4/3) + 9·n,   hence   u(n) ≤ 9·n^(4/3)  for `n ≥ 1`.

The only things not proved here are genuine facts about the Euclidean plane
(straight arcs cross only at line intersections; two unit circles meet in at
most two points; two points lie on at most two unit circles; and the
expectation computation). Those are the geometric/probabilistic *layer*,
isolated as hypotheses.

No `sorry`; the Lean kernel checks every step.
-/

import Mathlib

open Real

namespace SimpleGraph.Incidence

/-- Exponent `2/3`, used throughout the incidence bounds. -/
private noncomputable def q : ℝ := 2 / 3

/-- `(x^(2/3))^3 = x^2` for `x ≥ 0`. -/
private lemma rpow_q_cube (x : ℝ) (hx : 0 ≤ x) : (x ^ q) ^ 3 = x ^ 2 := by
  have h1 : (x ^ q) ^ (3 : ℝ) = x ^ (q * 3) := (Real.rpow_mul hx q 3).symm
  have h2 : (x ^ q) ^ 3 = (x ^ q) ^ (3 : ℝ) := (Real.rpow_natCast (x ^ q) 3).symm
  have h3 : x ^ (q * 3) = x ^ 2 := by
    have hq3 : q * 3 = (2 : ℝ) := by unfold q; norm_num
    rw [hq3]
    exact Real.rpow_natCast x 2
  calc (x ^ q) ^ 3 = (x ^ q) ^ (3 : ℝ) := h2
    _ = x ^ (q * 3) := h1
    _ = x ^ 2 := h3

/-- Multigraph crossing lemma. A graph of multiplicity at most `s`, with `n > 0`
vertices, `e ≥ 4·s·n` edges and `c` crossings, obeys `c ≥ e³/(64·s²·n²)`, given
the random-subgraph expectation inequality `hsample` (the probability layer;
for `s = 1` this is the script-53 crossing lemma). -/
lemma multigraph_crossing_lemma (n e c s : ℕ) (hn_pos : 0 < n) (hs_pos : 0 < s)
    (he : 4 * s * n ≤ e)
    (hsample : ∀ (p : ℝ), 0 < p → p ≤ 1 →
      p^4 * (c : ℝ) ≥ p^2 * (e : ℝ) - 3 * (s : ℝ) * p * (n : ℝ)) :
    (c : ℝ) ≥ (e : ℝ)^3 / (64 * (s : ℝ)^2 * (n : ℝ)^2) := by
  set p : ℝ := 4 * (s : ℝ) * (n : ℝ) / (e : ℝ) with hp_def
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos
  have h4sn_pos : 0 < 4 * s * n := by
    exact mul_pos (mul_pos (by norm_num) hs_pos) hn_pos
  have he_pos : 0 < e := lt_of_lt_of_le h4sn_pos he
  have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he_pos
  have hp_pos : 0 < p := by positivity
  have hp_le_one : p ≤ 1 := by
    rw [hp_def]
    have h4 : 4 * (s : ℝ) * (n : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
    have : 4 * (s : ℝ) * (n : ℝ) / (e : ℝ) ≤ 1 := by
      rw [div_le_one he0]; exact h4
    exact this
  have hsample := hsample p hp_pos hp_le_one
  have hp4_pos : 0 < p^4 := by positivity
  have hrhs : p^2 * (e : ℝ) - 3 * (s : ℝ) * p * (n : ℝ) =
      4 * (s : ℝ)^2 * (n : ℝ)^2 / (e : ℝ) := by
    rw [hp_def]; field_simp; ring
  have hge : p^4 * (c : ℝ) ≥ 4 * (s : ℝ)^2 * (n : ℝ)^2 / (e : ℝ) := by
    rw [hrhs] at hsample; exact hsample
  have hquot : (4 * (s : ℝ)^2 * (n : ℝ)^2 / (e : ℝ)) / p^4 =
      (e : ℝ)^3 / (64 * (s : ℝ)^2 * (n : ℝ)^2) := by
    rw [hp_def]; field_simp; ring
  have hdiv : (c : ℝ) ≥ (4 * (s : ℝ)^2 * (n : ℝ)^2 / (e : ℝ)) / p^4 := by
    field_simp [hp4_pos.ne', he0.ne'] at hge ⊢; linarith
  rw [hquot] at hdiv; exact hdiv

/-- General bounded-intersection incidence bound.

Given `n` points, `m` curves, an arc graph with `e` edges and `c` crossings,
multiplicity at most `s`, at most `t` intersections per curve pair, and
`I ≤ e + m` incidences, then for any `K ≥ 0` with `K³ ≥ 32·t·s²`,

    I ≤ K·n^(2/3)·m^(2/3) + 4·s·n + m.

`hcross` is the crossing lemma for the realised graph (see
`multigraph_crossing_lemma`). -/
lemma incidence_bound (n m e c I s t : ℕ) (K : ℝ)
    (hn_pos : 0 < n) (hs_pos : 0 < s) (_ht_pos : 0 < t)
    (hK_nonneg : 0 ≤ K) (hK : K^3 ≥ 32 * (t : ℝ) * (s : ℝ)^2)
    (hcr : (c : ℝ) ≤ (t : ℝ) / 2 * (m : ℝ)^2)
    (hcross : 4 * s * n ≤ e →
      (c : ℝ) ≥ (e : ℝ)^3 / (64 * (s : ℝ)^2 * (n : ℝ)^2))
    (hI : (I : ℝ) ≤ (e : ℝ) + (m : ℝ)) :
    (I : ℝ) ≤ K * (n : ℝ)^q * (m : ℝ)^q + 4 * (s : ℝ) * (n : ℝ) + (m : ℝ) := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hterm_nonneg : 0 ≤ K * (n : ℝ)^q * (m : ℝ)^q := by positivity
  have hsn_nonneg : 0 ≤ 4 * (s : ℝ) * (n : ℝ) := by positivity
  by_cases h : 4 * s * n ≤ e
  · -- dense case: the crossing lemma and the crossing upper bound meet
    have hle : (e : ℝ)^3 / (64 * (s : ℝ)^2 * (n : ℝ)^2) ≤
        (t : ℝ) / 2 * (m : ℝ)^2 := by linarith [hcross h, hcr]
    have hden_pos : 0 < 64 * (s : ℝ)^2 * (n : ℝ)^2 := by positivity
    have he3 : (e : ℝ)^3 ≤
        32 * (t : ℝ) * (s : ℝ)^2 * (n : ℝ)^2 * (m : ℝ)^2 := by
      calc (e : ℝ)^3
          = ((e : ℝ)^3 / (64 * (s : ℝ)^2 * (n : ℝ)^2)) *
              (64 * (s : ℝ)^2 * (n : ℝ)^2) := by field_simp [hden_pos.ne']
        _ ≤ ((t : ℝ) / 2 * (m : ℝ)^2) * (64 * (s : ℝ)^2 * (n : ℝ)^2) :=
            mul_le_mul_of_nonneg_right hle (by positivity)
        _ = 32 * (t : ℝ) * (s : ℝ)^2 * (n : ℝ)^2 * (m : ℝ)^2 := by ring
    have hfac : 0 ≤ (n : ℝ)^2 * (m : ℝ)^2 := by positivity
    have hK3 : (e : ℝ)^3 ≤ K^3 * (n : ℝ)^2 * (m : ℝ)^2 := by
      nlinarith
    set R : ℝ := K * (n : ℝ)^q * (m : ℝ)^q with hR
    have hR0 : 0 ≤ R := by positivity
    have hR3 : R^3 = K^3 * (n : ℝ)^2 * (m : ℝ)^2 := by
      have hdist : (K * (n : ℝ)^q * (m : ℝ)^q)^3 =
          K^3 * ((n : ℝ)^q)^3 * ((m : ℝ)^q)^3 := by ring
      rw [hR, hdist, rpow_q_cube (n : ℝ) hn0, rpow_q_cube (m : ℝ) hm0]
    have hcube : (e : ℝ)^3 ≤ R^3 := by rw [hR3]; exact hK3
    have heR : (e : ℝ) ≤ R := by
      by_contra hgt
      have hlt : R < (e : ℝ) := by simpa [not_le] using hgt
      have hlt3 : R^3 < (e : ℝ)^3 := by gcongr
      linarith
    have hI' : (I : ℝ) ≤ R + (m : ℝ) := by linarith [hI, heR]
    linarith
  · -- sparse case: e < 4·s·n
    have hlt_nat : e < 4 * s * n := by omega
    have hlt : (e : ℝ) < 4 * (s : ℝ) * (n : ℝ) := by exact_mod_cast hlt_nat
    have hI' : (I : ℝ) ≤ 4 * (s : ℝ) * (n : ℝ) + (m : ℝ) := by linarith [hI]
    linarith [hterm_nonneg]

/-- Szemerédi–Trotter for lines (`s = t = 1`, `K = 4`): the number `I` of
incidences between `n` points and `m` lines is at most
`4·n^(2/3)·m^(2/3) + 4·n + m`, given the arc-graph interfaces. -/
lemma szemeredi_trotter (n m e c I : ℕ)
    (hn_pos : 0 < n)
    (hcr : (c : ℝ) ≤ (1 : ℝ) / 2 * (m : ℝ)^2)
    (hcross : 4 * n ≤ e → (c : ℝ) ≥ (e : ℝ)^3 / (64 * (n : ℝ)^2))
    (hI : (I : ℝ) ≤ (e : ℝ) + (m : ℝ)) :
    (I : ℝ) ≤ 4 * (n : ℝ)^q * (m : ℝ)^q + 4 * (n : ℝ) + (m : ℝ) := by
  have hcross' : 4 * 1 * n ≤ e →
      (c : ℝ) ≥ (e : ℝ)^3 / (64 * ((1 : ℕ) : ℝ)^2 * (n : ℝ)^2) := by
    intro h
    have h4 : 4 * n ≤ e := by simpa [one_mul] using h
    have h := hcross h4
    have hden : 64 * ((1 : ℕ) : ℝ)^2 * (n : ℝ)^2 = 64 * (n : ℝ)^2 := by simp
    rw [hden]
    exact h
  have hcr1 : (c : ℝ) ≤ ((1 : ℕ) : ℝ) / 2 * (m : ℝ)^2 := by simpa using hcr
  have hmain := incidence_bound n m e c I 1 1 (4 : ℝ) hn_pos
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcr1 hcross' hI
  simpa [one_mul] using hmain

/-- `x^(2/3) · x^(2/3) = x^(4/3)` for `x ≥ 0`. -/
private lemma rpow_q_add (x : ℝ) (hx : 0 ≤ x) : x ^ q * x ^ q = x ^ (4 / 3 : ℝ) := by
  by_cases h0 : x = 0
  · rw [h0]
    have hq_ne : q ≠ 0 := by unfold q; norm_num
    have h4_ne : (4 / 3 : ℝ) ≠ 0 := by norm_num
    simp [Real.zero_rpow hq_ne, Real.zero_rpow h4_ne]
  · have hpos : 0 < x := by
      exact lt_of_le_of_ne hx (Ne.symm h0)
    have h : x ^ (q + q) = x ^ q * x ^ q := Real.rpow_add hpos q q
    have hq : q + q = (4 / 3 : ℝ) := by unfold q; norm_num
    rw [hq] at h
    exact h.symm

/-- Erdős unit-distance bound from unit circles (`s = t = 2`, `K = 8`, `m = n`,
`I = 2·u`). For `n ≥ 1` points the number `u = u(n)` of unit-distance pairs is
at most `9·n^(4/3)`, given the circle-arc graph interfaces:

* `hcr`    : two unit circles meet in at most two points, so `c ≤ n²`;
* `hcross` : the multigraph crossing lemma for multiplicity `≤ 2`;
* `hI_arc` : the `2·u` point–circle incidences give `2·u ≤ e + n` arcs
             (each unit pair is an incidence from each of its two endpoints).
-/
lemma unit_distance_bound (n u e c : ℕ) (hn_pos : 0 < n)
    (hcr : (c : ℝ) ≤ (n : ℝ)^2)
    (hcross : 4 * 2 * n ≤ e →
      (c : ℝ) ≥ (e : ℝ)^3 / (64 * (2 : ℝ)^2 * (n : ℝ)^2))
    (hI_arc : ((2 * u : ℕ) : ℝ) ≤ (e : ℝ) + (n : ℝ)) :
    (u : ℝ) ≤ 9 * (n : ℝ)^(4 / 3 : ℝ) := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hcr' : (c : ℝ) ≤ (2 : ℝ) / 2 * (n : ℝ)^2 := by
    have : (2 : ℝ) / 2 * (n : ℝ)^2 = (n : ℝ)^2 := by ring
    rw [this]; exact hcr
  have hmain := incidence_bound n n e c (2 * u) 2 2 (8 : ℝ) hn_pos
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcr' hcross hI_arc
  have hq4 : (n : ℝ)^q * (n : ℝ)^q = (n : ℝ)^(4 / 3 : ℝ) := rpow_q_add (n : ℝ) hn0
  have hreg : 8 * (n : ℝ)^q * (n : ℝ)^q = 8 * ((n : ℝ)^q * (n : ℝ)^q) := by ring
  have h8 : 8 * (n : ℝ)^q * (n : ℝ)^q = 8 * (n : ℝ)^(4 / 3 : ℝ) := by
    rw [hreg, hq4]
  have hraw := hmain
  rw [h8] at hraw
  have hdiv : (u : ℝ) ≤ 4 * (n : ℝ)^(4 / 3 : ℝ) + (9 / 2 : ℝ) * (n : ℝ) := by
    have h2 : (2 : ℝ) * (u : ℝ) ≤
        8 * (n : ℝ)^(4 / 3 : ℝ) + 4 * (2 : ℝ) * (n : ℝ) + (n : ℝ) := by
      simpa [mul_assoc] using hraw
    linarith
  have hn_one : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega)
  have h1 : (n : ℝ)^(1 : ℝ) ≤ (n : ℝ)^(4 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn_one (by norm_num)
  have hle : (n : ℝ) ≤ (n : ℝ)^(4 / 3 : ℝ) := by simpa using h1
  have ha_nonneg : 0 ≤ (n : ℝ)^(4 / 3 : ℝ) := by positivity
  set a : ℝ := (n : ℝ)^(4 / 3 : ℝ) with ha_def
  have hstep1 : 4 * a + (9 / 2 : ℝ) * (n : ℝ) ≤ 4 * a + (9 / 2 : ℝ) * a := by
    gcongr
  have hstep2 : 4 * a + (9 / 2 : ℝ) * a ≤ 9 * a := by
    have hc : 4 * a + (9 / 2 : ℝ) * a = (17 / 2 : ℝ) * a := by ring
    rw [hc]
    have hcoef : (17 / 2 : ℝ) ≤ 9 := by norm_num
    exact mul_le_mul_of_nonneg_right hcoef ha_nonneg
  have hfin : 4 * a + (9 / 2 : ℝ) * (n : ℝ) ≤ 9 * a := le_trans hstep1 hstep2
  simpa [ha_def] using le_trans hdiv hfin

/-- Constant checks for the record. -/
example : (4 : ℝ)^3 ≥ 32 * (1 : ℝ) * (1 : ℝ)^2 := by norm_num
example : (8 : ℝ)^3 ≥ 32 * (2 : ℝ) * (2 : ℝ)^2 := by norm_num
example : (17 / 2 : ℝ) ≤ (9 : ℝ) := by norm_num

/-- At the multigraph threshold `e = 4·s·n` the optimal retention is `p = 1`. -/
example (s n : ℕ) (hs : 0 < s) (hn : 0 < n) :
    4 * (s : ℝ) * (n : ℝ) / (4 * (s : ℝ) * (n : ℝ)) = 1 := by
  have hpos : 0 < 4 * (s : ℝ) * (n : ℝ) := by positivity
  field_simp [hpos.ne']

end SimpleGraph.Incidence
