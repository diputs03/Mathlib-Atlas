/-
# 51 — Planar edge bounds from Euler's formula (hard way)

Script 47 showed that *planar graphs* are a layer gap in Mathlib: there is no
plane embedding, no notion of face, and no planar Euler formula `V - E + F = 2`.
Building the embedding layer (a combinatorial rotation system / map whose
induced surface is the sphere) is a genuinely topological undertaking.

The crossing-lemma / Erdős unit-distance chain, however, consumes only two
purely arithmetic consequences of planarity:

  * a simple planar graph on n ≥ 3 vertices has  e ≤ 3n - 6;
  * a triangle-free (e.g. bipartite) simple planar graph has  e ≤ 2n - 4.

This file proves those consequences rigorously from the data a plane embedding
supplies — the Euler equation and the face-degree bookkeeping — without
asserting that any particular graph is planar. The hypotheses below are exactly
the interface a future `PlaneEmbedding` will inhabit:

    euler : n - e + f = 2          (connected plane graph)
    face  : 3·f ≤ 2·e              (every face has boundary length ≥ 3,
                                    and the sum of face-boundary lengths is 2·e)

Nothing here is circular: no planarity predicate is assumed or proved for any
graph; we only derive the inequalities that follow once an embedding provides
`f` and Euler's formula. Together with scripts 48–50 this supplies the
combinatorial estimates the crossing lemma invokes; the missing *layer* is the
construction that produces the hypotheses (rotation system → faces → Euler).

No `sorry`; the Lean kernel checks every step.
-/

import Mathlib

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SimpleGraph.PlanarBounds

/-- The general planar edge bound from Euler's formula and the fact that in a
simple plane graph every face has boundary length at least three.

Given `n - e + f = 2` and `3·f ≤ 2·e` with `n ≥ 3`, one has `e ≤ 3·n - 6`. -/
lemma planar_edge_bound (n e f : ℕ) (hn : 3 ≤ n)
    (heuler : (n : ℤ) - e + f = 2) (hface : 3 * f ≤ 2 * e) :
    e ≤ 3 * n - 6 := by
  have hf : (f : ℤ) = 2 - (n : ℤ) + (e : ℤ) := by linarith
  have hfc : 3 * (f : ℤ) ≤ 2 * (e : ℤ) := by exact_mod_cast hface
  have hz : (e : ℤ) ≤ 3 * (n : ℤ) - 6 := by
    rw [hf] at hfc
    linarith
  have h6 : 6 ≤ 3 * n := by omega
  have hcast : (↑(3 * n - 6) : ℤ) = 3 * (n : ℤ) - 6 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul]; norm_num
  exact_mod_cast (hcast ▸ hz)

/-- The triangle-free (in particular bipartite) planar edge bound: every face
has boundary length at least four, so `4·f ≤ 2·e`, giving `e ≤ 2·n - 4`. -/
lemma bipartite_planar_edge_bound (n e f : ℕ) (hn : 3 ≤ n)
    (heuler : (n : ℤ) - e + f = 2) (hface : 4 * f ≤ 2 * e) :
    e ≤ 2 * n - 4 := by
  have hf : (f : ℤ) = 2 - (n : ℤ) + (e : ℤ) := by linarith
  have hfc : 4 * (f : ℤ) ≤ 2 * (e : ℤ) := by exact_mod_cast hface
  have hz : (e : ℤ) ≤ 2 * (n : ℤ) - 4 := by
    rw [hf] at hfc
    linarith
  have h4 : 4 ≤ 2 * n := by omega
  have hcast : (↑(2 * n - 4) : ℤ) = 2 * (n : ℤ) - 4 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul]; norm_num
  exact_mod_cast (hcast ▸ hz)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Plane-graph data for `G`: a face count together with Euler's formula and the
face-degree inequality. A future plane-embedding construction will provide
these; the downstream edge bounds only depend on this interface. -/
structure PlaneData where
  faces : ℕ
  euler : (Fintype.card V : ℤ) - Finset.card G.edgeFinset + faces = 2
  faceBoundary : 3 * faces ≤ 2 * Finset.card G.edgeFinset

-- A simple plane graph on at least three vertices has at most `3·n - 6` edges.
omit [DecidableEq V] in
lemma card_edgeFinset_le_three_mul_card_sub_six (hV : 3 ≤ Fintype.card V)
    (d : PlaneData G) :
    Finset.card G.edgeFinset ≤ 3 * Fintype.card V - 6 :=
  planar_edge_bound (Fintype.card V) (Finset.card G.edgeFinset) d.faces
    hV d.euler d.faceBoundary

/-- Plane-graph data for a triangle-free graph (face boundary length ≥ 4). -/
structure BipartitePlaneData where
  faces : ℕ
  euler : (Fintype.card V : ℤ) - Finset.card G.edgeFinset + faces = 2
  faceBoundary : 4 * faces ≤ 2 * Finset.card G.edgeFinset

-- A triangle-free simple plane graph on at least three vertices has at most
-- `2·n - 4` edges.
omit [DecidableEq V] in
lemma card_edgeFinset_le_two_mul_card_sub_four (hV : 3 ≤ Fintype.card V)
    (d : BipartitePlaneData G) :
    Finset.card G.edgeFinset ≤ 2 * Fintype.card V - 4 :=
  bipartite_planar_edge_bound (Fintype.card V) (Finset.card G.edgeFinset)
    d.faces hV d.euler d.faceBoundary

/-- The bounds are sharp: a triangle (`n=3, e=3, f=2`) saturates `e = 3n-6`. -/
example : (3 : ℕ) ≤ 3 * 3 - 6 := by norm_num

/-- `K₄` (`n=4, e=6, f=4`) also saturates `e = 3n-6 = 6`. -/
example : (6 : ℕ) ≤ 3 * 4 - 6 := by norm_num

/-- The arithmetic of the general bound, for the record:
`3(2 - n + e) ≤ 2e` unfolds to `e ≤ 3n - 6`. -/
lemma planar_arithmetic (n e f : ℤ)
    (heuler : n - e + f = 2) (hface : 3 * f ≤ 2 * e) : e ≤ 3 * n - 6 := by
  linarith

end SimpleGraph.PlanarBounds
