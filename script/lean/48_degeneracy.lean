/-
# 48 — Graph degeneracy, done the hard way (kernel-verified, no `sorry`)

Script 47 classified graph degeneracy as an *assembly gap*: the primitives
(`degree`, induced/deleted subgraphs, `exists_minimal_degree_vertex`, coloring)
all exist, but the degeneracy notion and its edge bound do not. This file
*builds* the missing mathematics on top of Mathlib at the pinned commit and lets
the Lean kernel check it.

We define degeneracy through the vertex-elimination (peeling) characterization:
a graph is `k`-degenerate if one can repeatedly delete a vertex of degree at
most `k` until the empty graph remains. From this we prove the classical edge
bounds

    |E(G)| ≤ k · |support G| ≤ k · |V|.

The main theorem is stated with `Set.ncard` on the (instance-independent) edge
and support sets so that it does not depend on any `DecidableRel` choice; the
peeling arithmetic is taken from Mathlib (`card_edgeFinset_deleteIncidenceSet`,
`card_support_deleteIncidenceSet`).
-/

import Mathlib

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SimpleGraph

/-- A graph is `k`-degenerate if its vertices admit an elimination ordering:
either the graph is empty, or there is a vertex `v` of degree at most `k` whose
incidence set can be deleted, leaving a `k`-degenerate graph.

This is the standard recursive/peeling definition of graph degeneracy
(equivalently: every nonempty subgraph has a vertex of degree at most `k`). -/
inductive DegeneracyAtMost (k : ℕ) : SimpleGraph V → Prop
  | /-- The empty graph is `k`-degenerate for every `k`. -/
    bot (G : SimpleGraph V) (h : G = ⊥) : DegeneracyAtMost k G
  | /-- Peel a vertex of degree at most `k`; the graph that remains after
  deleting its incidence set must be `k`-degenerate. -/
    peel (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
      (hdeg : G.degree v ≤ k)
      (hrest : DegeneracyAtMost k (G.deleteIncidenceSet v)) :
      DegeneracyAtMost k G

namespace DegeneracyAtMost

omit [DecidableEq V] in
lemma ncard_edgeSet_eq_card_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] :
    Set.ncard G.edgeSet = Finset.card G.edgeFinset := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset]

omit [DecidableEq V] in
lemma ncard_support_eq_fintype_card (G : SimpleGraph V) [DecidableRel G.Adj] :
    Set.ncard G.support = Fintype.card G.support :=
  (Set.fintypeCard_eq_ncard G.support).symm

/-- The sharp degeneracy edge bound: a `k`-degenerate graph has at most
`k · |support G|` edges among its non-isolated vertices. -/
theorem ncard_edgeSet_le_mul_ncard_support (k : ℕ) {G : SimpleGraph V}
    (h : DegeneracyAtMost k G) :
    Set.ncard G.edgeSet ≤ k * Set.ncard G.support := by
  classical
  induction h with
  | bot G hG =>
    rw [hG]
    simp
  | peel G v hdeg hrest ih =>
    let H := G.deleteIncidenceSet v
    have eEdgeH : Set.ncard H.edgeSet = Finset.card H.edgeFinset :=
      ncard_edgeSet_eq_card_edgeFinset H
    have eSuppH : Set.ncard H.support = Fintype.card H.support :=
      ncard_support_eq_fintype_card H
    have ihF : Finset.card H.edgeFinset ≤ k * Fintype.card H.support := by
      rw [← eEdgeH, ← eSuppH]
      exact ih
    have hEdges : Finset.card H.edgeFinset =
        Finset.card G.edgeFinset - G.degree v :=
      G.card_edgeFinset_deleteIncidenceSet v
    have hdegLe : G.degree v ≤ Finset.card G.edgeFinset :=
      G.degree_le_card_edgeFinset v
    have hsub : H.support ⊆ G.support := fun x hx =>
      (G.support_deleteIncidenceSet_subset v hx).1
    have fin : Finset.card G.edgeFinset ≤ k * Fintype.card G.support := by
      by_cases hzero : G.degree v = 0
      · -- The peeled vertex is isolated: edges and support are unchanged.
        have hGE0 : Finset.card G.edgeFinset = Finset.card H.edgeFinset := by
          rw [hEdges, hzero]; simp
        have hSuppMono : Fintype.card H.support ≤ Fintype.card G.support :=
          Set.card_le_card hsub
        rw [hGE0]
        exact ihF.trans (Nat.mul_le_mul_left k hSuppMono)
      · -- The peeled vertex lies in the support, which shrinks by at least one.
        have hvPos : 0 < G.degree v := Nat.pos_of_ne_zero hzero
        have hvs : v ∈ G.support := (G.degree_pos_iff_mem_support v).mp hvPos
        have hCardSupp : Fintype.card H.support ≤ Fintype.card G.support - 1 :=
          G.card_support_deleteIncidenceSet hvs
        have h1 : 0 < Fintype.card G.support :=
          Fintype.card_pos_iff.mpr ⟨⟨v, hvs⟩⟩
        have hGE : Finset.card G.edgeFinset =
            Finset.card H.edgeFinset + G.degree v := by omega
        have hLast : k * (Fintype.card G.support - 1) + k =
            k * Fintype.card G.support := by
          have h2 : (Fintype.card G.support - 1) + 1 = Fintype.card G.support :=
            Nat.sub_add_cancel (by linarith)
          calc
            k * (Fintype.card G.support - 1) + k
              = k * (Fintype.card G.support - 1) + k * 1 := by rw [Nat.mul_one]
            _ = k * ((Fintype.card G.support - 1) + 1) := by rw [Nat.mul_add]
            _ = k * Fintype.card G.support := by rw [h2]
        rw [hGE]
        calc
          Finset.card H.edgeFinset + G.degree v
            ≤ k * Fintype.card H.support + k := Nat.add_le_add ihF hdeg
          _ ≤ k * (Fintype.card G.support - 1) + k :=
              Nat.add_le_add (Nat.mul_le_mul_left k hCardSupp) le_rfl
          _ = k * Fintype.card G.support := hLast
    have eEdgeG : Set.ncard G.edgeSet = Finset.card G.edgeFinset :=
      ncard_edgeSet_eq_card_edgeFinset G
    have eSuppG : Set.ncard G.support = Fintype.card G.support :=
      ncard_support_eq_fintype_card G
    rw [eEdgeG, eSuppG]
    exact fin

/-- The textbook degeneracy edge bound: a `k`-degenerate graph on `n` vertices
has at most `k · n` edges. -/
theorem card_edgeFinset_le_mul_card (k : ℕ) {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : DegeneracyAtMost k G) :
    Finset.card G.edgeFinset ≤ k * Fintype.card V := by
  have hn : Set.ncard G.edgeSet ≤ k * Set.ncard G.support :=
    h.ncard_edgeSet_le_mul_ncard_support k
  have eEdgeG : Set.ncard G.edgeSet = Finset.card G.edgeFinset :=
    ncard_edgeSet_eq_card_edgeFinset G
  have eSuppG : Set.ncard G.support = Fintype.card G.support :=
    ncard_support_eq_fintype_card G
  rw [eEdgeG, eSuppG] at hn
  have hSupp : Fintype.card G.support ≤ Fintype.card V := by
    have hle := Set.card_le_card (Set.subset_univ (s := G.support))
    simpa using hle
  exact hn.trans (Nat.mul_le_mul_left k hSupp)

/-- The empty graph is `0`-degenerate. -/
example : DegeneracyAtMost 0 (⊥ : SimpleGraph V) := .bot ⊥ rfl

/-- The bound applies to the empty graph. -/
example : Set.ncard (⊥ : SimpleGraph V).edgeSet ≤
    0 * Set.ncard (⊥ : SimpleGraph V).support :=
  (.bot ⊥ rfl : DegeneracyAtMost 0 (⊥ : SimpleGraph V)).ncard_edgeSet_le_mul_ncard_support 0

/-- Sanity check on the underlying edge object: the complete graph on three
labeled vertices has exactly three edges. -/
example : Finset.card (SimpleGraph.completeGraph (Fin 3)).edgeFinset = 3 := by decide

end DegeneracyAtMost
end SimpleGraph
