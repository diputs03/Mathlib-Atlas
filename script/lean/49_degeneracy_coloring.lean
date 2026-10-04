/-
# 49 — Degeneracy implies greedy (k+1)-colorability, the hard way

Script 48 introduced `SimpleGraph.DegeneracyAtMost k` (the vertex-peeling /
elimination-ordering characterization) and proved the degeneracy edge bound.
This file proves the canonical *structural* consequence of degeneracy:

    a k-degenerate finite graph is properly (k + 1)-colorable,

i.e. its chromatic number is at most k + 1. The proof is the classical greedy
argument run along the reverse of the peeling order. This notion (the "coloring
number" bound) is absent from Mathlib at the pinned commit: a search for
`coloringNumber`, `degenera`, and `greedy` under `Combinatorics/SimpleGraph`
returns nothing.

The file is self-contained (Lean module names may not begin with a digit, so the
standalone scripts cannot import one another); it restates the inductive
predicate from script 48 and then builds on it. No `sorry`; the Lean kernel
checks the result.
-/

import Mathlib

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SimpleGraph

/-- A graph is `k`-degenerate if its vertices admit an elimination ordering:
either the graph is empty, or there is a vertex `v` of degree at most `k` whose
incidence set can be deleted, leaving a `k`-degenerate graph. (Same definition
as in script 48, restated so this script compiles standalone.) -/
inductive DegeneracyAtMost (k : ℕ) : SimpleGraph V → Prop
  | bot (G : SimpleGraph V) (h : G = ⊥) : DegeneracyAtMost k G
  | peel (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
      (hdeg : G.degree v ≤ k)
      (hrest : DegeneracyAtMost k (G.deleteIncidenceSet v)) :
      DegeneracyAtMost k G

namespace DegeneracyAtMost

/-- **Greedy coloring theorem.** A `k`-degenerate graph admits a proper
vertex coloring with `k + 1` colors.

The coloring is built in the reverse of the peeling order: color the graph left
after peeling `v`, then assign `v` a color different from the colors of its at
most `k` neighbors; among `k + 1` colors at least one is free. -/
theorem colorable_succ (k : ℕ) {G : SimpleGraph V}
    (h : DegeneracyAtMost k G) : G.Colorable (k + 1) := by
  induction h with
  | bot G hG =>
    -- The empty graph is monochromatically colorable.
    refine ⟨Coloring.mk (fun _ => (0 : Fin (k + 1))) fun {v w} h => ?_⟩
    rw [hG] at h
    simp at h
  | peel G v hdeg hrest ih =>
    let H := G.deleteIncidenceSet v
    obtain ⟨C⟩ := ih
    -- Colors already used by the peeled vertex's neighbors.
    let N := G.neighborFinset v
    let used := Finset.image (fun x => C x) N
    have hcard : Finset.card used ≤ k := by
      calc Finset.card used
          ≤ Finset.card N := Finset.card_image_le
        _ = G.degree v := G.card_neighborFinset_eq_degree v
        _ ≤ k := hdeg
    have hlt : Finset.card used <
        Finset.card (Finset.univ : Finset (Fin (k + 1))) := by
      simp
      omega
    obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    -- Color v with the free color c; every other vertex keeps its old color.
    let color : V → Fin (k + 1) := fun x => if x = v then c else C x
    have valid : ∀ {x y : V}, G.Adj x y → color x ≠ color y := by
      intro x y hxy
      by_cases hx : x = v
      · -- The first endpoint is the peeled vertex v.
        have hadj : G.Adj v y := hx ▸ hxy
        have hnv : y ≠ v := (G.ne_of_adj hadj).symm
        have hyn : y ∈ N := by simpa [N] using hadj
        have hcin : C y ∈ used := Finset.mem_image.mpr ⟨y, hyn, rfl⟩
        have hcc : c ≠ C y := fun e => hc (e ▸ hcin)
        dsimp only [color]
        rw [ite_eq_left hx, ite_eq_right hnv]
        exact hcc
      · by_cases hy : y = v
        · -- The second endpoint is the peeled vertex v.
          have hadj : G.Adj x v := hy ▸ hxy
          have hnv : x ≠ v := G.ne_of_adj hadj
          have hxn : x ∈ N := by simpa [N] using hadj.symm
          have hcin : C x ∈ used := Finset.mem_image.mpr ⟨x, hxn, rfl⟩
          have hcc : c ≠ C x := fun e => hc (e ▸ hcin)
          dsimp only [color]
          rw [ite_eq_right hnv, ite_eq_left hy]
          exact hcc.symm
        · -- Neither endpoint is v: the edge survives in H, where the old
          -- coloring C is already proper.
          have hH : H.Adj x y := by
            rw [deleteIncidenceSet_adj]
            exact ⟨hxy, hx, hy⟩
          have hne2 : C x ≠ C y := C.valid hH
          dsimp only [color]
          rw [ite_eq_right hx, ite_eq_right hy]
          exact hne2
    exact ⟨Coloring.mk color valid⟩

/-- In terms of the chromatic number: `χ(G) ≤ k + 1` for a `k`-degenerate
graph. -/
theorem chromaticNumber_le_succ (k : ℕ) {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : DegeneracyAtMost k G) : G.chromaticNumber ≤ k + 1 :=
  (chromaticNumber_le_iff_colorable (n := k + 1)).mpr (h.colorable_succ k)

/-- The empty graph is `0`-degenerate and hence 1-colorable. -/
example : (⊥ : SimpleGraph V).Colorable 1 :=
  (.bot ⊥ rfl : DegeneracyAtMost 0 (⊥ : SimpleGraph V)).colorable_succ 0

end DegeneracyAtMost
end SimpleGraph
