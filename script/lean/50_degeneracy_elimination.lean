/-
# 50 — Every finite graph admits a degeneracy elimination ordering (hard way)

Scripts 48 and 49 took a *given* degeneracy ordering and derived its two
consequences (the edge bound and greedy coloring). This file supplies the
constructive existence half of the degeneracy characterization:

  whenever a finite graph that is not empty always has a vertex *in its support*
  of degree at most k, repeatedly deleting such vertices terminates (the support
  strictly shrinks at each step), and that recursion is exactly a
  `DegeneracyAtMost k` derivation.

As a concrete consequence, every finite graph on `n` vertices is
`(n - 1)`-degenerate: every vertex has degree `< n`, so any vertex still in the
support is a legal peel. Combined with scripts 48–49 this recovers the universal
bounds `|E| ≤ (n-1)·n` and `χ(G) ≤ n` constructively.

The recursion is well-founded on the cardinality of the support: peeling a
support vertex drops it from the support, so the measure decreases. Self
contained (digit-prefixed script files cannot be imported as Lean modules); the
`DegeneracyAtMost` inductive is restated from script 48. No `sorry`; the Lean
kernel checks the result.
-/

import Mathlib

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SimpleGraph

/-- A graph is `k`-degenerate if its vertices admit an elimination ordering.
(Same definition as in scripts 48–49, restated for standalone compilation.) -/
inductive DegeneracyAtMost (k : ℕ) : SimpleGraph V → Prop
  | bot (G : SimpleGraph V) (h : G = ⊥) : DegeneracyAtMost k G
  | peel (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
      (hdeg : G.degree v ≤ k)
      (hrest : DegeneracyAtMost k (G.deleteIncidenceSet v)) :
      DegeneracyAtMost k G

namespace DegeneracyAtMost

/-- **Constructive elimination-ordering lemma.** If every nonempty graph on `V`
has a vertex *in its support* whose degree is at most `k`, then every graph is
`k`-degenerate. The proof is well-founded recursion on the cardinality of the
support: a peeled support vertex disappears from the support, so the measure
strictly decreases until the empty graph is reached. -/
theorem of_forall_exists_low_degree (k : ℕ)
    (h : ∀ (H : SimpleGraph V) [DecidableRel H.Adj], H ≠ ⊥ →
      ∃ (v : V), v ∈ H.support ∧ H.degree v ≤ k)
    (G : SimpleGraph V) [DecidableRel G.Adj] : DegeneracyAtMost k G := by
  classical
  set_option linter.style.haveILetI false in
  have hrec : ∀ (n : ℕ) (H : SimpleGraph V) (i : DecidableRel H.Adj),
      Fintype.card H.support ≤ n → DegeneracyAtMost k H :=
    fun n =>
      Nat.strong_induction_on n fun n ih H i hn => by
        letI := i
        by_cases hb : H = ⊥
        · exact .bot H hb
        · rcases h H hb with ⟨v, hvs, hvdeg⟩
          let H' := H.deleteIncidenceSet v
          have hpos : 0 < Fintype.card H.support :=
            Fintype.card_pos_iff.mpr ⟨⟨v, hvs⟩⟩
          have hdec : Fintype.card H'.support ≤ Fintype.card H.support - 1 :=
            H.card_support_deleteIncidenceSet hvs
          have hshrink : Fintype.card H'.support < Fintype.card H.support := by
            omega
          have hlt : Fintype.card H'.support < n := hshrink.trans_le hn
          exact .peel H v hvdeg
            (ih (Fintype.card H'.support) hlt H' inferInstance le_rfl)
  exact hrec (Fintype.card G.support) G inferInstance le_rfl

/-- **Every finite graph is `(n - 1)`-degenerate**, where `n` is the number of
vertices. A vertex in the support has degree `< n`
(`degree_lt_card_verts`), hence degree at most `n - 1`. -/
theorem degenerate_card_sub_one (G : SimpleGraph V) [DecidableRel G.Adj] :
    DegeneracyAtMost (Fintype.card V - 1) G := by
  refine of_forall_exists_low_degree (Fintype.card V - 1) ?_ G
  intro H _ hnb
  have hsup : Set.Nonempty H.support :=
    Set.nonempty_iff_ne_empty.mpr fun h =>
      hnb ((support_eq_bot_iff (G := H)).mp h)
  rcases hsup with ⟨v, hv⟩
  refine ⟨v, hv, ?_⟩
  have hlt : H.degree v < Fintype.card V := H.degree_lt_card_verts v
  omega

/-- The complete graph on three vertices is `2`-degenerate, as the universal
construction gives. -/
example : DegeneracyAtMost (Fintype.card (Fin 3) - 1)
    (completeGraph (Fin 3)) :=
  degenerate_card_sub_one _

end DegeneracyAtMost
end SimpleGraph
