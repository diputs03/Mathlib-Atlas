/-
# Script 62 — Incidence chain complex of a combinatorial map (Betti ranks,
# and a second, algebraic proof of the Euler bound χ ≤ 2)

Scripts 55–59 built the planar-map layer *combinatorially*: a map is a finite set
of darts `α` with a fixed-point-free edge involution `τ` and a vertex rotation
`σ`, faces are the cycles of `φ := τ * σ⁻¹`, and script 59 proved
`V - E + F ≤ 2` for connected maps by factoring permutations into
transpositions and counting orbit splits/joins.

This script gives a completely independent, *linear-algebraic* proof. We form
the cellular chain complex over `ℚ`

    C₂ = ℚ[faces]  ---∂₂--->  C₁ = ℚ[edges]  ---∂₁--->  C₀ = ℚ[vertices]

with vertices/edges/faces realized as the finite quotient types
`Quotient (Perm.SameCycle.setoid ·)` (one element per cycle), and with the
oriented incidence matrices

    ∂₁(v,e) = 1_{v = head(e)} − 1_{v = tail(e)},
    ∂₂(e,f) = 1_{e oriented with f} − 1_{e oriented against f}.

We prove, kernel-verified with no `sorry` and no axioms beyond Mathlib:

  1. `∂₁ * ∂₂ = 0` (the face boundary is a closed walk): the key identity
     `τ (φ d) = σ⁻¹ d` makes the vertex-incidence sum telescope around each
     face orbit.
  2. For a connected map (the same `Subgroup.closure {τ,σ}` transitivity
     hypothesis as in scripts 58–59), the transpose kernel of `∂₁` consists
     exactly of the constant vertex functions, so `rank ∂₁ = V − 1`.
  3. Using the primal–dual group identity `closure {τ,φ} = closure {τ,σ}`
     (script 58), `ker ∂₂` consists exactly of the constant face functions, so
     `rank ∂₂ = F − 1` and `b₂ := dim ker ∂₂ = 1`.
  4. Rank–nullity then gives the Betti numbers of a connected orientable map:
        b₀ = 1,  b₁ = E − V − F + 2 = 2 − χ,  b₂ = 1,
     and the alternating-sum identity `χ = b₀ − b₁ + b₂`.
  5. Since `b₁ ≥ 0`, `χ = V − E + F ≤ 2` — a second proof of the connected
     Euler bound (script 59 gave the first), with no topology assumed: the only
     inputs are the permutation relations and connectedness.

The quotient cycle types are also shown to have cardinality equal to the
`orbits` count used in scripts 56/59 (`card_cyc`), so the two developments use
exactly the same V, E, F.

The topological reading (these ranks are the singular homology of the
underlying closed orientable surface) is deliberately *not* asserted here:
realizing the combinatorial map as a CW surface is the layer gap scoped in
note 60. Everything below is finite combinatorics and linear algebra.
-/

import Mathlib

open Equiv

namespace SimpleGraph.ChainEuler

variable (α : Type*) [Fintype α] [DecidableEq α]

/-- Number of cycles (orbits) of a permutation, counting fixed points as
one-element cycles (identical to `CombiMap.orbits` in script 56). -/
def orbits (p : Perm α) : ℕ :=
  Multiset.card p.cycleType + (Fintype.card α - p.cycleType.sum)

/-- Rational indicator `1_{a = b}`. -/
private def qind {β : Type*} [DecidableEq β] (b a : β) : ℚ := if a = b then 1 else 0

private lemma sum_qind {β : Type*} [Fintype β] [DecidableEq β] (b : β) (q : β → ℚ) :
    ∑ a : β, qind b a * q a = q b := by
  have h : ∀ a : β, qind b a * q a = if a = b then q b else 0 := by
    intro a
    by_cases h : a = b
    · simp [qind, h]
    · simp [qind, h]
  rw [Finset.sum_congr rfl (fun x _ => h x)]
  simp [Finset.sum_ite_eq']

/-- Variant of `sum_qind` with the fixed point in the second argument. -/
private lemma sum_qind' {β : Type*} [Fintype β] [DecidableEq β] (a : β) (q : β → ℚ) :
    ∑ b : β, qind b a * q b = q a := by
  have hs : ∀ b : β, qind b a * q b = qind a b * q b := by
    intro b
    have he : qind b a = qind a b := by simp [qind, eq_comm]
    rw [he]
  rw [Finset.sum_congr rfl (fun b _ => hs b)]
  exact sum_qind a q

/-- Cycle classes (orbits) of a permutation as a quotient type. -/
abbrev Cyc (f : Perm α) : Type _ :=
  Quotient (Perm.SameCycle.setoid f)

/-- The class of a point in the cycle quotient. -/
def cyc (f : Perm α) (x : α) : Cyc α f :=
  Quotient.mk'' x

instance cycFintype (f : Perm α) : Fintype (Cyc α f) :=
  @Quotient.fintype α _ (Perm.SameCycle.setoid f)
    (Perm.instDecidableRelSameCycle f)

instance cycDecidableEq (f : Perm α) : DecidableEq (Cyc α f) :=
  @Quotient.decidableEq α _ (Perm.SameCycle.setoid f)
    (Perm.instDecidableRelSameCycle f)

section CycCard

/-- A representative point of a nontrivial cycle factor `c`. -/
private lemma factor_nonempty (f c : Perm α) (hc : c ∈ f.cycleFactorsFinset) :
    c.support.Nonempty :=
  Finset.card_pos.mp
    (zero_lt_two.trans_le
      (Perm.mem_cycleFactorsFinset_iff.mp hc).1.two_le_card_support)

private noncomputable def factorPick (f c : Perm α)
    (hc : c ∈ f.cycleFactorsFinset) : α :=
  Classical.choose (factor_nonempty α f c hc)

private lemma factorPick_mem (f c : Perm α) (hc : c ∈ f.cycleFactorsFinset) :
    factorPick α f c hc ∈ c.support :=
  Classical.choose_spec (factor_nonempty α f c hc)

/-- For a cycle factor `c` and `x ∈ c.support`, `cycleOf f x = c`. -/
private lemma cycleOf_eq_factor {f c : Perm α} (hc : c ∈ f.cycleFactorsFinset)
    {x : α} (hx : x ∈ c.support) : f.cycleOf x = c := by
  have hci := Perm.mem_cycleFactorsFinset_iff.mp hc
  have hcx : c x ≠ x := Perm.mem_support.mp hx
  have hfx : f x ≠ x := by
    have h3 : f x = c x := (hci.2 x hx).symm
    rw [h3]
    exact hcx
  have h1 : f.cycleOf x ∈ f.cycleFactorsFinset :=
    Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Perm.mem_support.mpr hfx)
  have hxin : x ∈ (f.cycleOf x).support :=
    (Perm.mem_support_cycleOf_iff' hfx).mpr Perm.SameCycle.rfl
  by_cases h : f.cycleOf x = c
  · exact h
  · have hd : Perm.Disjoint (f.cycleOf x) c :=
      Perm.cycleFactorsFinset_pairwise_disjoint f h1 hc h
    have hds : _root_.Disjoint (f.cycleOf x).support c.support :=
      Perm.Disjoint.disjoint_support hd
    exact False.elim (Finset.disjoint_left.mp hds hxin hx)

/-- Two points in the support of the same cycle factor lie in the same
`SameCycle` class. -/
private lemma sameCycle_of_factor {f c : Perm α} (hc : c ∈ f.cycleFactorsFinset)
    {x y : α} (hx : x ∈ c.support) (hy : y ∈ c.support) :
    Perm.SameCycle f x y := by
  have hci := Perm.mem_cycleFactorsFinset_iff.mp hc
  have hfx : f x ≠ x := by
    have h3 : f x = c x := (hci.2 x hx).symm
    rw [h3]; exact Perm.mem_support.mp hx
  have hfy : f y ≠ y := by
    have h3 : f y = c y := (hci.2 y hy).symm
    rw [h3]; exact Perm.mem_support.mp hy
  have ex := cycleOf_eq_factor α hc hx
  have ey := cycleOf_eq_factor α hc hy
  exact (Perm.sameCycle_iff_cycleOf_eq_of_mem_support
    (Perm.mem_support.mpr hfx) (Perm.mem_support.mpr hfy)).mpr
    (ex.trans ey.symm)

private def cycForward (f : Perm α) (z : Cyc α f) :
    Function.fixedPoints f ⊕ {c // c ∈ f.cycleFactorsFinset} :=
  Quotient.liftOn z
    (fun x =>
      if h : f x = x then
        Sum.inl ⟨x, h⟩
      else
        Sum.inr ⟨f.cycleOf x,
          Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Perm.mem_support.mpr h)⟩)
    (by
      intro x y hxy
      by_cases hx : f x = x
      · have h1 : x = y := hxy.eq_of_left hx
        have hy : f y = y := by rw [←h1]; exact hx
        have hsub : (⟨x, hx⟩ : Function.fixedPoints f) = ⟨y, hy⟩ := by
          apply Subtype.ext
          exact h1
        rw [dite_eq_left hx, dite_eq_left hy]
        exact congr_arg Sum.inl hsub
      · have hfy : f y ≠ y := by
          intro hy
          have h2 : x = y := hxy.eq_of_right hy
          exact hx (by rw [h2]; exact hy)
        have hcx : f.cycleOf x ∈ f.cycleFactorsFinset :=
          Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Perm.mem_support.mpr hx)
        have hcy : f.cycleOf y ∈ f.cycleFactorsFinset :=
          Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Perm.mem_support.mpr hfy)
        have hc : f.cycleOf x = f.cycleOf y := Perm.SameCycle.cycleOf_eq hxy
        have hsub : (⟨f.cycleOf x, hcx⟩ : {c // c ∈ f.cycleFactorsFinset}) =
            ⟨f.cycleOf y, hcy⟩ := by
          apply Subtype.ext
          exact hc
        rw [dite_eq_right hx, dite_eq_right hfy]
        exact congr_arg Sum.inr hsub)

private noncomputable def cycBackward (f : Perm α) :
    Function.fixedPoints f ⊕ {c // c ∈ f.cycleFactorsFinset} → Cyc α f
  | Sum.inl ⟨x, _⟩ => cyc α f x
  | Sum.inr ⟨c, hc⟩ => cyc α f (factorPick α f c hc)

private lemma cycBackward_forward (f : Perm α) (z : Cyc α f) :
    cycBackward α f (cycForward α f z) = z := by
  induction z using Quotient.inductionOn' with
  | h x =>
    by_cases hx : f x = x
    · have hfw : cycForward α f (Quotient.mk'' x) = Sum.inl ⟨x, hx⟩ := by
        simp only [cycForward, cyc, Quotient.liftOn_mk, dite_eq_left hx]
      rw [hfw]
      simp [cycBackward, cyc]
    · have h1 : f.cycleOf x ∈ f.cycleFactorsFinset :=
        Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Perm.mem_support.mpr hx)
      have hp : factorPick α f (f.cycleOf x) h1 ∈ (f.cycleOf x).support :=
        factorPick_mem α f (f.cycleOf x) h1
      have hs : Perm.SameCycle f (factorPick α f (f.cycleOf x) h1) x :=
        ((Perm.mem_support_cycleOf_iff' hx).mp hp).symm
      have hfw : cycForward α f (Quotient.mk'' x) = Sum.inr ⟨f.cycleOf x, h1⟩ := by
        simp only [cycForward, cyc, Quotient.liftOn_mk, dite_eq_right hx]
      rw [hfw]
      simp [cycBackward, cyc]
      exact Quotient.sound' hs

private lemma cycForward_backward (f : Perm α) :
    ∀ (t : Function.fixedPoints f ⊕ {c // c ∈ f.cycleFactorsFinset}),
      cycForward α f (cycBackward α f t) = t
  | Sum.inl ⟨x, hx⟩ => by
      show cycForward α f (Quotient.mk'' x) = Sum.inl ⟨x, hx⟩
      simp only [cycForward, cyc]
      rw [Quotient.liftOn_mk, dite_eq_left hx]
  | Sum.inr ⟨c, hc⟩ => by
      set p : α := factorPick α f c hc with hpdef
      have hp : p ∈ c.support := factorPick_mem α f c hc
      have hci := Perm.mem_cycleFactorsFinset_iff.mp hc
      have hfx : f p ≠ p := by
        have h3 : f p = c p := (hci.2 p hp).symm
        rw [h3]; exact Perm.mem_support.mp hp
      have eq : f.cycleOf p = c := cycleOf_eq_factor α hc hp
      have hpc : f.cycleOf p ∈ f.cycleFactorsFinset :=
        Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Perm.mem_support.mpr hfx)
      have hsub : (⟨f.cycleOf p, hpc⟩ : {c // c ∈ f.cycleFactorsFinset}) =
          ⟨c, hc⟩ := by
        apply Subtype.ext
        exact eq
      have hfw : cycForward α f (Quotient.mk'' p) = Sum.inr ⟨c, hc⟩ := by
        simp only [cycForward, cyc]
        rw [Quotient.liftOn_mk, dite_eq_right hfx]
        exact congr_arg Sum.inr hsub
      simpa [cycBackward, cyc, hpdef] using hfw

/-- Cycle classes are in bijection with fixed points together with the
nontrivial cycle factors. -/
noncomputable def cycEquiv (f : Perm α) :
    Cyc α f ≃ (Function.fixedPoints f ⊕ {c // c ∈ f.cycleFactorsFinset}) where
  toFun := cycForward α f
  invFun := cycBackward α f
  left_inv := cycBackward_forward α f
  right_inv := cycForward_backward α f

lemma card_cyc (f : Perm α) : Fintype.card (Cyc α f) = orbits α f := by
  simp only [orbits]
  have hsub : Fintype.card {c // c ∈ f.cycleFactorsFinset} =
      f.cycleFactorsFinset.card := Fintype.card_coe f.cycleFactorsFinset
  rw [Fintype.card_congr (cycEquiv α f), Fintype.card_sum,
    Perm.card_fixedPoints f, hsub]
  have hmap : Multiset.card f.cycleType = f.cycleFactorsFinset.card := by
    rw [Perm.cycleType_def]
    simp
  rw [hmap]
  ring

end CycCard

/-- The one-dimensional subspace of constant functions on `β`. -/
def constLin (β : Type*) [Fintype β] [DecidableEq β] : ℚ →ₗ[ℚ] (β → ℚ) where
  toFun c _ := c
  map_add' _ _ := funext fun _ => rfl
  map_smul' _ _ := funext fun _ => rfl

lemma constLin_injective (β : Type*) [Fintype β] [DecidableEq β] [Nonempty β] :
    Function.Injective (constLin β) := by
  intro c1 c2 h
  have he : constLin β c1 = constLin β c2 := h
  exact congr_fun he (Classical.arbitrary β)

lemma finrank_constLin (β : Type*) [Fintype β] [DecidableEq β] [Nonempty β] :
    Module.finrank ℚ (LinearMap.range (constLin β)) = 1 := by
  have hker : LinearMap.ker (constLin β) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact constLin_injective β
  have h := (constLin β).finrank_range_add_finrank_ker
  rw [hker] at h
  simp at h
  simpa using h

/-- If a function on the cycle quotient of `g` is unchanged by one `f` step
and trivial under `g`, it is constant along the orbit of the group generated
by `f` and `g`. -/
lemma orbit_quotient_const (g f : Perm α) (q : Cyc α g → ℚ)
    (h_step : ∀ x : α, q (cyc α g (f x)) = q (cyc α g x))
    {x y : α}
    (h : y ∈ MulAction.orbit (Subgroup.closure ({f, g} : Set (Perm α))) x) :
    q (cyc α g y) = q (cyc α g x) := by
  let K : Subgroup (Perm α) :=
    { carrier := {p | ∀ z : α, q (cyc α g (p z)) = q (cyc α g z)}
      one_mem' := fun z => rfl
      mul_mem' := fun {a b} ha hb z => by
        simpa [mul_apply] using (ha (b z)).trans (hb z)
      inv_mem' := fun {a} ha z => by
        have hq := ha (a⁻¹ z)
        simpa using hq.symm }
  have hf : f ∈ K := h_step
  have hg : g ∈ K := fun z => by
    apply congr_arg q
    exact Quotient.sound' ⟨(-1 : ℤ), by simp⟩
  have hsub : ({f, g} : Set (Perm α)) ⊆ (K : Set (Perm α)) := by
    intro u hu
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with (rfl | rfl)
    · exact hf
    · exact hg
  have hle : Subgroup.closure ({f, g} : Set (Perm α)) ≤ K :=
    (Subgroup.closure_le (K := K)).mpr hsub
  obtain ⟨pg, hpg⟩ := MulAction.mem_orbit_iff.mp h
  have hpin : (pg : Perm α) ∈ K := hle pg.prop
  have hmain := hpin x
  have hyx : cyc α g y = cyc α g ((pg : Perm α) x) := by
    rw [←hpg]
    rfl
  exact (congr_arg q hyx).trans hmain

/-- A combinatorial (orientable) map (restated from script 56): darts with a
fixed-point-free edge involution `edge` and a vertex rotation `vert`. -/
structure Map where
  /-- Edge involution τ. -/
  edge : Perm α
  /-- τ is an involution. -/
  edge_invol : edge ^ 2 = 1
  /-- τ has no fixed point. -/
  edge_noFix : ∀ x : α, edge x ≠ x
  /-- Vertex rotation σ. -/
  vert : Perm α

namespace Map

variable (M : Map α)

/-- Face permutation φ = τ · σ⁻¹. -/
def face : Perm α := M.edge * M.vert⁻¹

/-- Vertex cycle quotient (one element per vertex). -/
abbrev VCyc : Type _ := Cyc α M.vert

/-- Edge cycle quotient (one element per edge). -/
abbrev ECyc : Type _ := Cyc α M.edge

/-- Face cycle quotient (one element per face). -/
abbrev FCyc : Type _ := Cyc α (face α M)

/-- The vertex class of a dart. -/
def vcyc (x : α) : VCyc α M := cyc α M.vert x

/-- The edge class of a dart. -/
def ecyc (x : α) : ECyc α M := cyc α M.edge x

/-- The face class of a dart. -/
def fcyc (x : α) : FCyc α M := cyc α (face α M) x

/-- Number of vertices = cycles of σ. -/
def vertices : ℕ := orbits α M.vert

/-- Number of edges = cycles of τ (each a 2-cycle). -/
def edges : ℕ := orbits α M.edge

/-- Number of faces = cycles of φ. -/
def faces : ℕ := orbits α (face α M)

lemma card_VCyc : Fintype.card (VCyc α M) = M.vertices := card_cyc α M.vert

lemma card_ECyc : Fintype.card (ECyc α M) = M.edges := card_cyc α M.edge

lemma card_FCyc : Fintype.card (FCyc α M) = M.faces := card_cyc α (face α M)

section EdgeFibers

omit [Fintype α] [DecidableEq α] in
lemma edge_apply2 (x : α) : M.edge (M.edge x) = x := by
  have h : (M.edge ^ 2) x = x := by
    rw [M.edge_invol]
    rfl
  simpa [pow_two] using h

omit [Fintype α] [DecidableEq α] in
lemma edge_inv : M.edge⁻¹ = M.edge := by
  ext x
  have h : M.edge (M.edge x) = x := edge_apply2 α M x
  have h' : M.edge (M.edge⁻¹ x) = x := by simp
  exact M.edge.injective (h'.trans h.symm)

/-- A τ-class of a dart contains exactly the dart and its reverse. -/
lemma sameCycle_edge_iff {x y : α} :
    Perm.SameCycle M.edge x y ↔ y = x ∨ y = M.edge x := by
  constructor
  · rintro ⟨i, hi⟩
    have h2 : M.edge ^ (2 : ℤ) = 1 := by exact_mod_cast M.edge_invol
    by_cases h : i % 2 = 0
    · have hk : ∃ k : ℤ, i = 2 * k := ⟨i / 2, by omega⟩
      rcases hk with ⟨k, rfl⟩
      have he : (M.edge ^ (2 * k : ℤ)) x = x := by
        rw [zpow_mul, h2]; simp
      rw [he] at hi
      exact Or.inl hi.symm
    · have hk : ∃ k : ℤ, i = 2 * k + 1 := ⟨(i - 1) / 2, by omega⟩
      rcases hk with ⟨k, rfl⟩
      have he : (M.edge ^ (2 * k + 1 : ℤ)) x = M.edge x := by
        rw [zpow_add, zpow_mul, h2]; simp
      rw [he] at hi
      exact Or.inr hi.symm
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, edge_apply2 α M x⟩

/-- A chosen representative dart for each edge. -/
noncomputable def edgeRep (e : ECyc α M) : α :=
  Classical.choose (Quotient.exists_rep e)

omit [Fintype α] [DecidableEq α] in
lemma edgeRep_class (e : ECyc α M) :
    ecyc α M (edgeRep α M e) = e :=
  Classical.choose_spec (Quotient.exists_rep e)

lemma edge_class_iff {e : ECyc α M} {x : α} :
    ecyc α M x = e ↔
      x = edgeRep α M e ∨ x = M.edge (edgeRep α M e) := by
  set r : α := edgeRep α M e with hrdef
  have hcr : ecyc α M r = e := edgeRep_class α M e
  rw [hcr]
  have h2 : ecyc α M x = ecyc α M r ↔ Perm.SameCycle M.edge x r := Quotient.eq''
  rw [h2, sameCycle_edge_iff α M]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · have h3 : M.edge r = x := by rw [h, edge_apply2 α M x]
      exact Or.inr h3.symm
  · rintro (rfl | rfl)
    · exact Perm.SameCycle.rfl
    · exact ⟨1, edge_apply2 α M r⟩

lemma edgeRep_inj {e e' : ECyc α M} (h : edgeRep α M e = edgeRep α M e') : e = e' := by
  have hh := congr_arg (ecyc α M) h
  rw [edgeRep_class α M e, edgeRep_class α M e'] at hh
  exact hh

/-- One representative dart per edge. -/
noncomputable def reps : Finset α := Finset.image (edgeRep α M) Finset.univ

lemma reps_edgeRep {r : α} (hr : r ∈ reps α M) :
    ∃ e : ECyc α M, edgeRep α M e = r := by
  simpa [reps, Finset.mem_image] using hr

lemma edgeRep_mem_reps (e : ECyc α M) : edgeRep α M e ∈ reps α M := by
  apply Finset.mem_image.mpr
  exact ⟨e, Finset.mem_univ e, rfl⟩

lemma tau_rep_notin {r : α} (hr : r ∈ reps α M) : M.edge r ∉ reps α M := by
  obtain ⟨e, he⟩ := reps_edgeRep α M hr
  intro h
  obtain ⟨e', _, he'⟩ := Finset.mem_image.mp h
  have hce : ecyc α M (M.edge r) = e' := by
    rw [he']
    exact edgeRep_class α M e'
  have hcr : ecyc α M (M.edge r) = e := by
    rw [← he]
    exact (edge_class_iff α M (e := e) (x := M.edge (edgeRep α M e))).mpr
      (Or.inr rfl)
  have hee : e' = e := hce.trans hcr.symm
  rw [hee] at he'
  exact M.edge_noFix r (he'.trans he.symm)

/-- The reverse darts of the representatives. -/
noncomputable def tauReps : Finset α := Finset.image M.edge (reps α M)

lemma disjoint_reps : _root_.Disjoint (reps α M) (tauReps α M) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx'
  exact tau_rep_notin α M hr hx

lemma reps_union : (reps α M) ∪ (tauReps α M) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  set e : ECyc α M := ecyc α M x
  set r : α := edgeRep α M e
  have hx : x = r ∨ x = M.edge r :=
    (edge_class_iff α M (e := e) (x := x)).mp rfl
  rcases hx with (rfl | rfl)
  · exact Finset.mem_union_left _ (edgeRep_mem_reps α M e)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨r, edgeRep_mem_reps α M e, rfl⟩)

end EdgeFibers

section FaceFibers

lemma face_apply (x : α) : face α M x = M.edge (M.vert⁻¹ x) := rfl

/-- The key map relation: crossing the edge after a face step lands at the
previous dart around the vertex, `τ (φ d) = σ⁻¹ d`. -/
lemma tau_face (x : α) : M.edge (face α M x) = M.vert⁻¹ x := by
  rw [face_apply, edge_apply2]

lemma cyc_sigma_inv (x : α) :
    vcyc α M (M.vert⁻¹ x) = vcyc α M x :=
  Quotient.sound' ⟨(1 : ℤ), by simp⟩

lemma cyc_face_self (x : α) :
    fcyc α M (face α M x) = fcyc α M x :=
  Quotient.sound' ⟨(-1 : ℤ), by simp⟩

lemma cyc_face_inv (x : α) :
    fcyc α M ((face α M)⁻¹ x) = fcyc α M x :=
  Quotient.sound' ⟨(1 : ℤ), by simp⟩

/-- The darts carried by a given face cycle. -/
def faceFiber (f : FCyc α M) : Finset α :=
  Finset.univ.filter (fun z => fcyc α M z = f)

lemma mem_faceFiber {z : α} {f : FCyc α M} :
    z ∈ faceFiber α M f ↔ fcyc α M z = f := by
  simp [faceFiber]

/-- φ permutes each face fiber, so the fiber is invariant as a finset. -/
lemma face_image_fiber (f : FCyc α M) :
    Finset.image (face α M) (faceFiber α M f) = faceFiber α M f := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have h : fcyc α M (face α M z) = f := by
      rw [cyc_face_self α M z, (mem_faceFiber α M).mp hz]
    exact (mem_faceFiber α M).mpr h
  · intro y hy
    have hfy : fcyc α M y = f := (mem_faceFiber α M).mp hy
    have h1 : (face α M)⁻¹ y ∈ faceFiber α M f := by
      rw [mem_faceFiber, cyc_face_inv α M y, hfy]
    have h2 : face α M ((face α M)⁻¹ y) = y := by simp
    exact Finset.mem_image.mpr ⟨(face α M)⁻¹ y, h1, h2⟩

end FaceFibers

section Connectedness

/-- The group generated by τ and σ. -/
def vertGroup : Subgroup (Perm α) :=
  Subgroup.closure ({M.edge, M.vert} : Set (Perm α))

/-- The group generated by τ and φ. -/
def faceGroup : Subgroup (Perm α) :=
  Subgroup.closure ({M.edge, face α M} : Set (Perm α))

/-- A map is connected if the τ/σ group acts transitively on darts. -/
def Connected : Prop :=
  ∀ (x : α), MulAction.orbit M.vertGroup x = Set.univ

omit [Fintype α] [DecidableEq α] in
lemma connected_iff :
    M.Connected ↔ ∀ (x y : α), y ∈ MulAction.orbit M.vertGroup x := by
  simp [Connected, Set.eq_univ_iff_forall]

omit [Fintype α] [DecidableEq α] in
lemma face_mem_vertGroup : face α M ∈ M.vertGroup :=
  M.vertGroup.mul_mem
    (Subgroup.subset_closure (by simp : M.edge ∈ ({M.edge, M.vert} : Set (Perm α))))
    (M.vertGroup.inv_mem'
      (Subgroup.subset_closure (by simp : M.vert ∈ ({M.edge, M.vert} : Set (Perm α)))))

omit [Fintype α] [DecidableEq α] in
lemma vert_eq_face_inv_mul_edge : M.vert = (face α M)⁻¹ * M.edge := by
  calc M.vert
      = (M.vert * M.edge⁻¹) * M.edge := by simp [mul_assoc]
    _ = (face α M)⁻¹ * M.edge := by rw [face, mul_inv_rev, inv_inv]

/-- The primal and dual transitivity groups coincide (script 58). -/
lemma faceGroup_eq_vertGroup : M.faceGroup = M.vertGroup := by
  have h1 : ({M.edge, face α M} : Set (Perm α)) ⊆ M.vertGroup := by
    intro g hg
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with (rfl | rfl)
    · exact Subgroup.subset_closure (by simp : M.edge ∈ ({M.edge, M.vert} : Set (Perm α)))
    · exact face_mem_vertGroup α M
  have h2 : M.faceGroup ≤ M.vertGroup := (Subgroup.closure_le (K := M.vertGroup)).mpr h1
  have h3 : ({M.edge, M.vert} : Set (Perm α)) ⊆ M.faceGroup := by
    intro g hg
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with (rfl | rfl)
    · exact Subgroup.subset_closure (by simp : M.edge ∈ ({M.edge, face α M} : Set (Perm α)))
    · rw [vert_eq_face_inv_mul_edge α M]
      exact M.faceGroup.mul_mem
        (M.faceGroup.inv_mem'
          (Subgroup.subset_closure (by simp : face α M ∈ ({M.edge, face α M} : Set (Perm α)))))
        (Subgroup.subset_closure (by simp : M.edge ∈ ({M.edge, face α M} : Set (Perm α))))
  have h4 : M.vertGroup ≤ M.faceGroup := (Subgroup.closure_le (K := M.faceGroup)).mpr h3
  exact le_antisymm h2 h4

end Connectedness

/-- An edge equation at representatives gives the equation at every dart. -/
lemma edge_step_forall (g : Perm α) (q : Cyc α g → ℚ)
    (h : ∀ e : ECyc α M,
      q (cyc α g (M.edge (edgeRep α M e))) = q (cyc α g (edgeRep α M e))) :
    ∀ z : α, q (cyc α g (M.edge z)) = q (cyc α g z) := by
  intro z
  set e : ECyc α M := ecyc α M z
  set r : α := edgeRep α M e
  have hz : z = r ∨ z = M.edge r :=
    (edge_class_iff α M (e := e) (x := z)).mp rfl
  rcases hz with (rfl | rfl)
  · exact (h e).symm
  · exact h e

section LinearAlgebra

variable [Nonempty α]

omit [Fintype α] [DecidableEq α] in
instance nonempty_VCyc : Nonempty (VCyc α M) :=
  ⟨vcyc α M (Classical.arbitrary α)⟩

omit [Fintype α] [DecidableEq α] in
instance nonempty_ECyc : Nonempty (ECyc α M) :=
  ⟨ecyc α M (Classical.arbitrary α)⟩

omit [Fintype α] [DecidableEq α] in
instance nonempty_FCyc : Nonempty (FCyc α M) :=
  ⟨fcyc α M (Classical.arbitrary α)⟩

/-- Vertex–edge incidence matrix ∂₁ (rows vertices, columns edges). -/
noncomputable def D1 : Matrix (VCyc α M) (ECyc α M) ℚ := fun v e =>
  let r := edgeRep α M e
  qind v (vcyc α M (M.edge r)) - qind v (vcyc α M r)

/-- Edge–face incidence matrix ∂₂ (rows edges, columns faces). -/
noncomputable def D2 : Matrix (ECyc α M) (FCyc α M) ℚ := fun e f =>
  let r := edgeRep α M e
  qind f (fcyc α M r) - qind f (fcyc α M (M.edge r))

/-- The transpose of ∂₁ sends a vertex weighting to head-minus-tail along each
edge. -/
lemma D1_transpose_mulVec (q : VCyc α M → ℚ) (e : ECyc α M) :
    (D1 α M).transpose.mulVec q e =
      q (vcyc α M (M.edge (edgeRep α M e))) - q (vcyc α M (edgeRep α M e)) := by
  set r : α := edgeRep α M e
  have h : (D1 α M).transpose.mulVec q e = ∑ v : VCyc α M, (D1 α M v e) * q v := rfl
  rw [h]
  have hs : ∀ v : VCyc α M, (D1 α M v e) * q v =
      qind v (vcyc α M (M.edge r)) * q v -
        qind v (vcyc α M r) * q v := by
    intro v; rfl
  rw [Finset.sum_congr rfl (fun v _ => hs v), Finset.sum_sub_distrib,
    sum_qind, sum_qind]
  rfl

/-- ∂₂ sends a face weighting to the signed face difference across each edge. -/
lemma D2_mulVec (x : FCyc α M → ℚ) (e : ECyc α M) :
    (D2 α M).mulVec x e =
      x (fcyc α M (edgeRep α M e)) -
        x (fcyc α M (M.edge (edgeRep α M e))) := by
  set r : α := edgeRep α M e
  have h : (D2 α M).mulVec x e = ∑ f : FCyc α M, (D2 α M e f) * x f := rfl
  rw [h]
  have hs : ∀ f : FCyc α M, (D2 α M e f) * x f =
      qind f (fcyc α M r) * x f -
      qind f (fcyc α M (M.edge r)) * x f := by
    intro f; rfl
  rw [Finset.sum_congr rfl (fun f _ => hs f), Finset.sum_sub_distrib,
    sum_qind, sum_qind]
  rfl

/-- `ker ∂₁ᵀ` is exactly the constant vertex functions. -/
lemma ker_D1_transpose (hconn : M.Connected) :
    LinearMap.ker (D1 α M).transpose.mulVecLin =
      LinearMap.range (constLin (VCyc α M)) := by
  ext q
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hq
    have he : ∀ e : ECyc α M,
        q (vcyc α M (M.edge (edgeRep α M e))) = q (vcyc α M (edgeRep α M e)) := by
      intro e
      have hz : (D1 α M).transpose.mulVec q e = 0 := by
        rw [hq]; rfl
      rw [D1_transpose_mulVec α M q e] at hz
      exact sub_eq_zero.mp hz
    have hstep : ∀ z : α,
        q (vcyc α M (M.edge z)) = q (vcyc α M z) :=
      edge_step_forall α M M.vert q he
    let v0 : VCyc α M := vcyc α M (Classical.arbitrary α)
    have hc : ∀ (v : VCyc α M), q v = q v0 := by
      intro v
      let x : α := Classical.choose (Quotient.exists_rep v)
      have hx : vcyc α M x = v := Classical.choose_spec (Quotient.exists_rep v)
      let y : α := Classical.choose (Quotient.exists_rep v0)
      have hy : vcyc α M y = v0 := Classical.choose_spec (Quotient.exists_rep v0)
      have hxy : y ∈ MulAction.orbit M.vertGroup x :=
        (connected_iff α M).mp hconn x y
      have hq' : q (vcyc α M y) = q (vcyc α M x) :=
        orbit_quotient_const α M.vert M.edge q hstep hxy
      rw [hy, hx] at hq'
      exact hq'.symm
    refine ⟨q v0, ?_⟩
    funext v
    exact hc v
  · rintro ⟨c, rfl⟩
    intro e
    rw [D1_transpose_mulVec α M _ e]
    simp

/-- `ker ∂₂` is exactly the constant face functions (dual connectedness). -/
lemma ker_D2 (hconn : M.Connected) :
    LinearMap.ker (D2 α M).mulVecLin =
      LinearMap.range (constLin (FCyc α M)) := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hx
    have he : ∀ e : ECyc α M,
        x (fcyc α M (edgeRep α M e)) =
          x (fcyc α M (M.edge (edgeRep α M e))) := by
      intro e
      have hz : (D2 α M).mulVec x e = 0 := by rw [hx]; rfl
      rw [D2_mulVec α M x e] at hz
      exact sub_eq_zero.mp hz
    have hstep : ∀ z : α,
        x (fcyc α M (M.edge z)) = x (fcyc α M z) :=
      edge_step_forall α M (face α M) x (fun e => (he e).symm)
    let f0 : FCyc α M := fcyc α M (Classical.arbitrary α)
    have hgrp : M.faceGroup = M.vertGroup := faceGroup_eq_vertGroup α M
    have hc : ∀ (f : FCyc α M), x f = x f0 := by
      intro f
      let z : α := Classical.choose (Quotient.exists_rep f)
      have hz : fcyc α M z = f := Classical.choose_spec (Quotient.exists_rep f)
      let w : α := Classical.choose (Quotient.exists_rep f0)
      have hw : fcyc α M w = f0 := Classical.choose_spec (Quotient.exists_rep f0)
      have hzw : w ∈ MulAction.orbit M.vertGroup z :=
        (connected_iff α M).mp hconn z w
      rw [←hgrp] at hzw
      have hx' : x (fcyc α M w) = x (fcyc α M z) :=
        orbit_quotient_const α (face α M) M.edge x hstep hzw
      rw [hw, hz] at hx'
      exact hx'.symm
    refine ⟨x f0, ?_⟩
    funext f
    exact hc f
  · rintro ⟨c, rfl⟩
    intro e
    rw [D2_mulVec α M _ e]
    simp

/-- `rank ∂₁ = V − 1` for a connected map. -/
lemma rank_D1 (hconn : M.Connected) :
    Matrix.rank (D1 α M) = Fintype.card (VCyc α M) - 1 := by
  let t := (D1 α M).transpose.mulVecLin
  have hker : LinearMap.ker t = LinearMap.range (constLin (VCyc α M)) :=
    ker_D1_transpose α M hconn
  have hdim := t.finrank_range_add_finrank_ker
  have hV : Module.finrank ℚ (VCyc α M → ℚ) = Fintype.card (VCyc α M) :=
    Module.finrank_fintype_fun_eq_card
  have hk : Module.finrank ℚ (LinearMap.ker t) = 1 := by
    rw [hker, finrank_constLin (VCyc α M)]
  have hrt : Matrix.rank (D1 α M).transpose = Matrix.rank (D1 α M) :=
    Matrix.rank_transpose
  rw [hV] at hdim
  rw [hk] at hdim
  rw [← hrt]
  have hpos : 0 < Fintype.card (VCyc α M) := Fintype.card_pos
  omega

/-- `rank ∂₂ = F − 1` for a connected map. -/
lemma rank_D2 (hconn : M.Connected) :
    Matrix.rank (D2 α M) = Fintype.card (FCyc α M) - 1 := by
  let b := (D2 α M).mulVecLin
  have hker : LinearMap.ker b = LinearMap.range (constLin (FCyc α M)) :=
    ker_D2 α M hconn
  have hdim := b.finrank_range_add_finrank_ker
  have hF : Module.finrank ℚ (FCyc α M → ℚ) = Fintype.card (FCyc α M) :=
    Module.finrank_fintype_fun_eq_card
  have hk : Module.finrank ℚ (LinearMap.ker b) = 1 := by
    rw [hker, finrank_constLin (FCyc α M)]
  rw [hF] at hdim
  have hpos : 0 < Fintype.card (FCyc α M) := Fintype.card_pos
  omega

/-- Dimension of `ker ∂₁`: `E − V + 1`. -/
lemma finrank_ker_D1 (hconn : M.Connected) :
    Module.finrank ℚ (LinearMap.ker (D1 α M).mulVecLin) =
      Fintype.card (ECyc α M) - (Fintype.card (VCyc α M) - 1) := by
  have hdim := (D1 α M).mulVecLin.finrank_range_add_finrank_ker
  have hE : Module.finrank ℚ (ECyc α M → ℚ) = Fintype.card (ECyc α M) :=
    Module.finrank_fintype_fun_eq_card
  rw [hE] at hdim
  have hr : Module.finrank ℚ (LinearMap.range (D1 α M).mulVecLin) =
      Matrix.rank (D1 α M) := rfl
  rw [hr, rank_D1 α M hconn] at hdim
  have hpos : 0 < Fintype.card (VCyc α M) := Fintype.card_pos
  omega

/-- `b₂ = dim ker ∂₂ = 1`. -/
lemma b2_eq_one (hconn : M.Connected) :
    Module.finrank ℚ (LinearMap.ker (D2 α M).mulVecLin) = 1 := by
  rw [ker_D2 α M hconn, finrank_constLin (FCyc α M)]

/-- Sum over edges equals the sum over their representative darts. -/
private lemma sum_edge_reps (v : VCyc α M) (f : FCyc α M) :
    ∑ (e : ECyc α M), (D1 α M) v e * (D2 α M) e f =
      ∑ r ∈ reps α M,
        (qind v (vcyc α M (M.edge r)) - qind v (vcyc α M r)) *
          (qind f (fcyc α M r) - qind f (fcyc α M (M.edge r))) := by
  have hi : Set.InjOn (edgeRep α M) (Finset.univ : Finset (ECyc α M)) :=
    fun e _ e' _ h => edgeRep_inj α M h
  rw [reps, ← Finset.sum_image hi]
  apply Finset.sum_congr rfl
  intro e _
  rfl

/-- Entry of ∂₁ * ∂₂ is zero: the vertex-incidence sum telescopes around the
face walk. -/
lemma D1_mul_D2_entry (v : VCyc α M) (f : FCyc α M) :
    ((D1 α M) * (D2 α M)) v f = 0 := by
  set A : α → ℚ := fun z => qind v (vcyc α M z) with hA
  set B : α → ℚ := fun z => qind f (fcyc α M z) with hB
  rw [Matrix.mul_apply]
  rw [sum_edge_reps α M v f]
  have hmain : ∑ r ∈ reps α M,
        (A (M.edge r) - A r) * (B r - B (M.edge r)) =
      ∑ z ∈ faceFiber α M f, (A (M.edge z) - A z) := by
    let R := reps α M
    let T := tauReps α M
    have hdisj : _root_.Disjoint R T := disjoint_reps α M
    have hunion : R ∪ T = Finset.univ := reps_union α M
    have hiT : Set.InjOn M.edge R := fun x _ y _ h => M.edge.injective h
    have h_eq1 : ∑ r ∈ R, A (M.edge r) * B (M.edge r) = ∑ x ∈ T, A x * B x := by
      rw [tauReps, Finset.sum_image hiT]; rfl
    have h_eq2 : ∑ r ∈ R, A r * B (M.edge r) = ∑ x ∈ T, A (M.edge x) * B x := by
      rw [tauReps, Finset.sum_image hiT]
      apply Finset.sum_congr rfl
      intro x _
      rw [edge_apply2 α M x]
    have h_exp : ∑ r ∈ R, (A (M.edge r) - A r) * (B r - B (M.edge r)) =
        (∑ r ∈ R, A (M.edge r) * B r) + (∑ r ∈ R, A r * B (M.edge r)) -
          (∑ r ∈ R, A (M.edge r) * B (M.edge r)) - (∑ r ∈ R, A r * B r) := by
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sub, sub_mul]; ring
    rw [h_exp, h_eq1, h_eq2]
    have h_pos : (∑ r ∈ R, A (M.edge r) * B r) + ∑ x ∈ T, A (M.edge x) * B x =
        ∑ z ∈ (R ∪ T), A (M.edge z) * B z := by
      rw [Finset.sum_union hdisj]; ring
    have h_neg2 : (∑ x ∈ T, A x * B x) + ∑ r ∈ R, A r * B r =
        ∑ z ∈ (R ∪ T), A z * B z := by
      rw [Finset.sum_union hdisj]; ring
    rw [h_pos, sub_sub, h_neg2, hunion, ← Finset.sum_sub_distrib]
    have hterm : ∀ z : α,
        (A (M.edge z) * B z) - A z * B z = (A (M.edge z) - A z) * B z := by
      intro z; ring
    rw [Finset.sum_congr rfl (fun z _ => hterm z)]
    have hB : ∀ z : α, B z = if fcyc α M z = f then (1 : ℚ) else 0 := by
      intro z; simp [hB, qind]
    rw [Finset.sum_congr rfl (fun z _ => by rw [hB z, mul_ite, mul_one, mul_zero])]
    rw [← Finset.sum_filter]
    rfl
  rw [hmain]
  have himg := face_image_fiber α M f
  have hiφ : Set.InjOn (face α M) (faceFiber α M f) :=
    fun x _ y _ h => (face α M).injective h
  have h_shift : ∑ z ∈ faceFiber α M f, A (M.edge z) =
      ∑ z ∈ faceFiber α M f, A (M.edge (face α M z)) := by
    rw [← Finset.sum_image hiφ, himg]
  rw [h_shift]
  have h_eq : ∀ z ∈ faceFiber α M f, A (M.edge (face α M z)) = A z := by
    intro z _
    have h1 : M.edge (face α M z) = M.vert⁻¹ z := tau_face α M z
    rw [h1]
    have h2 : vcyc α M (M.vert⁻¹ z) = vcyc α M z := cyc_sigma_inv α M z
    simp [hA, qind, h2]
  rw [Finset.sum_congr rfl h_eq, Finset.sum_sub_distrib, sub_self]

/-- The chain complex condition `∂₁ * ∂₂ = 0`. -/
lemma d1_comp_d2 : (D1 α M) * (D2 α M) = 0 := by
  ext i j
  exact D1_mul_D2_entry α M i j

/-- `im ∂₂ ≤ ker ∂₁`. -/
lemma range_D2_le_ker_D1 :
    LinearMap.range (D2 α M).mulVecLin ≤ LinearMap.ker (D1 α M).mulVecLin := by
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  rw [LinearMap.mem_ker, ← Matrix.mulVec_mulVec, d1_comp_d2 α M]
  simp

/-- `ker ∂₁` as a submodule of edge chains. -/
def K1 : Submodule ℚ (ECyc α M → ℚ) :=
  LinearMap.ker (D1 α M).mulVecLin

/-- `im ∂₂` as a submodule of edge chains. -/
def I2 : Submodule ℚ (ECyc α M → ℚ) :=
  LinearMap.range (D2 α M).mulVecLin

/-- `im ∂₂` viewed inside `ker ∂₁`. -/
def I2' : Submodule ℚ (K1 α M) :=
  Submodule.comap (K1 α M).subtype (I2 α M)

/-- The first Betti number `b₁ = E − V − F + 2 = 2 − χ`, realized as
`finrank (ker ∂₁ ⧸ im ∂₂)`. -/
theorem b1_eq (hconn : M.Connected) :
    Module.finrank ℚ ((K1 α M) ⧸ (I2' α M)) =
      Fintype.card (ECyc α M) - Fintype.card (VCyc α M) - Fintype.card (FCyc α M) + 2 := by
  have hle : I2 α M ≤ K1 α M := range_D2_le_ker_D1 α M
  have hEquiv : I2' α M ≃ₗ[ℚ] I2 α M :=
    { toFun := fun x => ⟨(x : ECyc α M → ℚ), x.prop⟩
      invFun := fun y => ⟨⟨(y : ECyc α M → ℚ), hle y.prop⟩, y.prop⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hfi : Module.finrank ℚ (I2' α M) = Module.finrank ℚ (I2 α M) :=
    hEquiv.finrank_eq
  have hq := (I2' α M).finrank_quotient_add_finrank
  have hrk2 : Module.finrank ℚ (I2 α M) = Matrix.rank (D2 α M) := rfl
  have hk1 := finrank_ker_D1 α M hconn
  have hr2 := rank_D2 α M hconn
  have hposV : 0 < Fintype.card (VCyc α M) := Fintype.card_pos
  have hposF : 0 < Fintype.card (FCyc α M) := Fintype.card_pos
  rw [hfi, hrk2, hr2] at hq
  rw [hk1] at hq
  omega

/-- `b₀ = V − rank ∂₁ = 1`. -/
theorem b0_eq_one (hconn : M.Connected) :
    Fintype.card (VCyc α M) - Matrix.rank (D1 α M) = 1 := by
  rw [rank_D1 α M hconn]
  have hpos : 0 < Fintype.card (VCyc α M) := Fintype.card_pos
  omega

/-- Second, algebraic proof of the connected Euler bound:
`χ = V − E + F ≤ 2`, because `rank ∂₂ = F − 1 ≤ dim ker ∂₁ = E − V + 1`. -/
theorem algebraic_euler_bound (hconn : M.Connected) :
    (Fintype.card (VCyc α M) : ℤ) - Fintype.card (ECyc α M) +
        Fintype.card (FCyc α M) ≤ 2 := by
  have hle : I2 α M ≤ K1 α M := range_D2_le_ker_D1 α M
  let K2 := LinearMap.ker (D2 α M).mulVecLin
  have hdim1 := (D1 α M).mulVecLin.finrank_range_add_finrank_ker
  have hdim2 := (D2 α M).mulVecLin.finrank_range_add_finrank_ker
  have hr1n := rank_D1 α M hconn
  have hr2n := rank_D2 α M hconn
  have hb2 : Module.finrank ℚ K2 = 1 := b2_eq_one α M hconn
  have hle2 : Matrix.rank (D2 α M) ≤ Module.finrank ℚ (K1 α M) :=
    Submodule.finrank_le_finrank_of_le hle
  have e1 : (Matrix.rank (D1 α M) : ℤ) + Module.finrank ℚ (K1 α M) =
      (Fintype.card (ECyc α M) : ℤ) := by exact_mod_cast hdim1
  have e2 : (Matrix.rank (D2 α M) : ℤ) + Module.finrank ℚ K2 =
      (Fintype.card (FCyc α M) : ℤ) := by exact_mod_cast hdim2
  have r1 : (Matrix.rank (D1 α M) : ℤ) = (Fintype.card (VCyc α M) : ℤ) - 1 := by
    have h1le : 1 ≤ Fintype.card (VCyc α M) := Fintype.card_pos
    have : (Matrix.rank (D1 α M) : ℤ) = ↑(Fintype.card (VCyc α M) - 1) :=
      by exact_mod_cast hr1n
    rw [this, Nat.cast_sub h1le]; simp
  have r2 : (Matrix.rank (D2 α M) : ℤ) = (Fintype.card (FCyc α M) : ℤ) - 1 := by
    have h1le : 1 ≤ Fintype.card (FCyc α M) := Fintype.card_pos
    have : (Matrix.rank (D2 α M) : ℤ) = ↑(Fintype.card (FCyc α M) - 1) :=
      by exact_mod_cast hr2n
    rw [this, Nat.cast_sub h1le]; simp
  have hk2 : (Module.finrank ℚ K2 : ℤ) = 1 := by exact_mod_cast hb2
  have hle3 : (Matrix.rank (D2 α M) : ℤ) ≤ Module.finrank ℚ K1 :=
    by exact_mod_cast hle2
  linarith

end LinearAlgebra

/-- The Euler bound without a nonemptiness assumption (empty map: χ = 0). -/
theorem euler_bound (hconn : M.Connected) :
    (Fintype.card (VCyc α M) : ℤ) - Fintype.card (ECyc α M) +
        Fintype.card (FCyc α M) ≤ 2 := by
  by_cases hne : Nonempty α
  · letI : Nonempty α := hne
    exact algebraic_euler_bound α M hconn
  · haveI : IsEmpty α := ⟨fun x => hne ⟨x⟩⟩
    have hV : IsEmpty (VCyc α M) := by
      refine ⟨fun z => Quotient.inductionOn z fun x => ?_⟩
      exact isEmptyElim x
    have hE : IsEmpty (ECyc α M) := by
      refine ⟨fun z => Quotient.inductionOn z fun x => ?_⟩
      exact isEmptyElim x
    have hF : IsEmpty (FCyc α M) := by
      refine ⟨fun z => Quotient.inductionOn z fun x => ?_⟩
      exact isEmptyElim x
    have cV : Fintype.card (VCyc α M) = 0 := Fintype.card_eq_zero_iff.mpr hV
    have cE : Fintype.card (ECyc α M) = 0 := Fintype.card_eq_zero_iff.mpr hE
    have cF : Fintype.card (FCyc α M) = 0 := Fintype.card_eq_zero_iff.mpr hF
    rw [cV, cE, cF]
    norm_num

end Map

end SimpleGraph.ChainEuler
