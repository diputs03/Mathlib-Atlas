/-
# Script 59 (stage 1): orbit-count restriction machinery for connected maps

Goal of the full script (later stages): for a connected combinatorial map
(edge involution τ fixed-point-free, vertex rotation σ; face permutation
φ = τ * σ⁻¹), prove

    χ = V − E + F ≤ 2,   equivalently genus g = (2 − χ)/2 ≥ 0.

The combinatorial heart is the transposition orbit-count theorem that Mathlib
does not provide in full generality (it only has the *adjacent* split
`IsCycle.swap_mul` and fixed-point joins). We prove, for any permutation `f`
on a finite type and distinct points `x y`, with `g = swap x y * f`:

  • if `x y` lie in the SAME `f`-cycle, `orbits g = orbits f + 1` (a chord cut
    splits one cycle into two);
  • if they lie in DISTINCT `f`-cycles (fixed points allowed),
    `orbits g = orbits f − 1` (two cycles merge).

Stage 1 (this file) builds the orbit-count definition together with the
restriction / additivity machinery: if a finset `s` is invariant under a
permutation, then the total number of orbits is the number of orbits inside
`s` plus the number outside it, and a permutation that only changes inside `s`
changes the total orbit count by exactly the change inside `s`.

Everything is proved from the kernel up: no `sorry`, no axioms beyond Mathlib.
-/

import Mathlib

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Equiv Equiv.Perm

namespace SimpleGraph.SwapOrbit

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Number of orbits (cycles, counting fixed points as singleton orbits) of a
permutation on a finite type. Mathlib has `cycleType` for the non-trivial
cycles but no direct "number of cycles including fixed points", so we count:
each non-trivial cycle contributes one orbit, and every point not in the
support (a fixed point) contributes one more. -/
def orbits (p : Perm α) : Nat :=
  Multiset.card p.cycleType + (Fintype.card α - p.cycleType.sum)

section Restrict

variable (s : Finset α)

/-- The permutation induced by `f` on the subtype `{x // x ∈ s}`, when `s` is
invariant under `f`. -/
def partPerm (f : Perm α) (h : ∀ z, f z ∈ s ↔ z ∈ s) : Perm { z // z ∈ s } :=
  f.subtypePerm fun z => h z

/-- The induced permutation on `s`, extended to all of `α` by fixing every
point outside `s`. -/
def part (f : Perm α) (h : ∀ z, f z ∈ s ↔ z ∈ s) : Perm α :=
  Perm.ofSubtype (partPerm s f h)

lemma part_mem (f : Perm α) (h : ∀ z, f z ∈ s ↔ z ∈ s) {z : α} (hz : z ∈ s) :
    part s f h z = f z :=
  Perm.ofSubtype_subtypePerm_of_mem h hz

lemma part_not_mem (f : Perm α) (h : ∀ z, f z ∈ s ↔ z ∈ s) {z : α} (hz : z ∉ s) :
    part s f h z = z :=
  Perm.ofSubtype_subtypePerm_of_not_mem h hz

lemma support_part_subset (f : Perm α) (h : ∀ z, f z ∈ s ↔ z ∈ s) :
    (part s f h).support ⊆ s := by
  intro z hz
  by_contra hz'
  exact Equiv.Perm.mem_support.mp hz (part_not_mem s f h hz')

/-- Invariance of `s` implies invariance of its complement. -/
lemma partPerm_compl (f : Perm α) (h : ∀ z, f z ∈ s ↔ z ∈ s) :
    ∀ z, f z ∈ sᶜ ↔ z ∈ sᶜ := by
  intro z
  simp only [Finset.mem_compl]
  exact (h z).not

/-- Number of orbits of `f` *inside* the invariant finset `s`. -/
def orbitsOn (f : Perm α) (h : ∀ z, f z ∈ s ↔ z ∈ s) : Nat :=
  let p : Perm { z // z ∈ s } := partPerm s f h
  Multiset.card p.cycleType + (s.card - p.cycleType.sum)

lemma factor_part (f : Perm α) (h : ∀ z, f z ∈ s ↔ z ∈ s) :
    part s f h * part sᶜ f (partPerm_compl s f h) = f := by
  ext z
  by_cases hz : z ∈ s
  · have hc : z ∉ sᶜ := by simpa using hz
    have e1 : part sᶜ f (partPerm_compl s f h) z = z :=
      part_not_mem sᶜ f (partPerm_compl s f h) hc
    have e2 : part s f h z = f z := part_mem s f h hz
    rw [Perm.mul_apply, e1, e2]
  · have hc : z ∈ sᶜ := by simpa using hz
    have e2 : part sᶜ f (partPerm_compl s f h) z = f z :=
      part_mem sᶜ f (partPerm_compl s f h) hc
    have hfz : f z ∉ s := (h z).not.mpr hz
    rw [Perm.mul_apply, e2]
    exact part_not_mem s f h hfz

lemma disjoint_part (f : Perm α) (h : ∀ z, f z ∈ s ↔ z ∈ s) :
    Disjoint (part s f h) (part sᶜ f (partPerm_compl s f h)) := by
  rw [disjoint_iff_disjoint_support]
  have hdc : Disjoint s sᶜ :=
    Finset.disjoint_left.mpr fun x hx1 hx2 => by
      simp only [Finset.mem_compl] at hx2
      exact hx2 hx1
  exact Finset.disjoint_of_subset_left (support_part_subset s f h)
    (Finset.disjoint_of_subset_right
      (support_part_subset sᶜ f (partPerm_compl s f h)) hdc)

lemma cycleType_part (f : Perm α) (h : ∀ z, f z ∈ s ↔ z ∈ s) :
    (part s f h).cycleType = (partPerm s f h).cycleType :=
  cycleType_ofSubtype

/-- Orbit-count additivity over an invariant finset and its complement. -/
lemma orbits_add (f : Perm α) (h : ∀ z, f z ∈ s ↔ z ∈ s) :
    orbits f = orbitsOn s f h + orbitsOn sᶜ f (partPerm_compl s f h) := by
  set ps : Perm { z // z ∈ s } := partPerm s f h with hps
  set pt : Perm { z // z ∈ sᶜ } := partPerm sᶜ f (partPerm_compl s f h) with hpt
  have hfac := factor_part s f h
  have hdis := disjoint_part s f h
  have hct : f.cycleType = ps.cycleType + pt.cycleType := by
    rw [← hfac, hdis.cycleType_mul, cycleType_part, cycleType_part, hps, hpt]
  have hsub : Fintype.card { z // z ∈ s } = s.card := by
    rw [Fintype.card_subtype]
    ; simp
  have eqc : Finset.univ.filter (fun z => z ∈ sᶜ) = sᶜ := by ext x; simp
  have hsubt : Fintype.card { z // z ∈ sᶜ } = sᶜ.card := by
    rw [Fintype.card_subtype, eqc]
  have hs : ps.cycleType.sum ≤ s.card := by
    rw [sum_cycleType ps]
    have := Finset.card_le_univ ps.support
    rw [hsub] at this
    exact this
  have ht : pt.cycleType.sum ≤ sᶜ.card := by
    rw [sum_cycleType pt]
    have := Finset.card_le_univ pt.support
    rw [hsubt] at this
    exact this
  have hcard : Fintype.card α = s.card + sᶜ.card := by
    have hc := Finset.card_compl s
    have hb : s.card ≤ Fintype.card α := s.card_le_univ
    omega
  set bS := ps.cycleType.sum with hbS
  set bT := pt.cycleType.sum with hbT
  have hsubb : Fintype.card α - (bS + bT) = (s.card - bS) + (sᶜ.card - bT) := by omega
  rw [orbits, hct]
  simp only [orbitsOn, hps, hpt, Multiset.card_add, Multiset.sum_add]
  rw [hsubb]
  ; ring

/-- If two permutations agree outside an invariant finset, the change in the
total orbit count equals the change inside the finset (stated without
subtraction so it holds unconditionally). -/
lemma orbits_change (f g : Perm α)
    (hf : ∀ z, f z ∈ s ↔ z ∈ s) (hg : ∀ z, g z ∈ s ↔ z ∈ s)
    (hout : ∀ z, z ∉ s → g z = f z) :
    orbits g + orbitsOn s f hf = orbits f + orbitsOn s g hg := by
  have hft : ∀ z, f z ∈ sᶜ ↔ z ∈ sᶜ := partPerm_compl s f hf
  have hgt : ∀ z, g z ∈ sᶜ ↔ z ∈ sᶜ := partPerm_compl s g hg
  have hpt : partPerm sᶜ g hgt = partPerm sᶜ f hft := by
    ext ⟨z, hz⟩
    show g z = f z
    exact hout z (by simpa using hz)
  have hocc : orbitsOn sᶜ g hgt = orbitsOn sᶜ f hft := by
    unfold orbitsOn
    rw [hpt]
  have of := orbits_add s f hf
  have og := orbits_add s g hg
  rw [og, of, hocc]
  ; ring

/-- Left-multiplying by a transposition supported inside an invariant finset
preserves invariance of the finset. -/
lemma swap_invar (x y : α) (hx : x ∈ s) (hy : y ∈ s) (f : Perm α)
    (h : ∀ z, f z ∈ s ↔ z ∈ s) :
    ∀ z, (swap x y * f) z ∈ s ↔ z ∈ s := by
  have h1 : ∀ w, w ∈ s → swap x y w ∈ s := by
    intro w hw
    rcases eq_or_ne w x with (hwx | hwx)
    · rw [hwx]; simpa using hy
    rcases eq_or_ne w y with (hwy | hwy)
    · rw [hwy]; simpa using hx
    · have heq : swap x y w = w := swap_apply_of_ne_of_ne hwx hwy
      rw [heq]
      exact hw
  have h2 : ∀ w, w ∉ s → swap x y w = w := by
    intro w hw
    have hwx : w ≠ x := by intro he; exact hw (he ▸ hx)
    have hwy : w ≠ y := by intro he; exact hw (he ▸ hy)
    exact swap_apply_of_ne_of_ne hwx hwy
  intro z
  have hfi : ∀ z, z ∈ s → f z ∈ s := fun z hz => (h z).mpr hz
  have hfo : ∀ z, z ∉ s → f z ∉ s := fun z hz => (h z).not.mpr hz
  constructor
  · intro hz
    by_cases hc : f z ∈ s
    · exact (h z).mp hc
    · have heq : swap x y (f z) = f z := h2 (f z) hc
      exact False.elim (hc (heq ▸ hz))
  · intro hz
    exact h1 (f z) (hfi z hz)

/-- A transposition supported on `{x,y} ⊆ s` acts as the identity outside `s`,
so `swap x y * f` agrees with `f` outside `s`. -/
lemma swap_outside (x y : α) (hx : x ∈ s) (hy : y ∈ s) (f : Perm α)
    (h : ∀ z, f z ∈ s ↔ z ∈ s) :
    ∀ z, z ∉ s → (swap x y * f) z = f z := by
  intro z hz
  have hfz : f z ∉ s := (h z).not.mpr hz
  have hnx : f z ≠ x := by intro e; rw [e] at hfz; exact hfz hx
  have hny : f z ≠ y := by intro e; rw [e] at hfz; exact hfz hy
  have : (swap x y * f) z = swap x y (f z) := by rfl
  rw [this, swap_apply_of_ne_of_ne hnx hny]

/-- The orbit count on an invariant finset is unchanged when the finset is
replaced by an equal one (regardless of how the invariance proof is given). -/
lemma orbitsOn_congr {s t : Finset α} (hst : s = t) (f : Perm α)
    (hs : ∀ z, f z ∈ s ↔ z ∈ s) (ht : ∀ z, f z ∈ t ↔ z ∈ t) :
    orbitsOn s f hs = orbitsOn t f ht := by
  subst hst
  unfold orbitsOn
  congr 1

end Restrict

/-- A permutation on a nonempty finite type whose single `IsCycleOn` region is
the whole type (it is transitive) has exactly one orbit. -/
lemma orbits_one_of_isCycleOn_univ {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    (p : Perm β) (h : p.IsCycleOn Set.univ) : orbits p = 1 := by
  by_cases hn : Nontrivial β
  · have hnu : Set.Nontrivial (Set.univ : Set β) := by
      obtain ⟨a, b, hab⟩ := @exists_pair_ne β hn
      exact ⟨a, Set.mem_univ a, b, Set.mem_univ b, hab⟩
    have hc : p.IsCycle := by
      rw [isCycle_iff_exists_isCycleOn]
      exact ⟨Set.univ, hnu, h, fun _ _ => trivial⟩
    have hsup : p.support = Finset.univ := by
      ext z
      simp only [Finset.mem_univ, iff_true, Equiv.Perm.mem_support]
      exact h.apply_ne hnu (Set.mem_univ z)
    rw [orbits, hc.cycleType, hsup]
    ; simp
  · have hsub : Subsingleton β := not_nontrivial_iff_subsingleton.mp hn
    have h1 : p = 1 := Subsingleton.elim p 1
    have hc1 : Fintype.card β = 1 := by
      rw [Fintype.card_eq_one_iff]
      exact ⟨Classical.arbitrary β, fun y => Subsingleton.elim _ _⟩
    rw [orbits, h1, hc1]
    ; simp [cycleType_one]

/-- Inside a nonempty invariant finset, if the induced permutation is
transitive (one `IsCycleOn` region on the whole subtype), there is one orbit. -/
lemma orbitsOn_eq_one (s : Finset α) (f : Perm α) (h : ∀ z, f z ∈ s ↔ z ∈ s)
    (hs : s.Nonempty) (h1 : (partPerm s f h).IsCycleOn Set.univ) : orbitsOn s f h = 1 := by
  haveI : Nonempty { z // z ∈ s } := Finset.Nonempty.to_subtype hs
  have he := orbits_one_of_isCycleOn_univ (partPerm s f h) h1
  have hcard : s.card = Fintype.card { z // z ∈ s } := by
    rw [Fintype.card_subtype]
    ; simp
  unfold orbitsOn
  rw [hcard]
  exact he

/-- If a permutation `p` on a finite type agrees with `formPerm l` on every
element of a nodup list `l` that covers the whole type, then `p` has exactly
one orbit. -/
lemma orbits_eq_one_of_cycleList {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    (l : List β) (hn : l.Nodup) (hcov : ∀ z : β, z ∈ l) (p : Perm β)
    (hsuc : ∀ (i : ℕ) (hi : i < l.length), p l[i] = l.formPerm l[i]) :
    orbits p = 1 := by
  have heq : p = l.formPerm := by
    ext z
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hcov z)
    exact hsuc i hi
  rw [heq]
  have hc : l.formPerm.IsCycleOn { a | a ∈ l } := hn.isCycleOn_formPerm
  have hu : ({ a | a ∈ l } : Set β) = Set.univ := by
    ext a; simp [hcov a]
  rw [hu] at hc
  exact orbits_one_of_isCycleOn_univ l.formPerm hc

/-- If a permutation `p` is the product of the `formPerm`s of two disjoint
nodup lists that together cover the whole type, then `p` has exactly two
orbits (a list of length one contributes one fixed-point orbit). -/
lemma orbits_eq_two_of_cycleLists {β : Type*} [Fintype β] [DecidableEq β]
    (l1 l2 : List β) (h1n : l1.Nodup) (h2n : l2.Nodup)
    (hd : Disjoint l1.toFinset l2.toFinset)
    (hcov : ∀ z : β, z ∈ l1 ∨ z ∈ l2)
    (htne : l1.toFinset.Nonempty) (hcne : l2.toFinset.Nonempty)
    (p : Perm β) (heq : p = l1.formPerm * l2.formPerm) :
    orbits p = 2 := by
  set t : Finset β := l1.toFinset with ht
  have hcom : tᶜ = l2.toFinset := by
    ext z
    simp only [ht, Finset.mem_compl, List.mem_toFinset]
    constructor
    · intro h
      rcases hcov z with (h1 | h2)
      · exact False.elim (h h1)
      · exact h2
    · intro h2 h1
      exact Finset.disjoint_left.mp hd
        (by simpa [ht, List.mem_toFinset] using h1) (by simpa using h2)
  have hfix2 : ∀ z ∈ t, l2.formPerm z = z := by
    intro z hz
    have h : z ∉ l2 := fun h2 =>
      Finset.disjoint_left.mp hd hz (by simpa using h2)
    exact List.formPerm_apply_of_notMem h
  have hfix1 : ∀ z ∈ tᶜ, l1.formPerm z = z := by
    intro z hz
    have h : z ∉ l1 := fun h1 =>
      Finset.disjoint_left.mp hd.symm (by simpa [hcom] using hz)
        (by simpa [ht, List.mem_toFinset] using h1)
    exact List.formPerm_apply_of_notMem h
  have hinv : ∀ z, p z ∈ t ↔ z ∈ t := by
    rw [heq]
    intro z
    constructor
    · intro hz
      by_cases h : z ∈ t
      · exact h
      · have hc : z ∈ tᶜ := by simpa using h
        have e1 : l1.formPerm z = z := hfix1 z hc
        have m2 : z ∈ l2 := by simpa [hcom, List.mem_toFinset] using hc
        set w := l2.formPerm z with hw
        have ew2 : w ∈ l2 := List.formPerm_mem_iff_mem.mpr m2
        have nw : w ∉ l1 := fun h =>
          Finset.disjoint_left.mp hd
            (by simpa [ht, List.mem_toFinset] using h) (by simpa using ew2)
        have ep : (l1.formPerm * l2.formPerm) z = w := by
          rw [Perm.mul_apply, hw, List.formPerm_apply_of_notMem nw]
        have hp : (l1.formPerm * l2.formPerm) z ∈ tᶜ := by
          rw [ep]
          simpa [hcom, List.mem_toFinset] using ew2
        have hdt : Disjoint t tᶜ :=
          Finset.disjoint_left.mpr fun x hx1 hx2 => by
            simp only [Finset.mem_compl] at hx2
            exact hx2 hx1
        exact False.elim (Finset.disjoint_left.mp hdt hz hp)
    · intro hz
      have e2 : l2.formPerm z = z := hfix2 z hz
      rw [Perm.mul_apply, e2]
      have e : l1.formPerm z ∈ l1 := List.formPerm_mem_iff_mem.mpr
        (by simpa [ht, List.mem_toFinset] using hz)
      simpa [ht, List.mem_toFinset] using e
  have hsub1 : (partPerm t p hinv).IsCycleOn Set.univ := by
    have hag : ∀ z ∈ t, p z = l1.formPerm z := by
      intro z hz
      rw [heq, Perm.mul_apply, hfix2 z hz]
    have hsp : partPerm t p hinv = partPerm t l1.formPerm fun z => by
      simp only [ht, List.mem_toFinset, List.formPerm_mem_iff_mem] := by
      ext ⟨z, hz⟩
      show p z = l1.formPerm z
      exact hag z hz
    rw [hsp]
    have hc := h1n.isCycleOn_formPerm
    have hs : ({ a | a ∈ l1 } : Set β) = (t : Set β) := by
      ext a; simp [ht]
    rw [hs] at hc
    exact hc.subtypePerm
  have hinv2 : ∀ z, p z ∈ tᶜ ↔ z ∈ tᶜ := partPerm_compl t p hinv
  set u : Finset β := l2.toFinset with hu
  have huc : u = tᶜ := hcom.symm
  have hiu : ∀ z, p z ∈ u ↔ z ∈ u := by
    rw [huc]
    exact hinv2
  have hagu : ∀ z ∈ u, p z = l2.formPerm z := by
    intro z hz
    have hzc : z ∈ tᶜ := by rwa [hcom]
    have mz : z ∈ l2 := by
      have : z ∈ u := hz
      simpa [hu, List.mem_toFinset] using this
    set w := l2.formPerm z with hw
    have ew2 : w ∈ l2 := List.formPerm_mem_iff_mem.mpr mz
    have ew2u : w ∈ u := by simpa [hu, List.mem_toFinset] using ew2
    have nw : w ∉ l1 := fun h =>
      Finset.disjoint_left.mp hd
        (by simpa [ht, List.mem_toFinset] using h) ew2u
    rw [heq, Perm.mul_apply, List.formPerm_apply_of_notMem nw]
  have hiffu : ∀ z, l2.formPerm z ∈ u ↔ z ∈ u := fun z => by
    simp only [hu, List.mem_toFinset, List.formPerm_mem_iff_mem]
  have hspu : partPerm u p hiu = partPerm u l2.formPerm hiffu := by
    ext ⟨z, hz⟩
    show p z = l2.formPerm z
    exact hagu z hz
  have h2cyc : (partPerm u p hiu).IsCycleOn Set.univ := by
    rw [hspu]
    have hc := h2n.isCycleOn_formPerm
    have hs : ({ a | a ∈ l2 } : Set β) = (u : Set β) := by
      ext a; simp [hu]
    rw [hs] at hc
    exact hc.subtypePerm
  have ho2 : orbitsOn u p hiu = 1 := orbitsOn_eq_one u p hiu hcne h2cyc
  have htr : orbitsOn tᶜ p hinv2 = orbitsOn u p hiu :=
    orbitsOn_congr hcom p hinv2 hiu
  have hsub2count : orbitsOn tᶜ p hinv2 = 1 := by
    rw [htr, ho2]
  have ha := orbits_add t p hinv
  rw [ha, orbitsOn_eq_one t p hinv htne hsub1, hsub2count]

/-- The carrier of the cycle of `f` through `z`, with a fixed point represented
as the singleton `{z}` so that every orbit (including a singleton orbit) has a
nonempty carrier. -/
def cyc (f : Perm α) (z : α) : Finset α :=
  if _h : f z = z then {z} else (f.cycleOf z).support

lemma cyc_mem_self (f : Perm α) (z : α) : z ∈ cyc f z := by
  by_cases h : f z = z
  · rw [cyc, dite_eq_left h]
    simp
  · rw [cyc, dite_eq_right h]
    exact (mem_support_cycleOf_iff' h).mpr SameCycle.rfl

lemma cyc_isCycleOn (f : Perm α) (z : α) : f.IsCycleOn (cyc f z) := by
  by_cases h : f z = z
  · rw [cyc, dite_eq_left h, Finset.coe_singleton]
    exact isCycleOn_singleton.mpr h
  · rw [cyc, dite_eq_right h]
    exact isCycleOn_support_cycleOf f z

lemma mem_cyc_iff (f : Perm α) {z u : α} : u ∈ cyc f z ↔ f.SameCycle z u := by
  by_cases h : f z = z
  · rw [cyc, dite_eq_left h, Finset.mem_singleton]
    constructor
    · rintro rfl
      exact SameCycle.rfl
    · intro hs
      obtain ⟨i, _, hi⟩ := hs.exists_pow_eq'
      have hfix : ∀ i : ℕ, (f ^ i) z = z := by
        intro i
        induction i with
        | zero => rfl
        | succ i ih => rw [pow_succ', Perm.mul_apply, ih, h]
      exact hi ▸ hfix i
  · rw [cyc, dite_eq_right h]
    exact mem_support_cycleOf_iff' h

lemma cyc_disjoint {f : Perm α} {x y : α} (h : ¬ f.SameCycle x y) :
    Disjoint (cyc f x) (cyc f y) := by
  rw [Finset.disjoint_left]
  intro z hz1 hz2
  have h1 : f.SameCycle x z := (mem_cyc_iff f).mp hz1
  have h2 : f.SameCycle y z := (mem_cyc_iff f).mp hz2
  exact h (h1.trans h2.symm)

/-- For a permutation that is a single cycle on a nonempty finite type, the
list of iterates `a, p a, …, p^(n-1) a` contains every point exactly once and
its `formPerm` equals `p`. -/
lemma cycle_power_list {β : Type*} [Fintype β] [DecidableEq β] (p : Perm β)
    (hp : p.IsCycleOn (Finset.univ : Finset β)) (a : β) :
    let n := Fintype.card β
    let L : List β := (List.range n).map fun i => (p ^ i) a
    L.Nodup ∧ (∀ z, z ∈ L) ∧ L.formPerm = p := by
  set n := Fintype.card β with hn
  set L : List β := (List.range n).map fun i => (p ^ i) a with hL
  have hpos : 0 < n := Finset.card_pos.mpr ⟨a, Finset.mem_univ a⟩
  have hlen : L.length = n := by
    rw [hL, List.length_map, List.length_range]
  have hget : ∀ i (hi : i < n), L[i] = (p ^ i) a := by
    intro i hi
    have hi' : i < L.length := by rw [hlen]; exact hi
    simp only [hL, List.getElem_map, List.getElem_range]
  have hnod : L.Nodup := by
    rw [hL, List.nodup_map_iff_inj_on List.nodup_range]
    intro i hi1 j hj1 he
    have hme : i ≡ j [MOD n] :=
      (hp.pow_apply_eq_pow_apply (Finset.mem_univ a)).mp he
    have hc : i % n = j % n := hme
    have hi : i < n := List.mem_range.mp hi1
    have hj : j < n := List.mem_range.mp hj1
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hc
    exact hc
  have hcov : ∀ z, z ∈ L := by
    intro z
    obtain ⟨i, hi, he⟩ := hp.exists_pow_eq (Finset.mem_univ a) (Finset.mem_univ z)
    rw [hL, List.mem_map]
    exact ⟨i, List.mem_range.mpr hi, he⟩
  have hfeq : L.formPerm = p := by
    ext z
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hcov z)
    have hin : i < n := by rwa [hlen] at hi
    rw [List.formPerm_apply_getElem L hnod i hi, hget i hin]
    have hlb : 0 < L.length := hlen ▸ hpos
    have hel : ∀ (j : ℕ) (hj : j % L.length < L.length),
        L[j % L.length]'hj = (p ^ (j % L.length)) a :=
      fun j hj => hget _ (hj.trans_eq hlen)
    by_cases h : i + 1 < n
    · -- ordinary successor: L[(i+1) mod n] = p^(i+1) a = p (p^i a)
      have hm : (i + 1) % L.length = i + 1 := by
        rw [hlen]; exact Nat.mod_eq_of_lt h
      exact (hel (i + 1) (Nat.mod_lt (i + 1) hlb)).trans
        (by rw [hm, pow_succ', Perm.mul_apply])
    · -- wrap-around: (i+1) mod n = 0 and p^n a = a
      have hi' : i + 1 = n := by omega
      have h0 : (i + 1) % L.length = 0 := by rw [hlen, hi']; simp
      have hwrap : p ((p ^ i) a) = a := by
        have hpi : p * p ^ i = p ^ n := by rw [← pow_succ', hi']
        have hz : (p * p ^ i) a = a := by
          rw [hpi]
          simpa [hn] using hp.pow_card_apply (Finset.mem_univ a)
        rwa [Perm.mul_apply] at hz
      exact (hel (i + 1) (Nat.mod_lt (i + 1) hlb)).trans
        (by rw [h0, pow_zero]; exact hwrap.symm)
  exact ⟨hnod, hcov, hfeq⟩

section SplitJoin

variable (f : Perm α)

/-- Coercing the iterates of the subtype permutation gives the iterates of `f`. -/
lemma coe_pow_cycle (s : Finset α) (hsinv : ∀ z, f z ∈ s ↔ z ∈ s) (z : α) (hz : z ∈ s)
    (i : ℕ) :
    (((partPerm s f hsinv) ^ i) ⟨z, hz⟩).val = (f ^ i) z := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hstep : ∀ (u : { z // z ∈ s }), ((partPerm s f hsinv) u).val = f u.val := fun _ => rfl
    rw [pow_succ', Perm.mul_apply, hstep _, ih, pow_succ', Perm.mul_apply]

/-- Multiplying by a transposition whose two points lie in the SAME cycle of `f`
splits that cycle into two: the number of orbits increases by exactly one. -/
lemma orbits_swap_same_cycle {x y : α} (hne : x ≠ y) (h : f.SameCycle x y) :
    orbits (swap x y * f) = orbits f + 1 := by
  have hfx : f x ≠ x := by
    by_contra e
    obtain ⟨i, _, hi⟩ := h.exists_pow_eq'
    have hfix : ∀ i : ℕ, (f ^ i) x = x := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih2 => rw [pow_succ', Perm.mul_apply, ih2, e]
    exact hne ((hi ▸ hfix i).symm)
  set s : Finset α := cyc f x with hs
  have hcs : f.IsCycleOn s := cyc_isCycleOn f x
  have hxs : x ∈ s := cyc_mem_self f x
  have hys : y ∈ s := (mem_cyc_iff f).mpr h
  have hsinv : ∀ z, f z ∈ s ↔ z ∈ s := fun z => hcs.apply_mem_iff
  let β := { z // z ∈ s }
  let p : Perm β := partPerm s f hsinv
  have hp : p.IsCycleOn Set.univ := hcs.subtypePerm
  have hpun : p.IsCycleOn (Finset.univ : Finset β) := by simpa using hp
  let xβ : β := ⟨x, hxs⟩
  let yβ : β := ⟨y, hys⟩
  have hcardn : s.card = Fintype.card β := by
    rw [Fintype.card_subtype]
    simp
  set n := Fintype.card β with hn
  set L : List β := (List.range n).map fun i => (p ^ i) xβ with hL
  have hres := cycle_power_list p hpun xβ
  dsimp only at hres
  have hLnod : L.Nodup := by simpa [hL, hn] using hres.1
  have hLcov : ∀ z, z ∈ L := by simpa [hL, hn] using hres.2.1
  have hLform : L.formPerm = p := by simpa [hL, hn] using hres.2.2
  have hLfin : L.toFinset = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro z
    exact List.mem_toFinset.mpr (hLcov z)
  have hLn : L.length = n := by
    have hc : L.toFinset.card = L.length := List.toFinset_card_of_nodup hLnod
    rw [hLfin, Finset.card_univ] at hc
    exact hc.symm
  obtain ⟨k, hkn, hkxy⟩ :=
    hpun.exists_pow_eq (Finset.mem_univ xβ) (Finset.mem_univ yβ)
  have hk0 : k ≠ 0 := by
    intro e
    rw [e] at hkxy
    simp only [pow_zero] at hkxy
    exact hne (Subtype.ext_iff.mp hkxy)
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  set L1 := L.take k with hL1
  set L2 := L.drop k with hL2
  have h1n : L1.Nodup := by rw [hL1]; exact hLnod.take
  have h2n : L2.Nodup := by rw [hL2]; exact hLnod.drop
  have hlen1 : L1.length = k := by
    rw [hL1, List.length_take, hLn]
    exact Nat.min_eq_left (by simpa [hn] using hkn.le)
  have hlen2 : L2.length = n - k := by
    rw [hL2, List.length_drop, hLn]
  have h1pos : 0 < L1.length := by rw [hlen1]; exact hkpos
  have h2pos : 0 < L2.length := by
    rw [hlen2]
    simpa [hn] using Nat.sub_pos_of_lt hkn
  have hdisl : List.Disjoint L1 L2 := List.disjoint_take_drop hLnod (by rfl)
  have hdis : Disjoint L1.toFinset L2.toFinset := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    exact hdisl (List.mem_toFinset.mp hz1) (List.mem_toFinset.mp hz2)
  have hcov2 : ∀ (z : β), z ∈ L1 ∨ z ∈ L2 := by
    intro z
    have hz : z ∈ L := hLcov z
    have happ : L1 ++ L2 = L := List.take_append_drop k L
    rw [← happ, List.mem_append] at hz
    exact hz
  have htne : L1.toFinset.Nonempty := by
    have hc : L1.toFinset.card = L1.length := List.toFinset_card_of_nodup h1n
    rw [← Finset.card_pos, hc, hlen1]
    exact hkpos
  have hcne : L2.toFinset.Nonempty := by
    have hc : L2.toFinset.card = L2.length := List.toFinset_card_of_nodup h2n
    rw [← Finset.card_pos, hc, hlen2]
    exact hlen2 ▸ h2pos
  let g : Perm α := swap x y * f
  have hginv : ∀ z, g z ∈ s ↔ z ∈ s := swap_invar s x y hxs hys f hsinv
  let q : Perm β := partPerm s g hginv
  have hout : ∀ z, z ∉ s → g z = f z := swap_outside s x y hxs hys f hsinv
  have coe_pow : ∀ (i : ℕ), ((p ^ i) xβ).val = (f ^ i) x :=
    fun i => coe_pow_cycle f s hsinv x hxs i
  have hfxy : (f ^ k) x = y := by
    have := congr_arg (fun w : β => w.val) hkxy
    rwa [coe_pow k] at this
  have hfnx : (f ^ n) x = x := by
    have hcn : n = s.card := by rw [hn, hcardn]
    rw [hcn]
    exact hcs.pow_card_apply hxs
  have ne_x : ∀ i, 0 < i → i < n → (f ^ i) x ≠ x := by
    intro i hi hlt heq
    have hcn : n = s.card := by rw [hn, hcardn]
    have hd : s.card ∣ i := (hcs.pow_apply_eq hxs).mp heq
    have hlt' : i < s.card := by rw [← hcn]; exact hlt
    exact Nat.not_dvd_of_pos_of_lt hi hlt' hd
  have ne_y : ∀ i, i < n → i ≠ k → (f ^ i) x ≠ y := by
    intro i hin hie heq
    have heq2 : (f ^ i) x = (f ^ k) x := heq.trans hfxy.symm
    have hme : i ≡ k [MOD s.card] := (hcs.pow_apply_eq_pow_apply hxs).mp heq2
    have hkn' : k < n := by simpa [hn] using hkn
    rw [hcardn] at hme
    have hmeq : i % n = k % n := hme
    rw [Nat.mod_eq_of_lt hin, Nat.mod_eq_of_lt hkn'] at hmeq
    exact hie hmeq
  have qcoe : ∀ (w : β), (q w).val = g w.val := fun _ => rfl
  have hqeq : q = L1.formPerm * L2.formPerm := by
    ext z
    obtain ⟨i, hi, hzi⟩ := List.getElem_of_mem (hLcov z)
    rw [← hzi, qcoe]
    have hLi : ∀ (t : ℕ) (ht : t < L.length), L[t] = (p ^ t) xβ := fun t _ => by
      simp only [hL, List.getElem_map, List.getElem_range]
    have hkn' : k < n := by simpa [hn] using hkn
    by_cases hik : i < k
    · -- z is in the first piece L1
      have hL1i : L1[i] = L[i] := by simp only [hL1, List.getElem_take]
      have hpi : L[i] = (p ^ i) xβ := hLi i (by rw [hLn]; omega)
      have hz1 : (p ^ i) xβ ∈ L1 := by
        rw [← hL1i.trans hpi]
        exact List.getElem_mem _
      have hznot2 : (p ^ i) xβ ∉ L2 := fun h => hdisl hz1 h
      have hwi : (p ^ i) xβ = L1[i] := (hL1i.trans hpi).symm
      simp only [hpi, Perm.mul_apply]
      rw [List.formPerm_apply_of_notMem hznot2, hwi,
        List.formPerm_apply_getElem L1 h1n i (by rw [hlen1]; exact hik)]
      by_cases h : i + 1 < k
      · -- ordinary successor inside L1
        have hml : (i + 1) % L1.length = i + 1 := by
          rw [hlen1]; exact Nat.mod_eq_of_lt h
        simp only [hml]
        have h1nxt : L1[i + 1] = L[i + 1] := by
          simp only [hL1, List.getElem_take]
        show (swap x y) (f ↑L1[i]) = ↑L1[i + 1]
        rw [h1nxt, hLi (i + 1) (by rw [hLn]; omega), coe_pow (i + 1)]
        have hcur : (↑L1[i] : α) = (f ^ i) x := by
          rw [← hwi]; exact coe_pow i
        have hnext : f (↑L1[i]) = (f ^ (i + 1)) x := by
          rw [hcur, pow_succ', Perm.mul_apply]
        have hx' : (f ^ (i + 1)) x ≠ x := ne_x (i + 1) (by omega) (by omega)
        have hy' : (f ^ (i + 1)) x ≠ y := ne_y (i + 1) (by omega) (by omega)
        rw [hnext, swap_apply_of_ne_of_ne hx' hy']
      · -- boundary of L1 wraps to its head: f^k x = y maps to x
        have hib : i + 1 = k := by omega
        have h0l : (i + 1) % L1.length = 0 := by rw [hlen1, hib]; simp
        simp only [h0l]
        have e0 : L1[0] = xβ := by
          simp only [hL1, List.getElem_take, hL, List.getElem_map,
            List.getElem_range, pow_zero, Perm.one_apply]
        rw [e0]
        have hcur : (↑L1[i] : α) = (f ^ i) x := by
          rw [← hwi]; exact coe_pow i
        show (swap x y) (f ↑L1[i]) = x
        rw [hcur]
        have hlast : f ((f ^ i) x) = y := by
          have heq : f ((f ^ i) x) = (f ^ (i + 1)) x := by
            rw [pow_succ', Perm.mul_apply]
          rw [heq, show i + 1 = k from hib, hfxy]
        rw [hlast]
        simp
    · -- z is in the second piece L2
      have hki : k ≤ i := by omega
      set j := i - k with hj
      have hij : i = k + j := by omega
      have hjn : j < L2.length := by rw [hlen2]; omega
      have hL2j : L2[j] = L[k + j] := by simp only [hL2, List.getElem_drop]
      have hpi' : L[i] = (p ^ i) xβ := hLi i hi
      have ez : L2[j] = (p ^ i) xβ :=
        hL2j.trans ((hLi (k + j) (by rw [hLn]; omega)).trans (by rw [←hij]))
      have hz2 : (p ^ i) xβ ∈ L2 := by rw [← ez]; exact List.getElem_mem _
      have hres_in2 : L2.formPerm ((p ^ i) xβ) ∈ L2 :=
        List.formPerm_mem_iff_mem.mpr hz2
      have hres_not1 : L2.formPerm ((p ^ i) xβ) ∉ L1 := fun h =>
        hdisl h hres_in2
      simp only [hpi', Perm.mul_apply]
      rw [List.formPerm_apply_of_notMem hres_not1, ←ez,
        List.formPerm_apply_getElem L2 h2n j hjn]
      by_cases h : j + 1 < n - k
      · -- ordinary successor inside L2
        have hml : (j + 1) % L2.length = j + 1 := by
          rw [hlen2]; exact Nat.mod_eq_of_lt h
        simp only [hml]
        have h2nxt : L2[j + 1] = (p ^ (i + 1)) xβ :=
          (by simp only [hL2, List.getElem_drop] : L2[j + 1] = L[k + (j + 1)]).trans
            ((hLi (k + (j + 1)) (by rw [hLn]; omega)).trans
              (by rw [show k + (j + 1) = i + 1 by omega]))
        show (swap x y) (f ↑L2[j]) = ↑L2[j + 1]
        rw [h2nxt, coe_pow (i + 1)]
        have hcur2 : (↑L2[j] : α) = (f ^ i) x := by
          rw [ez, coe_pow i]
        have hnext : f (↑L2[j]) = (f ^ (i + 1)) x := by
          rw [hcur2, pow_succ', Perm.mul_apply]
        have hx' : (f ^ (i + 1)) x ≠ x := ne_x (i + 1) (by omega) (by omega)
        have hy' : (f ^ (i + 1)) x ≠ y := ne_y (i + 1) (by omega) (by omega)
        rw [hnext, swap_apply_of_ne_of_ne hx' hy']
      · -- boundary of L2 wraps to its head: f^n x = x maps to y
        have hjb : j + 1 = n - k := by omega
        have h0l : (j + 1) % L2.length = 0 := by rw [hlen2, hjb]; simp
        simp only [h0l]
        have e0 : L2[0] = yβ := by
          simp only [hL2, List.getElem_drop, add_zero, hL, List.getElem_map,
            List.getElem_range]
          exact hkxy
        rw [e0]
        have hcur2 : (↑L2[j] : α) = (f ^ i) x := by
          rw [ez, coe_pow i]
        show (swap x y) (f ↑L2[j]) = y
        rw [hcur2]
        have hlast : f ((f ^ i) x) = x := by
          have heq : f ((f ^ i) x) = (f ^ (i + 1)) x := by
            rw [pow_succ', Perm.mul_apply]
          rw [heq, show i + 1 = n from by omega, hfnx]
        rw [hlast]
        simp
  have h1orb : orbitsOn s f hsinv = 1 :=
    orbitsOn_eq_one s f hsinv ⟨x, hxs⟩ hp
  have hq2 : orbits q = 2 :=
    orbits_eq_two_of_cycleLists L1 L2 h1n h2n hdis hcov2 htne hcne q hqeq
  have h2orb : orbitsOn s g hginv = 2 := by
    unfold orbitsOn
    rw [hcardn]
    simpa [hn, orbits] using hq2
  have hch := orbits_change s f g hsinv hginv hout
  rw [h1orb, h2orb] at hch
  have hfin : orbits g = orbits f + 1 := by omega
  exact hfin

/-- Multiplying by a transposition whose two points lie in DISTINCT cycles of
`f` merges those cycles into one: the number of orbits drops by exactly one.
A fixed point is a cycle of length one, so attaching a fixed point is covered.
The proof is a trick: with `g = swap x y * f`, the iterates `g^i x` follow the
`f`-cycle through `x` until at the end they land on `y`, so in `g` the points
`x y` are in the SAME cycle; applying the split lemma to `g` gives the join
count for `f`. -/
lemma orbits_swap_different_cycles {x y : α} (hne : x ≠ y)
    (h : ¬ f.SameCycle x y) :
    orbits (swap x y * f) + 1 = orbits f := by
  set sx : Finset α := cyc f x with hsx
  have hcx : f.IsCycleOn sx := cyc_isCycleOn f x
  have hxx : x ∈ sx := cyc_mem_self f x
  have hxinv : ∀ z, f z ∈ sx ↔ z ∈ sx := fun z => hcx.apply_mem_iff
  set a : ℕ := sx.card with ha
  have ha0 : 0 < a := Finset.card_pos.mpr ⟨x, hxx⟩
  have hfa : (f ^ a) x = x := by
    simpa [ha] using hcx.pow_card_apply hxx
  have hper : ∀ i, (f ^ i) x ∈ sx := by
    intro i
    induction i with
    | zero => exact hxx
    | succ i ih =>
      rw [pow_succ', Perm.mul_apply]
      exact (hxinv ((f ^ i) x)).mpr ih
  have hyn : y ∉ sx := fun hy => h ((mem_cyc_iff f).mp hy)
  have hneq_x : ∀ i, 0 < i → i < a → (f ^ i) x ≠ x := by
    intro i hi hlt heq
    have hd : a ∣ i := by
      simpa [ha] using (hcx.pow_apply_eq hxx).mp heq
    exact Nat.not_dvd_of_pos_of_lt hi hlt hd
  let g : Perm α := swap x y * f
  have hgit : ∀ i, i ≤ a → (g ^ i) x = if i = a then y else (f ^ i) x := by
    intro i hi
    induction i with
    | zero =>
      simp only [pow_zero, Perm.one_apply]
      have hna : (0 : ℕ) ≠ a := by omega
      rw [ite_eq_right hna]
    | succ i ih =>
      have ifi : i ≠ a := by omega
      rw [pow_succ', Perm.mul_apply, ih (by omega), ite_eq_right ifi]
      show (swap x y * f) ((f ^ i) x) =
          if i + 1 = a then y else (f ^ (i + 1)) x
      by_cases hia : i + 1 = a
      · -- last step of the cycle: f^a x = x is sent to y
        rw [ite_eq_left hia, Perm.mul_apply]
        have hlast : f ((f ^ i) x) = x := by
          have heq : f ((f ^ i) x) = (f ^ (i + 1)) x := by
            rw [pow_succ', Perm.mul_apply]
          rw [heq, hia, hfa]
        rw [hlast]
        simp
      · -- ordinary step: f^(i+1) x is neither x nor y, so the swap fixes it
        have hilt : i + 1 < a := by omega
        rw [ite_eq_right (by omega), Perm.mul_apply]
        have hsucc : f ((f ^ i) x) = (f ^ (i + 1)) x := by
          rw [pow_succ', Perm.mul_apply]
        rw [hsucc]
        have hnx : (f ^ (i + 1)) x ≠ x := hneq_x (i + 1) (by omega) hilt
        have hny : (f ^ (i + 1)) x ≠ y := fun e => hyn (e ▸ hper (i + 1))
        exact swap_apply_of_ne_of_ne hnx hny
  have hga : (g ^ a) x = y := by
    have h := hgit a (by rfl)
    simpa using h
  have hgsame : g.SameCycle x y :=
    ⟨(a : ℤ), by exact_mod_cast hga⟩
  have hsplit := orbits_swap_same_cycle g hne hgsame
  have hss : swap x y * g = f := by
    show swap x y * (swap x y * f) = f
    have hsq : swap x y * swap x y = (1 : Perm α) := by
      ext z
      simp
    rw [← mul_assoc, hsq, one_mul]
  rw [hss] at hsplit
  exact hsplit.symm

/-- Left-multiplying a permutation by any transposition raises the number of
orbits by at most one (it either splits one cycle or joins two). -/
lemma orbits_swap_le {x y : α} (hne : x ≠ y) :
    orbits (swap x y * f) ≤ orbits f + 1 := by
  by_cases h : f.SameCycle x y
  · rw [orbits_swap_same_cycle f hne h]
  · have hj := orbits_swap_different_cycles f hne h
    omega

end SplitJoin

section Involution

/-- Every involution on a finite type is a product of pairwise disjoint
transpositions, one for each nontrivial two-cycle: its support has exactly
twice as many darts as there are transpositions. -/
lemma involution_swap_factor :
    ∀ (f : Perm α), f ^ 2 = 1 →
      ∃ (L : List (Perm α)),
        (∀ t ∈ L, ∃ (x : α), x ≠ f x ∧ t = swap x (f x)) ∧
        L.prod = f ∧
        (∀ t ∈ L, ∀ u ∈ L, t ≠ u → Disjoint t.support u.support) ∧
        (∀ t ∈ L, t.support ⊆ f.support) ∧
        f.support.card = 2 * L.length := by
  have hmain : ∀ (n : ℕ), ∀ (f : Perm α), f ^ 2 = 1 → f.support.card = n →
      ∃ (L : List (Perm α)),
        (∀ t ∈ L, ∃ (x : α), x ≠ f x ∧ t = swap x (f x)) ∧
        L.prod = f ∧
        (∀ t ∈ L, ∀ u ∈ L, t ≠ u → Disjoint t.support u.support) ∧
        (∀ t ∈ L, t.support ⊆ f.support) ∧
        f.support.card = 2 * L.length := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f h2 hcard
      by_cases hem : f.support = ∅
      · have hf1 : f = 1 := support_eq_empty_iff.mp hem
        refine ⟨[], by simp, by rw [hf1]; simp, by simp, by simp, by simp [hem]⟩
      · have hne : f.support.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hem
        obtain ⟨x, hx⟩ := hne
        set y : α := f x with hydef
        have hxfx : x ≠ f x := (Equiv.Perm.mem_support.mp hx).symm
        have hxy : x ≠ y := by simpa [hydef] using hxfx
        have hyx : f y = x := by
          have h : (f ^ 2) x = x := by rw [h2]; simp
          simpa [pow_succ', Perm.mul_apply, hydef] using h
        have hyf : f y ≠ y := by
          rw [hyx]; intro h; exact hxy h
        set t : Perm α := swap x y with htdef
        set f' : Perm α := t * f with hf'def
        have hfx' : f' x = x := by
          simp [hf'def, htdef, Perm.mul_apply, hydef]
        have hfy' : f' y = y := by
          simp [hf'def, htdef, Perm.mul_apply, hyx]
        have hzin : ∀ z, z ≠ x → z ≠ y → f z ≠ x ∧ f z ≠ y := by
          intro z hzx hzy
          constructor
          · intro e
            have : f (f z) = f x := by rw [e]
            have h9 : (f ^ 2) z = y := by simpa [pow_succ', Perm.mul_apply, hydef] using this
            have h10 : z = y := by rw [h2] at h9; simpa using h9
            exact hzy h10
          · intro e
            have : f (f z) = f y := by rw [e]
            have h9 : (f ^ 2) z = x := by simpa [pow_succ', Perm.mul_apply, hyx] using this
            have h10 : z = x := by rw [h2] at h9; simpa using h9
            exact hzx h10
        have hf'z : ∀ z, z ≠ x → z ≠ y → f' z = f z := by
          intro z hzx hzy
          have h1 : f z ≠ x := (hzin z hzx hzy).1
          have h2' : f z ≠ y := (hzin z hzx hzy).2
          exact swap_apply_of_ne_of_ne h1 h2'
        have hxs : x ∈ f.support := Equiv.Perm.mem_support.mpr hxfx.symm
        have hys : y ∈ f.support := Equiv.Perm.mem_support.mpr hyf
        have hsup' : f'.support = f.support \ {x, y} := by
          ext z
          rcases eq_or_ne z x with (rfl | hzx)
          · simp [Equiv.Perm.mem_support, hfx', hxs]
          rcases eq_or_ne z y with (rfl | hzy)
          · simp [Equiv.Perm.mem_support, hfy', hys]
          · have hfz : f' z = f z := hf'z z hzx hzy
            simp [Equiv.Perm.mem_support, hfz, hzx, hzy]
        have hcomm : f * t = t * f := by
          rw [mul_swap_eq_swap_mul, hydef, hyx, swap_comm y x]
        have htt : t * t = 1 := by
          ext z
          simp [htdef]
        have h2' : f' ^ 2 = 1 := by
          simp only [hf'def, pow_two]
          calc t * f * (t * f)
              = t * (f * t) * f := by simp [mul_assoc]
            _ = t * (t * f) * f := by rw [hcomm]
            _ = (t * t) * (f * f) := by simp [mul_assoc]
            _ = 1 * (f * f) := by rw [htt]
            _ = 1 := by rw [one_mul, ← pow_two, h2]
        have hpair : ({x, y} : Finset α) ⊆ f.support := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with (rfl | rfl) <;> tauto
        have hcard' : f'.support.card = f.support.card - 2 := by
          rw [hsup', Finset.card_sdiff, Finset.inter_eq_left.mpr hpair]
          simp [hxy]
        have hn2 : 2 ≤ f.support.card := by
          have hle : ({x, y} : Finset α).card ≤ f.support.card :=
            Finset.card_le_card hpair
          simp [hxy] at hle
          exact hle
        have hlt : f'.support.card < n := by
          rw [hcard', hcard]
          omega
        obtain ⟨L', hlswap, hlprod, hldisj, hlsupp, hlcard⟩ :=
          ih f'.support.card hlt f' h2' rfl
        set L : List (Perm α) := t :: L' with hLdef
        have htswap : ∃ (z : α), z ≠ f z ∧ t = swap z (f z) :=
          ⟨x, hxfx, by simp [htdef, hydef]⟩
        have hlswapf : ∀ u ∈ L', ∃ (z : α), z ≠ f z ∧ u = swap z (f z) := by
          intro u hu
          obtain ⟨z, hzn, hzu⟩ := hlswap u hu
          have hzs : z ∈ u.support := by
            rw [hzu, support_swap hzn]
            simp
          have hzsf : z ∈ f'.support := hlsupp u hu hzs
          rw [hsup'] at hzsf
          have hsd2 : z ∈ f.support ∧ z ∉ ({x, y} : Finset α) :=
            Finset.mem_sdiff.mp hzsf
          have hnin : z ∉ ({x, y} : Finset α) := hsd2.2
          have hzx : z ≠ x := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hnin
            tauto
          have hzy : z ≠ y := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hnin
            tauto
          have heq : f' z = f z := hf'z z hzx hzy
          exact ⟨z, by rwa [heq] at hzn, by rw [heq] at hzu; exact hzu⟩
        have hLswap : ∀ q ∈ L, ∃ (z : α), z ≠ f z ∧ q = swap z (f z) := by
          intro q hq
          simp only [hLdef, List.mem_cons] at hq
          rcases hq with (rfl | hq)
          · exact htswap
          · exact hlswapf q hq
        have hLprod : L.prod = f := by
          rw [hLdef, List.prod_cons, hlprod, hf'def]
          rw [← mul_assoc, htt, one_mul]
        have htsupp : t.support = {x, y} := support_swap hxy
        have hsd : Disjoint ({x, y} : Finset α) (f.support \ {x, y}) :=
          Finset.disjoint_sdiff
        have htdis : ∀ u ∈ L', Disjoint t.support u.support := by
          intro u hu
          have h1 : u.support ⊆ f'.support := hlsupp u hu
          rw [htsupp]
          rw [hsup'] at h1
          exact Finset.disjoint_of_subset_right h1 hsd
        have hLdisj : ∀ q ∈ L, ∀ r ∈ L, q ≠ r → Disjoint q.support r.support := by
          intro q hq r hr hne
          simp only [hLdef, List.mem_cons] at hq hr
          rcases hq with (rfl | hq)
          · rcases hr with (rfl | hr)
            · contradiction
            · exact htdis r hr
          · rcases hr with (rfl | hr)
            · exact (htdis q hq).symm
            · exact hldisj q hq r hr hne
        have hLsupp : ∀ q ∈ L, q.support ⊆ f.support := by
          intro q hq
          simp only [hLdef, List.mem_cons] at hq
          rcases hq with (rfl | hq)
          · rw [htsupp]; exact hpair
          · have h1 : q.support ⊆ f'.support := hlsupp q hq
            rw [hsup'] at h1
            exact Finset.Subset.trans h1 Finset.sdiff_subset
        have hcc : f.support.card = f'.support.card + 2 := by omega
        have hLcard : f.support.card = 2 * L.length := by
          rw [hcc, hlcard, hLdef, List.length_cons]
          ring
        exact ⟨L, hLswap, hLprod, hLdisj, hLsupp, hLcard⟩
  intro f h2
  exact hmain f.support.card f h2 rfl

end Involution

section Union

/-- Orbit counts add over a disjoint union of two invariant finsets. -/
lemma orbitsOn_union {C D : Finset α} (hdis : Disjoint C D)
    (f : Perm α) (hC : ∀ z, f z ∈ C ↔ z ∈ C) (hD : ∀ z, f z ∈ D ↔ z ∈ D)
    (hU : ∀ z, f z ∈ C ∪ D ↔ z ∈ C ∪ D) :
    orbitsOn (C ∪ D) f hU = orbitsOn C f hC + orbitsOn D f hD := by
  let pC := part C f hC
  let pD := part D f hD
  let pU := part (C ∪ D) f hU
  let qC := partPerm C f hC
  let qD := partPerm D f hD
  have hfac : pC * pD = pU := by
    ext z
    simp only [Perm.mul_apply]
    by_cases hzC : z ∈ C
    · have hzD : z ∉ D := Finset.disjoint_left.mp hdis hzC
      have e1 : pD z = z := part_not_mem D f hD hzD
      have e2 : pC z = f z := part_mem C f hC hzC
      have e3 : pU z = f z := part_mem (C ∪ D) f hU (Finset.mem_union_left D hzC)
      rw [e1, e2, e3]
    · by_cases hzD : z ∈ D
      · have hzC' : z ∉ C := hzC
        have fzD : f z ∈ D := (hD z).mpr hzD
        have fzC : f z ∉ C := fun h => Finset.disjoint_left.mp hdis h fzD
        have e1 : pC (f z) = f z := part_not_mem C f hC fzC
        have e2 : pD z = f z := part_mem D f hD hzD
        have e3 : pU z = f z := part_mem (C ∪ D) f hU (Finset.mem_union_right C hzD)
        rw [e2, e1, e3]
      · have e1 : pC z = z := part_not_mem C f hC hzC
        have e2 : pD z = z := part_not_mem D f hD hzD
        have hzU : z ∉ C ∪ D := by simp [hzC, hzD]
        have e3 : pU z = z := part_not_mem (C ∪ D) f hU hzU
        rw [e2, e1, e3]
  have hsuppC : pC.support ⊆ C := support_part_subset C f hC
  have hsuppD : pD.support ⊆ D := support_part_subset D f hD
  have hdis' : Disjoint pC pD := by
    rw [disjoint_iff_disjoint_support]
    exact Finset.disjoint_of_subset_left hsuppC
      (Finset.disjoint_of_subset_right hsuppD hdis)
  have hsC : qC.cycleType.sum ≤ C.card := by
    rw [sum_cycleType qC]
    have := Finset.card_le_univ qC.support
    rw [Fintype.card_subtype] at this
    simpa using this
  have hsD : qD.cycleType.sum ≤ D.card := by
    rw [sum_cycleType qD]
    have := Finset.card_le_univ qD.support
    rw [Fintype.card_subtype] at this
    simpa using this
  have hcard : (C ∪ D).card = C.card + D.card := Finset.card_union_of_disjoint hdis
  have hct : pU.cycleType = qC.cycleType + qD.cycleType := by
    have h1 : (pC * pD).cycleType = pC.cycleType + pD.cycleType := hdis'.cycleType_mul
    have h2 : pC.cycleType = qC.cycleType := cycleType_part C f hC
    have h3 : pD.cycleType = qD.cycleType := cycleType_part D f hD
    rw [hfac] at h1
    rw [h1, h2, h3]
  have hqU : (partPerm (C ∪ D) f hU).cycleType =
      (partPerm C f hC).cycleType + (partPerm D f hD).cycleType := by
    have h4 : pU.cycleType = (partPerm (C ∪ D) f hU).cycleType :=
      cycleType_part (C ∪ D) f hU
    rw [← h4, hct]
  have hsubb : C.card + D.card - (qC.cycleType.sum + qD.cycleType.sum) =
      (C.card - qC.cycleType.sum) + (D.card - qD.cycleType.sum) := by
    omega
  have hgoal : orbitsOn (C ∪ D) f hU = orbitsOn C f hC + orbitsOn D f hD := by
    simp only [orbitsOn, hqU, Multiset.card_add, Multiset.sum_add, hcard]
    rw [hsubb]
    ring
  exact hgoal

end Union

section Fold

/-- Left-multiplying `p` by a list of transpositions raises the orbit count by
at most the number of transpositions. -/
lemma orbits_prod_swap_le (L : List (Perm α)) (p : Perm α)
    (h : ∀ t ∈ L, ∃ (x y : α), x ≠ y ∧ t = swap x y) :
    orbits (L.prod * p) ≤ orbits p + L.length := by
  induction L with
  | nil =>
    simp
  | cons t L ih =>
    have ht : t ∈ (t :: L) := by simp
    obtain ⟨x, y, hne, rfl⟩ := h t ht
    have hL : ∀ u ∈ L, ∃ (a b : α), a ≠ b ∧ u = swap a b := fun u hu =>
      h u (by simp [hu])
    rw [List.prod_cons, List.length_cons, mul_assoc]
    have h1 : orbits (swap x y * (L.prod * p)) ≤ orbits (L.prod * p) + 1 :=
      orbits_swap_le (L.prod * p) hne
    have h2 := ih hL
    omega

end Fold

section Invar

/-- A finset invariant under a permutation is invariant under its inverse. -/
lemma inv_invar (p : Perm α) {C : Finset α} (hC : ∀ z, p z ∈ C ↔ z ∈ C) :
    ∀ z, p⁻¹ z ∈ C ↔ z ∈ C := by
  intro z
  constructor
  · intro h
    have h4 : p (p⁻¹ z) ∈ C := (hC (p⁻¹ z)).mpr h
    simpa using h4
  · intro h
    by_contra h6
    have h7 : p (p⁻¹ z) ∉ C := (hC (p⁻¹ z)).not.mpr h6
    have h8 : p (p⁻¹ z) = z := by simp
    rw [h8] at h7
    exact h7 h

/-- Every integer iterate of a permutation keeps an invariant finset invariant:
if `z ∈ C`, then `p^i z ∈ C` for every `i : ℤ`. -/
lemma zpow_mem_of_invar (p : Perm α) {C : Finset α} (hC : ∀ z, p z ∈ C ↔ z ∈ C) :
    ∀ {z : α}, z ∈ C → ∀ (i : ℤ), (p ^ i) z ∈ C := by
  have hpos : ∀ (n : ℕ) (z : α), z ∈ C → (p ^ n) z ∈ C := by
    intro n
    induction n with
    | zero =>
      intro z hz
      simpa using hz
    | succ n ih =>
      intro z hz
      have h1 : (p ^ n) z ∈ C := ih z hz
      have h2 : p ((p ^ n) z) ∈ C := (hC ((p ^ n) z)).mpr h1
      have h3 : p ((p ^ n) z) = (p ^ (n + 1)) z := by
        rw [pow_succ', Perm.mul_apply]
      rw [h3] at h2
      exact h2
  have hCi := inv_invar p hC
  have hneg : ∀ (n : ℕ) (z : α), z ∈ C → (p⁻¹ ^ n) z ∈ C := by
    intro n
    induction n with
    | zero =>
      intro z hz
      simpa using hz
    | succ n ih =>
      intro z hz
      have h1 : (p⁻¹ ^ n) z ∈ C := ih z hz
      have h2 : p⁻¹ ((p⁻¹ ^ n) z) ∈ C := (hCi ((p⁻¹ ^ n) z)).mpr h1
      have h3 : p⁻¹ ((p⁻¹ ^ n) z) = (p⁻¹ ^ (n + 1)) z := by
        rw [pow_succ', Perm.mul_apply]
      rw [h3] at h2
      exact h2
  intro z hz i
  match i with
  | Int.ofNat n => exact hpos n z hz
  | Int.negSucc n => simpa [zpow_negSucc] using hneg (n + 1) z hz

/-- Restricting to an invariant finset, the permutation and its inverse have the
same number of orbits inside it. -/
lemma orbitsOn_inv (C : Finset α) (p : Perm α) (hC : ∀ z, p z ∈ C ↔ z ∈ C) :
    orbitsOn C p⁻¹ (inv_invar p hC) = orbitsOn C p hC := by
  have hq : partPerm C p⁻¹ (inv_invar p hC) = (partPerm C p hC)⁻¹ := by
    simp [partPerm, inv_subtypePerm]
  have hci : (partPerm C p hC)⁻¹.cycleType = (partPerm C p hC).cycleType :=
    cycleType_inv (partPerm C p hC)
  simp only [orbitsOn, hq, hci]

/-- A permutation and its inverse have the same number of orbits. -/
lemma orbits_inv (p : Perm α) : orbits p⁻¹ = orbits p := by
  simp only [orbits, cycleType_inv]

/-- The number of orbits on the whole type equals the unrestricted orbit count. -/
lemma orbitsOn_univ (p : Perm α) :
    orbitsOn (Finset.univ : Finset α) p (fun z => by simp) = orbits p := by
  let h : ∀ z, p z ∈ (Finset.univ : Finset α) ↔ z ∈ (Finset.univ : Finset α) :=
    fun z => by simp
  have hpart : part (Finset.univ : Finset α) p h = p := by
    ext z
    exact part_mem _ _ h (Finset.mem_univ z)
  have hqct : (partPerm (Finset.univ : Finset α) p h).cycleType = p.cycleType := by
    have h5 := cycleType_part (Finset.univ : Finset α) p h
    rw [hpart] at h5
    exact h5.symm
  have hsub : (Finset.univ : Finset α).card = Fintype.card α := by simp
  simp only [orbitsOn, orbits, hqct, hsub]

end Invar

section ListProd

/-- A product of pairwise support-disjoint permutations (from a nodup list) acts,
on the support of any one factor, exactly as that factor; and a point outside
every support is fixed. -/
lemma disjoint_prod_apply (L : List (Perm α)) (hn : L.Nodup)
    (hdis : ∀ t ∈ L, ∀ u ∈ L, t ≠ u → Disjoint t.support u.support) :
    (∀ t ∈ L, ∀ z ∈ t.support, L.prod z = t z) ∧
    (∀ z, (∀ t ∈ L, z ∉ t.support) → L.prod z = z) := by
  induction L with
  | nil => simp
  | cons t L ih =>
    have htn : t ∉ L := (List.nodup_cons.mp hn).1
    have hLn : L.Nodup := (List.nodup_cons.mp hn).2
    have hin : ∀ u ∈ L, u ∈ (t :: L) := fun u hu =>
      List.mem_cons.mpr (Or.inr hu)
    have htd : ∀ u ∈ L, Disjoint t.support u.support := fun u hu =>
      hdis t (by simp) u (hin u hu) (fun h => htn (h.symm ▸ hu))
    have hLD : ∀ u ∈ L, ∀ v ∈ L, u ≠ v → Disjoint u.support v.support :=
      fun u hu v hv hne => hdis u (hin u hu) v (hin v hv) hne
    have ⟨hA, hB⟩ := ih hLn hLD
    constructor
    · intro q hq z hz
      simp only [List.mem_cons] at hq
      rcases hq with (rfl | hq)
      · -- the head factor: every later factor fixes z
        have hzL : ∀ u ∈ L, z ∉ u.support := fun u hu =>
          Finset.disjoint_left.mp (htd u hu) hz
        have h1 : L.prod z = z := hB z hzL
        rw [List.prod_cons, Perm.mul_apply, h1]
      · -- an old factor: the head fixes both z and q z
        have hzt : z ∉ t.support :=
          Finset.disjoint_left.mp (htd q hq).symm hz
        have hqz : q z ∈ q.support := by
          by_contra h9
          have h10 : q (q z) = q z := by
            simpa [Equiv.Perm.mem_support] using h9
          have h11 : q z = z := q.injective h10
          exact Equiv.Perm.mem_support.mp hz h11
        have hqzt : q z ∉ t.support :=
          Finset.disjoint_left.mp (htd q hq).symm hqz
        have h2 : L.prod z = q z := hA q hq z hz
        rw [List.prod_cons, Perm.mul_apply, h2]
        simpa using hqzt
    · intro z hz
      have hnt : z ∉ t.support := hz t (by simp)
      have h1 : t z = z := by simpa using hnt
      have h2 : L.prod z = z := hB z fun u hu => hz u (hin u hu)
      rw [List.prod_cons, Perm.mul_apply, h2, h1]

end ListProd

section Crossing

/-- If a nonempty proper finset `C` is invariant under `σ` and the group
generated by `{τ, σ}` acts transitively (is connected), then some point `a ∈ C`
is joined by `τ` to a point outside `C`: there is an edge crossing the cut. -/
lemma crossing_pair (σ τ : Perm α) (hτ2 : τ ^ 2 = 1)
    {C : Finset α} (hCσ : ∀ z, σ z ∈ C ↔ z ∈ C)
    (hCprop : C ≠ Finset.univ) (_hCne : C.Nonempty)
    (hconn : ∀ (x y : α), y ∈ MulAction.orbit
        (Subgroup.closure ({τ, σ} : Set (Perm α))) x)
    {x0 : α} (hx0 : x0 ∈ C) :
    ∃ a, a ∈ C ∧ τ a ∉ C := by
  by_contra h
  have hin : ∀ a, a ∈ C → τ a ∈ C := by
    intro a ha
    by_contra h2
    exact h ⟨a, ha, h2⟩
  have hτz : ∀ z, τ (τ z) = z := by
    intro z
    have h9 : (τ ^ 2) z = z := by rw [hτ2]; simp
    simpa [pow_two, Perm.mul_apply] using h9
  have hCτ : ∀ z, τ z ∈ C ↔ z ∈ C := by
    intro z
    constructor
    · intro hz
      have h9 : τ (τ z) ∈ C := hin (τ z) hz
      rw [hτz z] at h9
      exact h9
    · exact hin z
  have hcl : ∀ (g : Perm α), g ∈ Subgroup.closure ({τ, σ} : Set (Perm α)) →
      ∀ z, z ∈ C → g z ∈ C := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem u hu =>
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with (rfl | rfl)
      · exact (hCτ z).mpr hz
      · exact (hCσ z).mpr hz
    | one => intro z hz; simpa using hz
    | mul u v _ _ ihu ihv =>
      intro z hz
      rw [Perm.mul_apply]
      exact ihu (v z) (ihv z hz)
    | inv u _ ihu =>
      intro z hz
      have him : Finset.image u C ⊆ C := by
        intro w hw
        rcases Finset.mem_image.mp hw with ⟨y, hy, rfl⟩
        exact ihu y hy
      have heq : Finset.image u C = C := by
        apply Finset.eq_of_subset_of_card_le him
        rw [Finset.card_image_of_injective _ u.injective]
      have hz' : z ∈ Finset.image u C := by rw [heq]; exact hz
      rcases Finset.mem_image.mp hz' with ⟨y, hy, hyu⟩
      have hiy : u⁻¹ z = y := u.injective (by simp [hyu])
      rw [hiy]
      exact hy
  have hall : ∀ (y : α), y ∈ C := by
    intro y
    have hy : y ∈ MulAction.orbit _ x0 := hconn x0 y
    rw [MulAction.mem_orbit_iff] at hy
    rcases hy with ⟨g, hgy⟩
    have hgy' : (g : Perm α) • x0 = y := hgy
    have hres : (g : Perm α) x0 ∈ C := hcl (g : Perm α) g.property x0 hx0
    have heq : (g : Perm α) x0 = y := by simpa using hgy'
    rw [heq] at hres
    exact hres
  have huniv : C = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
  exact hCprop huniv

end Crossing

section Growth

/-- Connected-growth (spanning-tree) lemma. If the group generated by the edge
involution `τ` and the vertex rotation `σ` acts transitively (the map is
connected), then the vertex cycles of `σ` can be merged into a single orbit by
a sequence of edge transpositions `t = swap a (τ a)`: there is a pairwise
support-disjoint, nodup list `tree` with `tree.length + 1 = orbits σ` (the
number of vertices) such that `p = tree.prod * σ⁻¹` has exactly one orbit. Each
tree edge joins two distinct cycles, exactly as a spanning tree joins the
vertices of a connected graph. -/
lemma connected_growth (σ τ : Perm α) (hτ2 : τ ^ 2 = 1)
    (hconn : ∀ (x y : α), y ∈ MulAction.orbit
        (Subgroup.closure ({τ, σ} : Set (Perm α))) x)
    (x0 : α) :
    ∃ (tree : List (Perm α)) (p : Perm α),
      (∀ t ∈ tree, ∃ a, t = swap a (τ a)) ∧
      (∀ t ∈ tree, ∀ u ∈ tree, t ≠ u → Disjoint t.support u.support) ∧
      tree.Nodup ∧
      p = tree.prod * σ⁻¹ ∧
      orbits p = 1 ∧
      tree.length + 1 = orbits σ := by
  have hτz : ∀ z, τ (τ z) = z := by
    intro z
    have h9 : (τ ^ 2) z = z := by rw [hτ2]; simp
    simpa [pow_two, Perm.mul_apply] using h9
  have hmain : ∀ (n : ℕ) (C : Finset α) (tree : List (Perm α)) (p : Perm α),
      (Finset.univ \ C).card = n →
      (hCσ : ∀ z, σ z ∈ C ↔ z ∈ C) →
      (x0 ∈ C) →
      (hpeq : p = tree.prod * σ⁻¹) →
      (hswap : ∀ t ∈ tree, ∃ a, t = swap a (τ a)) →
      (hdis : ∀ t ∈ tree, ∀ u ∈ tree, t ≠ u → Disjoint t.support u.support) →
      (hnodup : tree.Nodup) →
      (hsupp : ∀ t ∈ tree, t.support ⊆ C) →
      (hCp : ∀ z, p z ∈ C ↔ z ∈ C) →
      (hout : ∀ z, z ∉ C → p z = σ⁻¹ z) →
      (hcov : orbitsOn C σ hCσ = tree.length + 1) →
      (hone : orbitsOn C p hCp = 1) →
      (horb : orbits p + tree.length = orbits σ) →
      ∃ (tree' : List (Perm α)) (p' : Perm α),
        (∀ t ∈ tree', ∃ a, t = swap a (τ a)) ∧
        (∀ t ∈ tree', ∀ u ∈ tree', t ≠ u → Disjoint t.support u.support) ∧
        tree'.Nodup ∧
        p' = tree'.prod * σ⁻¹ ∧
        orbits p' = 1 ∧
        tree'.length + 1 = orbits σ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro C tree p hcard hCσ hx0 hpeq hswap hdis hnodup hsupp hCp hout
        hcov hone horb
      by_cases hfull : C = Finset.univ
      · -- C covers the whole type: p is a single orbit and the count is done
        subst hfull
        have hop1 : orbitsOn (Finset.univ : Finset α) p hCp = orbits p := by
          have h1 := orbitsOn_congr rfl p hCp (fun z => by simp)
          rw [h1, orbitsOn_univ p]
        have hp1 : orbits p = 1 := by
          rw [hop1] at hone
          exact hone
        have hσ1 : orbitsOn (Finset.univ : Finset α) σ hCσ = orbits σ := by
          have h1 := orbitsOn_congr rfl σ hCσ (fun z => by simp)
          rw [h1, orbitsOn_univ σ]
        have hlen : tree.length + 1 = orbits σ := by
          rw [hσ1] at hcov
          exact hcov.symm
        exact ⟨tree, p, hswap, hdis, hnodup, hpeq, hp1, hlen⟩
      · -- C is proper: connectedness gives an edge crossing the cut C | Cᶜ
        have hCprop : C ≠ Finset.univ := hfull
        have hCne : C.Nonempty := ⟨x0, hx0⟩
        obtain ⟨a, haC, hbnC⟩ :=
          crossing_pair σ τ hτ2 hCσ hCprop hCne hconn hx0
        set b : α := τ a with hbdef
        have hbC : b ∉ C := hbnC
        have hne : a ≠ b := by
          intro e
          exact hbC (e.symm ▸ haC)
        set D : Finset α := cyc σ b with hDdef
        have hDcyc : σ.IsCycleOn D := cyc_isCycleOn σ b
        have hDσ : ∀ z, σ z ∈ D ↔ z ∈ D := fun z => hDcyc.apply_mem_iff
        have hbD : b ∈ D := cyc_mem_self σ b
        have hDne : D.Nonempty := ⟨b, hbD⟩
        have hCD : Disjoint C D := by
          rw [Finset.disjoint_left]
          intro z hzC hzD
          have hsz : σ.SameCycle b z := (mem_cyc_iff σ).mp hzD
          rcases hsz with ⟨i, hi⟩
          have h10 : (σ ^ (-i)) * (σ ^ i) = (1 : Perm α) := by
            rw [← zpow_add, neg_add_cancel]
            simp
          have hbz : (σ ^ (-i)) z = b := by
            have h11 : (σ ^ (-i)) z = (σ ^ (-i)) ((σ ^ i) b) := by rw [hi]
            rw [h11]
            rw [← Perm.mul_apply, h10, Perm.one_apply]
          have hbiC : b ∈ C := by
            have h12 : (σ ^ (-i)) z ∈ C := zpow_mem_of_invar σ hCσ hzC (-i)
            rw [hbz] at h12
            exact h12
          exact hbC hbiC
        set t : Perm α := swap a b with htdef
        have hnotsame : ¬ p.SameCycle a b := by
          intro h
          rcases h with ⟨i, hi⟩
          have h12 : (p ^ i) a ∈ C := zpow_mem_of_invar p hCp haC i
          rw [hi] at h12
          exact hbC h12
        have hjoin : orbits (t * p) + 1 = orbits p :=
          orbits_swap_different_cycles p hne hnotsame
        set C' := C ∪ D with hC'def
        set p' := t * p with hp'def
        set tree' := t :: tree with htree'def
        have hC'σ : ∀ z, σ z ∈ C' ↔ z ∈ C' := by
          intro z
          simp only [hC'def, Finset.mem_union]
          rw [hCσ z, hDσ z]
        have hx0' : x0 ∈ C' := Finset.mem_union_left D hx0
        have hpeq' : p' = tree'.prod * σ⁻¹ := by
          rw [hp'def, htree'def, List.prod_cons, hpeq]
          rw [mul_assoc]
        have htswap : ∃ c, t = swap c (τ c) :=
          ⟨a, by simp [htdef, hbdef]⟩
        have hswap' : ∀ q ∈ tree', ∃ c, q = swap c (τ c) := by
          intro q hq
          simp only [htree'def, List.mem_cons] at hq
          rcases hq with (rfl | hq)
          · exact htswap
          · exact hswap q hq
        have htsupp : t.support = {a, b} := support_swap hne
        have htdis : ∀ u ∈ tree, Disjoint t.support u.support := by
          intro u hu
          obtain ⟨c, hcu⟩ := hswap u hu
          have husub : u.support ⊆ C := hsupp u hu
          by_cases hc : c = τ c
          · -- degenerate transposition: u = 1 with empty support
            have hcs2 : swap c (τ c) = (1 : Perm α) := by
              have h2 : τ c = c := hc.symm
              rw [h2, swap_self]
              rfl
            have hu1 : u = 1 := by
              rw [hcu]
              exact hcs2
            rw [hu1]
            simp
          · have hcs : u.support = {c, τ c} := by
              rw [hcu]
              exact support_swap hc
            have hcC : c ∈ C := by
              have h : c ∈ u.support := by rw [hcs]; simp
              exact husub h
            have htcC : τ c ∈ C := by
              have h : τ c ∈ u.support := by rw [hcs]; simp
              exact husub h
            have hnb1 : b ≠ c := by
              intro e
              exact hbC (e ▸ hcC)
            have hnb2 : b ≠ τ c := by
              intro e
              exact hbC (e ▸ htcC)
            have hna1 : a ≠ c := by
              intro e
              have h10 : τ a = τ c := by rw [e]
              have h11 : b = τ c := by
                rw [hbdef]
                exact h10
              exact hbC (h11.symm ▸ htcC)
            have hna2 : a ≠ τ c := by
              intro e
              have hτc : τ (τ c) = c := hτz c
              have h10 : τ a = c := by
                rw [e]
                exact hτc
              have h11 : b = c := by
                rw [hbdef]
                exact h10
              exact hbC (h11.symm ▸ hcC)
            rw [htsupp, hcs, Finset.disjoint_left]
            intro z hz1 hz2
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz1 hz2
            rcases hz1 with (hza | hzb)
            · rcases hz2 with (hzc | hztc)
              · exact hna1 (hza.symm.trans hzc)
              · exact hna2 (hza.symm.trans hztc)
            · rcases hz2 with (hzc | hztc)
              · exact hnb1 (hzb.symm.trans hzc)
              · exact hnb2 (hzb.symm.trans hztc)
        have htnin : t ∉ tree := by
          intro htin
          have hd : Disjoint t.support t.support := htdis t htin
          have h9 : ¬ t.support.Nonempty := fun h =>
            let ⟨x, hx⟩ := h
            Finset.disjoint_left.mp hd hx hx
          have he : t.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h9
          rw [htsupp] at he
          simp at he
        have hnodup' : tree'.Nodup := by
          rw [htree'def]
          exact List.nodup_cons.mpr ⟨htnin, hnodup⟩
        have hdis' : ∀ q ∈ tree', ∀ r ∈ tree', q ≠ r →
            Disjoint q.support r.support := by
          intro q hq r hr hneqr
          simp only [htree'def, List.mem_cons] at hq hr
          rcases hq with (rfl | hq)
          · rcases hr with (rfl | hr)
            · contradiction
            · exact htdis r hr
          · rcases hr with (rfl | hr)
            · exact (htdis q hq).symm
            · exact hdis q hq r hr hneqr
        have hsupp' : ∀ q ∈ tree', q.support ⊆ C' := by
          intro q hq
          simp only [htree'def, List.mem_cons] at hq
          rcases hq with (rfl | hq)
          · rw [htsupp]
            intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with (rfl | rfl)
            · exact Finset.mem_union_left D haC
            · exact Finset.mem_union_right C hbD
          · have h1 : q.support ⊆ C := hsupp q hq
            exact fun x hx => Finset.mem_union_left D (h1 hx)
        have hfwd : ∀ z, z ∈ C' → p' z ∈ C' := by
          intro z hz
          simp only [hC'def, Finset.mem_union] at hz
          rcases hz with (hzC | hzD)
          · -- z ∈ C: p z ∈ C; the new swap only sends a across to b ∈ D
            set w := p z with hwdef
            have hwC : w ∈ C := (hCp z).mpr hzC
            have hwnb : w ≠ b := by
              intro e
              have : b ∈ C := e.symm ▸ hwC
              exact hbC this
            by_cases hwa : w = a
            · have htw : t w = b := by
                rw [hwa, htdef]
                simp
              have hres : p' z = b := by
                rw [hp'def, Perm.mul_apply, ←hwdef, htw]
              rw [hres]
              exact Finset.mem_union_right C hbD
            · have hfix : t w = w := swap_apply_of_ne_of_ne hwa hwnb
              have hres : p' z = w := by
                rw [hp'def, Perm.mul_apply, hfix]
              rw [hres]
              exact Finset.mem_union_left D hwC
          · -- z ∈ D (hence z ∉ C): p z = σ⁻¹ z ∈ D
            have hznC : z ∉ C := fun hzC =>
              Finset.disjoint_left.mp hCD hzC hzD
            have h1 : p z = σ⁻¹ z := hout z hznC
            have hDi := inv_invar σ hDσ
            set w := σ⁻¹ z with hwdef
            have hwD : w ∈ D := (hDi z).mpr hzD
            have hwna : w ≠ a := by
              intro e
              have h2 : σ w = σ a := by rw [e]
              have h3 : σ w = z := by simp [hwdef]
              have h4 : σ a ∈ C := (hCσ a).mpr haC
              rw [h3] at h2
              exact hznC (h2 ▸ h4)
            by_cases hwb : w = b
            · have htw : t w = a := by
                rw [hwb, htdef]
                simp
              have hres : p' z = a := by
                rw [hp'def, Perm.mul_apply, h1, htw]
              rw [hres]
              exact Finset.mem_union_left D haC
            · have hfix : t w = w := swap_apply_of_ne_of_ne hwna hwb
              have hres : p' z = w := by
                rw [hp'def, Perm.mul_apply, h1, hfix]
              rw [hres]
              exact Finset.mem_union_right C hwD
        have himg : Finset.image p' C' ⊆ C' := by
          intro w hw
          rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩
          exact hfwd z hz
        have hcardimg : Finset.card (Finset.image p' C') = C'.card := by
          rw [Finset.card_image_of_injective _ p'.injective]
        have himgeq : Finset.image p' C' = C' :=
          Finset.eq_of_subset_of_card_le himg (by rw [hcardimg])
        have hCp' : ∀ z, p' z ∈ C' ↔ z ∈ C' := by
          intro z
          constructor
          · intro h
            have hzimg : p' z ∈ Finset.image p' C' := himgeq.symm ▸ h
            rcases Finset.mem_image.mp hzimg with ⟨y, hy, hpy⟩
            have hzy : z = y := (p'.injective hpy).symm
            rw [hzy]
            exact hy
          · exact hfwd z
        have hout' : ∀ z, z ∉ C' → p' z = σ⁻¹ z := by
          intro z hz
          have hznC : z ∉ C := fun h => hz (Finset.mem_union_left D h)
          have hznD : z ∉ D := fun h => hz (Finset.mem_union_right C h)
          set w := σ⁻¹ z with hwdef
          have hw : p z = w := hout z hznC
          have hwna : w ≠ a := by
            intro e
            have h2 : σ w = σ a := by rw [e]
            have h3 : σ w = z := by simp [hwdef]
            have h4 : σ a ∈ C := (hCσ a).mpr haC
            rw [h3] at h2
            exact hznC (h2 ▸ h4)
          have hwnb : w ≠ b := by
            intro e
            have h2 : σ w = σ b := by rw [e]
            have h3 : σ w = z := by simp [hwdef]
            have h4 : σ b ∈ D := (hDσ b).mpr hbD
            rw [h3] at h2
            exact hznD (h2 ▸ h4)
          have hfix : t w = w := swap_apply_of_ne_of_ne hwna hwnb
          rw [hp'def, Perm.mul_apply, hw, hfix]
        have hD1 : orbitsOn D σ hDσ = 1 :=
          orbitsOn_eq_one D σ hDσ hDne hDcyc.subtypePerm
        have hU' := orbitsOn_union hCD σ hCσ hDσ hC'σ
        have hgoal : orbitsOn (C ∪ D) σ hC'σ = tree'.length + 1 := by
          rw [hU', hcov, hD1, htree'def, List.length_cons]
        have hcov' : orbitsOn C' σ hC'σ = tree'.length + 1 := hgoal
        have hch := orbits_change C' σ⁻¹ p' (inv_invar σ hC'σ) hCp' hout'
        have hinvU := orbitsOn_inv C' σ hC'σ
        have hX : orbitsOn C' σ⁻¹ (inv_invar σ hC'σ) = tree'.length + 1 := by
          rw [hinvU, hcov']
        have hoi : orbits σ⁻¹ = orbits σ := orbits_inv σ
        have hone' : orbitsOn C' p' hCp' = 1 := by
          linarith [hch, hX, hoi, hjoin, horb]
        have horb' : orbits p' + tree'.length = orbits σ := by
          rw [htree'def, List.length_cons]
          omega
        have hDsub : D ⊆ Finset.univ \ C := by
          intro z hz
          have hznC : z ∉ C := fun hzC =>
            Finset.disjoint_left.mp hCD hzC hz
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hznC⟩
        have hcu : Finset.univ \ C' = (Finset.univ \ C) \ D := by
          ext z
          simp [hC'def]
        set m := (Finset.univ \ C').card with hmdef
        have hdec : m = (Finset.univ \ C).card - D.card := by
          rw [hmdef, hcu, Finset.card_sdiff,
            Finset.inter_eq_left.mpr hDsub]
        have hDpos : 0 < D.card := Finset.card_pos.mpr hDne
        have hDle : D.card ≤ (Finset.univ \ C).card :=
          Finset.card_le_card hDsub
        have hlt : m < n := by
          rw [hdec, hcard]
          omega
        exact ih m hlt C' tree' p' rfl hC'σ hx0' hpeq' hswap' hdis' hnodup'
          hsupp' hCp' hout' hcov' hone' horb'
  set C0 : Finset α := cyc σ x0 with hC0def
  have hC0σ : ∀ z, σ z ∈ C0 ↔ z ∈ C0 := fun z =>
    (cyc_isCycleOn σ x0).apply_mem_iff
  have hx00 : x0 ∈ C0 := cyc_mem_self σ x0
  have hC0ne : C0.Nonempty := ⟨x0, hx00⟩
  have hcov0 : orbitsOn C0 σ hC0σ = 1 :=
    orbitsOn_eq_one C0 σ hC0σ hC0ne (cyc_isCycleOn σ x0).subtypePerm
  have hCp0 : ∀ z, σ⁻¹ z ∈ C0 ↔ z ∈ C0 := inv_invar σ hC0σ
  have hone0 : orbitsOn C0 σ⁻¹ hCp0 = 1 := by
    rw [orbitsOn_inv C0 σ hC0σ, hcov0]
  have horb0 : orbits σ⁻¹ + 0 = orbits σ := by
    rw [orbits_inv σ]; simp
  have hcov0' : orbitsOn C0 σ hC0σ = ([] : List (Perm α)).length + 1 := by
    rw [hcov0]; simp
  exact hmain (Finset.univ \ C0).card C0 [] σ⁻¹ rfl hC0σ hx00
    (by simp) (by simp) (by simp) (by simp) (by simp) hCp0 (fun _ _ => rfl)
    hcov0' hone0 horb0

end Growth
section EulerBound

/-- A combinatorial map in the dart/rotation-system sense: a finite type of
darts, a fixed-point-free edge involution `edge` (pairing the two darts of
each edge) and a vertex rotation `vert` (cyclically permuting the darts incident
to each vertex). -/
structure Map (α : Type*) [Fintype α] [DecidableEq α] where
  edge : Perm α
  edge_invol : edge ^ 2 = 1
  edge_noFix : ∀ x, edge x ≠ x
  vert : Perm α

variable (M : Map α)

/-- The face permutation: the edge involution followed by the inverse vertex
rotation; its cycles are the faces of the map. -/
def Map.face (M : Map α) : Perm α := M.edge * M.vert⁻¹

/-- Number of vertices: cycles (orbits) of the vertex rotation. -/
def Map.V (M : Map α) : Nat := orbits M.vert

/-- Number of faces: orbits of the face permutation. -/
def Map.F (M : Map α) : Nat := orbits M.face

/-- Number of edges: half the number of darts. -/
def Map.E (_M : Map α) : Nat := Fintype.card α / 2

lemma Map.support_univ (M : Map α) : M.edge.support = Finset.univ := by
  ext z
  simp only [Finset.mem_univ, iff_true, Equiv.Perm.mem_support]
  exact M.edge_noFix z

/-- Connected maps satisfy the Euler bound χ = V − E + F ≤ 2: a spanning tree of
the vertex cycles (`connected_growth`) accounts for V − 1 edge transpositions,
and each of the remaining E − V + 1 transpositions can create at most one new
face orbit. -/
theorem Map.connected_euler_bound
    (hconn : ∀ (x y : α), y ∈ MulAction.orbit
        (Subgroup.closure ({M.edge, M.vert} : Set (Perm α))) x) :
    (M.V : ℤ) - M.E + M.F ≤ 2 := by
  by_cases hα : Nonempty α
  · haveI : Nonempty α := hα
    let x0 : α := Classical.arbitrary α
    obtain ⟨L0, hL0swap, hL0prod, hL0dis, hL0supp, hL0card⟩ :=
      involution_swap_factor M.edge M.edge_invol
    have hsup : M.edge.support = Finset.univ := M.support_univ
    have hcard0 : Fintype.card α = 2 * L0.length := by
      rw [hsup] at hL0card
      simpa using hL0card
    have hE : M.E = L0.length := by
      rw [Map.E, hcard0, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    obtain ⟨tree, p, htreeswap, htreedis, htnodup, hpeq, hp1, hV⟩ :=
      connected_growth M.vert M.edge M.edge_invol hconn x0
    set T : Perm α := tree.prod with hTdef
    have hτzE : ∀ z, M.edge (M.edge z) = z := by
      intro z
      have h9 : (M.edge ^ 2) z = z := by rw [M.edge_invol]; simp
      simpa [pow_two, Perm.mul_apply] using h9
    -- square of any transposition is the identity
    have h_swap_sq : ∀ (x y : α), x ≠ y → (swap x y) ^ 2 = 1 := by
      intro x y hne
      ext z
      simp only [pow_two, Perm.mul_apply]
      by_cases hzx : z = x
      · rw [hzx]; simp
      · by_cases hzy : z = y
        · rw [hzy]; simp
        · rw [swap_apply_of_ne_of_ne hzx hzy,
            swap_apply_of_ne_of_ne hzx hzy]
          simp
    -- every tree transposition is itself an involution
    have htsq : ∀ t ∈ tree, t ^ 2 = 1 := by
      intro t ht
      obtain ⟨a, ha⟩ := htreeswap t ht
      rw [ha]
      exact h_swap_sq a (M.edge a) (M.edge_noFix a).symm
    -- a permutation commutes with the product of permutations it commutes with
    have hprod_comm : ∀ (t : Perm α) (L : List (Perm α)),
        (∀ u ∈ L, Commute t u) → Commute t L.prod := by
      intro t L
      induction L with
      | nil => intro _; simp
      | cons u L ih =>
        intro hall
        rw [List.prod_cons]
        exact Commute.mul_right (hall u (by simp))
          (ih fun v hv => hall v (List.mem_cons.mpr (Or.inr hv)))
    -- the product T of pairwise disjoint tree transpositions is an involution
    have hT2 : T ^ 2 = 1 := by
      rw [hTdef]
      have hgen : ∀ (L : List (Perm α)),
          (∀ t ∈ L, ∃ a, t = swap a (M.edge a)) →
          (∀ t ∈ L, ∀ u ∈ L, t ≠ u → _root_.Disjoint t.support u.support) →
          L.Nodup → L.prod ^ 2 = 1 := by
        intro L
        induction L with
        | nil => intro _ _ _; simp
        | cons t L ih =>
          intro hs hd hn
          have htnin : t ∉ L := (List.nodup_cons.mp hn).1
          have hLn : L.Nodup := (List.nodup_cons.mp hn).2
          have hLs : ∀ u ∈ L, ∃ a, u = swap a (M.edge a) :=
            fun u hu => hs u (List.mem_cons.mpr (Or.inr hu))
          have hLd : ∀ t ∈ L, ∀ u ∈ L, t ≠ u →
              _root_.Disjoint t.support u.support :=
            fun t ht u hu hne => hd t (List.mem_cons.mpr (Or.inr ht)) u
              (List.mem_cons.mpr (Or.inr hu)) hne
          have hcin : ∀ u ∈ L, Commute t u := fun u hu =>
            have hne : t ≠ u := fun h => htnin (h.symm ▸ hu)
            have hdj : _root_.Disjoint t.support u.support :=
              hd t (by simp) u (List.mem_cons.mpr (Or.inr hu)) hne
            have hpd : Equiv.Perm.Disjoint t u :=
              disjoint_iff_disjoint_support.2 hdj
            hpd.commute
          have hct : Commute t L.prod := hprod_comm t L hcin
          have hsqt : t ^ 2 = 1 := by
            obtain ⟨a, ha⟩ := hs t (by simp)
            rw [ha]
            exact h_swap_sq a (M.edge a) (M.edge_noFix a).symm
          rw [List.prod_cons]
          have hcalc : (t * L.prod) ^ 2 = t ^ 2 * L.prod ^ 2 := by
            have he : L.prod * t = t * L.prod := hct.symm.eq
            have heq : t * L.prod * (t * L.prod) =
                t * t * (L.prod * L.prod) := by
              calc t * L.prod * (t * L.prod)
                  = t * (L.prod * (t * L.prod)) := by rw [mul_assoc]
                _ = t * ((L.prod * t) * L.prod) := by rw [mul_assoc]
                _ = t * ((t * L.prod) * L.prod) := by rw [he]
                _ = t * (t * (L.prod * L.prod)) := by rw [mul_assoc]
                _ = t * t * (L.prod * L.prod) := by rw [←mul_assoc]
            simp only [pow_two]
            exact heq
          rw [hcalc, hsqt, ih hLs hLd hLn, one_mul]
      exact hgen tree htreeswap htreedis htnodup
    -- the edge involution commutes with every tree transposition
    have hedge_comm : ∀ t ∈ tree, Commute M.edge t := by
      intro t ht
      obtain ⟨a, ha⟩ := htreeswap t ht
      set b := M.edge a with hb
      have hba : M.edge b = a := by
        simpa [hb, pow_two, Perm.mul_apply] using hτzE a
      have h : Commute M.edge (swap a b) := by
        have heq : M.edge * swap a b = swap a b * M.edge := by
          rw [mul_swap_eq_swap_mul, hb, hba, swap_comm b a]
        exact heq
      rw [ha]
      exact h
    have hcET : Commute M.edge T :=
      hprod_comm M.edge tree fun u hu => hedge_comm u hu
    -- the remaining involution τR = edge * T is again an involution
    set τR : Perm α := M.edge * T with hτRdef
    have hτR2 : τR ^ 2 = 1 := by
      rw [hτRdef]
      have he : T * M.edge = M.edge * T := hcET.symm.eq
      have hcalc : (M.edge * T) ^ 2 = M.edge ^ 2 * T ^ 2 := by
        have heq : M.edge * T * (M.edge * T) =
            M.edge * M.edge * (T * T) := by
          calc M.edge * T * (M.edge * T)
              = M.edge * (T * (M.edge * T)) := by rw [mul_assoc]
            _ = M.edge * ((T * M.edge) * T) := by rw [mul_assoc]
            _ = M.edge * ((M.edge * T) * T) := by rw [he]
            _ = M.edge * (M.edge * (T * T)) := by rw [mul_assoc]
            _ = M.edge * M.edge * (T * T) := by rw [←mul_assoc]
        simp only [pow_two]
        exact heq
      rw [hcalc, M.edge_invol, hT2, one_mul]
    -- the face permutation equals τR * p
    have hTT : T * T = (1 : Perm α) := by simpa [pow_two] using hT2
    have hfaceeq : M.face = τR * p := by
      have h1 : (M.edge * T) * (T * M.vert⁻¹) = M.edge * M.vert⁻¹ := by
        calc (M.edge * T) * (T * M.vert⁻¹)
            = M.edge * (T * (T * M.vert⁻¹)) := by rw [mul_assoc]
          _ = M.edge * ((T * T) * M.vert⁻¹) := by rw [mul_assoc]
          _ = M.edge * ((1 : Perm α) * M.vert⁻¹) := by rw [hTT]
          _ = M.edge * M.vert⁻¹ := by simp
      rw [hτRdef, hpeq]
      exact h1.symm
    -- τR fixes exactly the darts lying on tree edges
    have hOn : ∀ t ∈ tree, ∀ z ∈ t.support, T z = t z :=
      (disjoint_prod_apply tree htnodup htreedis).1
    have hOut : ∀ z, (∀ t ∈ tree, z ∉ t.support) → T z = z :=
      (disjoint_prod_apply tree htnodup htreedis).2
    have hedge_t_fix : ∀ t ∈ tree, ∀ z ∈ t.support, M.edge (t z) = z := by
      intro t ht z hz
      obtain ⟨a, ha⟩ := htreeswap t ht
      set b := M.edge a with hb
      have hne2 : a ≠ b := by
        rw [hb]
        exact (M.edge_noFix a).symm
      have hba : M.edge b = a := by
        simpa [hb, pow_two, Perm.mul_apply] using hτzE a
      have hts : t.support = {a, b} := by rw [ha]; exact support_swap hne2
      rw [hts] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with (hza | hzb)
      · have htz : t z = b := by rw [hza, ha]; simp [hb]
        rw [htz, hba, hza]
      · have htz : t z = a := by rw [hzb, ha]; simp [hb]
        rw [htz]
        exact hb.symm.trans hzb.symm
    set U : Finset α := Finset.biUnion tree.toFinset fun t => t.support with hUdef
    have hτRfix : ∀ z ∈ U, τR z = z := by
      intro z hz
      rcases Finset.mem_biUnion.mp hz with ⟨t, ht, hzt⟩
      have htl : t ∈ tree := List.mem_toFinset.mp ht
      have hTz : T z = t z := hOn t htl z hzt
      rw [hτRdef, Perm.mul_apply, hTz, hedge_t_fix t htl z hzt]
    have hτRmove : ∀ z, z ∉ U → τR z ≠ z := by
      intro z hzU
      have hall : ∀ t ∈ tree, z ∉ t.support := by
        simpa [hUdef, Finset.mem_biUnion] using hzU
      have hTz : T z = z := hOut z hall
      rw [hτRdef, Perm.mul_apply, hTz]
      exact M.edge_noFix z
    have hτRsupp : τR.support = Finset.univ \ U := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
        Equiv.Perm.mem_support]
      constructor
      · intro hne3 hzU
        exact hne3 (hτRfix z hzU)
      · intro hzU
        exact hτRmove z hzU
    have hcardU : U.card = ∑ t ∈ tree.toFinset, t.support.card := by
      rw [hUdef, Finset.card_biUnion]
      intro t ht u hu hne
      have htl : t ∈ tree := List.mem_toFinset.mp ht
      have hul : u ∈ tree := List.mem_toFinset.mp hu
      exact htreedis t htl u hul hne
    have hsupp2 : ∀ t ∈ tree, t.support.card = 2 := by
      intro t ht
      obtain ⟨a, ha⟩ := htreeswap t ht
      have hne2 : a ≠ M.edge a := (M.edge_noFix a).symm
      rw [ha, support_swap hne2]
      simp [hne2]
    have hsum : U.card = 2 * tree.length := by
      have hc : ∑ t ∈ tree.toFinset, t.support.card =
          ∑ _t ∈ tree.toFinset, (2 : Nat) :=
        Finset.sum_congr rfl fun t ht =>
          hsupp2 t (List.mem_toFinset.mp ht)
      rw [hcardU, hc, Finset.sum_const, List.toFinset_card_of_nodup htnodup]
      ring
    have hcardτR : τR.support.card = Fintype.card α - U.card := by
      rw [hτRsupp, Finset.card_sdiff]
      simp
    obtain ⟨R, hRswap, hRprod, hRdis, hRsupp, hRcard⟩ :=
      involution_swap_factor τR hτR2
    have hRtr : ∀ r ∈ R, ∃ (x y : α), x ≠ y ∧ r = swap x y := by
      intro r hr
      obtain ⟨x, hnx, hrx⟩ := hRswap r hr
      exact ⟨x, τR x, hnx, hrx⟩
    have hle : 2 * tree.length ≤ Fintype.card α := by
      have h : U.card ≤ Fintype.card α := Finset.card_le_univ U
      rw [hsum] at h
      exact h
    have hle2 : tree.length ≤ L0.length := by linarith
    have hRl : R.length = L0.length - tree.length := by
      have h1 : 2 * R.length = 2 * L0.length - 2 * tree.length := by
        rw [←hRcard, hcardτR, hsum, hcard0]
      omega
    have hFle : orbits (R.prod * p) ≤ orbits p + R.length :=
      orbits_prod_swap_le R p hRtr
    have hb : (R.length : ℤ) = (L0.length : ℤ) - tree.length := by
      have hc : (R.length : ℤ) = ↑(L0.length - tree.length) := by
        exact congrArg (fun n : Nat => (n:ℤ)) hRl
      rw [hc, Int.ofNat_sub hle2]
    have hFinal : (M.F : ℤ) ≤ 1 + (L0.length : ℤ) - tree.length := by
      calc (M.F : ℤ)
          = ↑(orbits M.face) := by rw [Map.F]
        _ = ↑(orbits (R.prod * p)) := by rw [hRprod, ←hfaceeq]
        _ ≤ (orbits p : ℤ) + R.length := Int.ofNat_le.mpr hFle
        _ = 1 + (L0.length : ℤ) - tree.length := by
            rw [hp1, hb]
            ring
    have hV' : (M.V : ℤ) = tree.length + 1 := by
      rw [Map.V]
      exact congrArg (fun n : Nat => (n:ℤ)) hV.symm
    have hE' : (M.E : ℤ) = L0.length := by
      rw [Map.E, hcard0, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    linarith
  · haveI : IsEmpty α := not_nonempty_iff.mp hα
    have h0 : Fintype.card α = 0 := Fintype.card_eq_zero
    have ho : ∀ (q : Perm α), orbits q = 0 := by
      intro q
      have hq1 : q = 1 := Subsingleton.elim q 1
      rw [orbits, hq1, cycleType_one, h0]
      simp
    have hV0 : M.V = 0 := by rw [Map.V]; exact ho M.vert
    have hF0 : M.F = 0 := by rw [Map.F]; exact ho M.face
    have hE0 : M.E = 0 := by
      rw [Map.E, h0, Nat.zero_div]
    rw [hV0, hF0, hE0]
    norm_num

/-- The combinatorial genus g = (2 − χ)/2 of a connected map is nonnegative.
Integrality of the genus (χ even for every map) is established in script 56. -/
theorem Map.connected_genus_nonneg
    (hconn : ∀ (x y : α), y ∈ MulAction.orbit
        (Subgroup.closure ({M.edge, M.vert} : Set (Perm α))) x) :
    0 ≤ (2 - ((M.V : ℚ) - M.E + M.F)) / 2 := by
  have hleχ : (M.V : ℤ) - M.E + M.F ≤ 2 := M.connected_euler_bound hconn
  have hq : ((M.V : ℚ) - M.E + M.F) ≤ 2 := by
    have hcast : (((M.V : ℤ) - M.E + M.F : ℤ) : ℚ) ≤ 2 :=
      Int.cast_le.mpr hleχ
    simpa using hcast
  linarith

end EulerBound
end SimpleGraph.SwapOrbit
