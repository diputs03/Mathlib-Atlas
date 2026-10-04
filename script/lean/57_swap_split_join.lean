/-
# 57 — The transposition split/join orbit lemma

Script 56 proved that the Euler characteristic of every combinatorial map is even
and that an integer genus exists. The missing combinatorial primitive needed for
`genus ≥ 0` (`χ ≤ 2`) on a connected map is the classical fact that multiplying a
permutation by a transposition changes its number of cycles (orbits) by exactly
one: it **splits** one cycle into two, or **joins** two cycles into one.

Mathlib provides the ingredients — `IsCycle.swap_mul` (an adjacent cut turns a
cycle into a cycle on the support minus the cut vertex, which becomes fixed) and
`support_swap_mul_eq` — but not the orbit-count statement itself. This file proves,
kernel-verified, the two clean adjacent/fixed-point forms of that lemma:

* `orbits_adjacent_split`: if `f` is a single cycle and `f x ≠ x`, then
  `g = swap x (f x) * f` fixes `x`, is otherwise one cycle, and
  `orbits g = orbits f + 1` (a cycle is split off at the vertex `x`);
* `orbits_fixed_join`: the exact inverse — if a cycle `f` fixes a point `z` and
  `x` lies on the cycle, then `h = swap z x * f` absorbs `z` into the cycle and
  `orbits h = orbits f - 1` (a fixed point is joined onto the cycle).

These are the insertion/deletion primitives for rotation systems: every edge
insertion in a combinatorial map is one such split or join of the vertex/face
permutations, which is what makes an inductive proof of `χ ≤ 2` possible.

The fully general forms (cut between two arbitrary points of the same cycle;
joining two arbitrary nontrivial cycles) follow by the same `f^i x` enumeration
used in `orbits_fixed_join` and are noted, not needed here.

No `sorry`, no warnings.
-/

import Mathlib

open Equiv

namespace SimpleGraph.OrbitSplit

variable (α : Type*) [Fintype α] [DecidableEq α]

/-- Number of cycles (orbits) of a permutation, counting fixed points as
one-element cycles. -/
def orbits (p : Perm α) : ℕ :=
  Multiset.card p.cycleType + (Fintype.card α - p.cycleType.sum)

lemma orbits_one : orbits α (1 : Perm α) = Fintype.card α := by
  rw [orbits, Perm.cycleType_one]; simp

/-- A single cycle on `n` points has `Fintype.card α - n + 1` orbits: the one
nontrivial cycle plus every point outside its support as a fixed point. -/
lemma orbits_cycle {f : Perm α} (hf : f.IsCycle) :
    orbits α f = Fintype.card α - f.support.card + 1 := by
  have hle : f.support.card ≤ Fintype.card α := Finset.card_le_univ (s := f.support)
  rw [orbits, hf.cycleType]
  simp
  omega

lemma orbits_swap {a b : α} (hne : a ≠ b) :
    orbits α (swap a b) = Fintype.card α - 1 := by
  have hcyc : (swap a b).IsCycle := Perm.isCycle_swap hne
  have hct : (swap a b).cycleType = {2} := by
    rw [hcyc.cycleType, Perm.support_swap hne]
    simp [hne]
  have h2le : 2 ≤ Fintype.card α := by
    have hle : ({a, b} : Finset α).card ≤ Fintype.card α :=
      Finset.card_le_univ (s := ({a, b} : Finset α))
    simpa [Finset.card_pair hne] using hle
  rw [orbits, hct]
  simp
  omega

/-- **Split.** Cutting a cycle `f` just after `x` (multiplying by
`swap x (f x)`) makes `x` a fixed point and leaves one cycle on the remaining
points; the number of orbits increases by exactly one. -/
theorem orbits_adjacent_split {f : Perm α} (hf : f.IsCycle) {x : α}
    (hx : f x ≠ x) :
    orbits α (swap x (f x) * f) = orbits α f + 1 := by
  have h2s : 2 ≤ f.support.card := hf.two_le_card_support
  have hnle : f.support.card ≤ Fintype.card α := Finset.card_le_univ (s := f.support)
  have h2le : 2 ≤ Fintype.card α := by linarith
  by_cases h2 : f (f x) = x
  · -- The cycle has length 2: f is itself the transposition, and the cut is 1.
    have hfs : f = swap x (f x) :=
      hf.eq_swap_of_apply_apply_eq_self hx h2
    have hg : swap x (f x) * f = 1 := by
      rw [hfs]; simp
    rw [hg, orbits_one]
    have hos : orbits α f = Fintype.card α - 1 := by
      rw [hfs]
      exact orbits_swap α hx.symm
    rw [hos]; omega
  · -- The cycle has length ≥ 3.
    set g : Perm α := swap x (f x) * f with hgdef
    have hg : g.IsCycle := hf.swap_mul hx h2
    have hsg : g.support = f.support \ {x} :=
      Perm.support_swap_mul_eq f x h2
    have hxmem : x ∈ f.support := Perm.mem_support.mpr hx
    have hcard : g.support.card = f.support.card - 1 := by
      rw [hsg, Finset.card_sdiff]
      simp [hxmem]
    rw [orbits_cycle α hg, orbits_cycle α hf, hcard]
    omega

/-- A positive power of a moved point stays in the support. -/
private lemma pow_mem_support {f : Perm α} {x : α} (hx : f x ≠ x) (j : ℕ) :
    (f ^ j) x ∈ f.support := by
  have himg : ∀ y ∈ f.support, f y ∈ f.support := by
    intro y hy
    rw [Perm.mem_support] at hy ⊢
    exact fun h => hy (f.injective h)
  induction j with
  | zero => exact Perm.mem_support.mpr hx
  | succ j ih =>
    have h5 := himg ((f ^ j) x) ih
    simpa [pow_succ, Perm.mul_apply] using h5

/-- **Join.** If a cycle `f` fixes `z` and `x` is on the cycle, then
`swap z x * f` is one cycle running through `z` and the whole support of `f`; the
number of orbits decreases by exactly one. -/
theorem orbits_fixed_join {f : Perm α} (hf : f.IsCycle) {z x : α}
    (hfz : f z = z) (hx : f x ≠ x) :
    orbits α (swap z x * f) = orbits α f - 1 := by
  set h : Perm α := swap z x * f with hhdef
  set n : ℕ := orderOf f with hndef
  have hn : n = f.support.card := hf.orderOf
  have hnpos : 0 < n := orderOf_pos f
  have hxz : x ≠ z := by
    intro heq
    rw [heq] at hx
    exact hx hfz
  have hz_notin : z ∉ f.support := by
    simpa [Perm.mem_support] using hfz
  -- h sends z to x.
  have h_hz : h z = x := by
    rw [hhdef, Perm.mul_apply, hfz]
    simp
  -- Minimal period of x along the cycle is n.
  have hper : ∀ j : ℕ, 0 < j → j < n → (f ^ j) x ≠ x := by
    intro j hj0 hjl heq
    have h1 : f ^ j = 1 := (hf.pow_eq_one_iff' hx).mpr heq
    have h2 : n ∣ j := orderOf_dvd_of_pow_eq_one h1
    have h3 : n ≤ j := Nat.le_of_dvd hj0 h2
    linarith
  -- (h ^ (j+1)) z = (f ^ j) x for j < n.
  have henum : ∀ j : ℕ, j < n → (h ^ (j + 1)) z = (f ^ j) x := by
    intro j hj
    induction j with
    | zero =>
      have hz1 : (h ^ 1) z = x := by
        rw [pow_one]
        exact h_hz
      rw [hz1, pow_zero, Perm.one_apply]
    | succ j ih =>
      have hlt : j < n := by omega
      have ih' := ih hlt
      have hpow : h ^ (j + 2) = h * h ^ (j + 1) := by rw [pow_succ']
      have hstep : (h ^ (j + 2)) z = h ((h ^ (j + 1)) z) := by
        rw [hpow, Perm.mul_apply]
      rw [hstep, ih']
      have hj1 : 0 < j + 1 := by omega
      have hjn : j + 1 < n := hj
      have hne1 : (f ^ (j + 1)) x ≠ x := hper (j + 1) hj1 hjn
      have hne2 : (f ^ (j + 1)) x ≠ z := by
        intro heq
        exact hz_notin (heq ▸ pow_mem_support α hx (j + 1))
      have hfp : f ((f ^ j) x) = (f ^ (j + 1)) x := by
        have hq : f ^ (j + 1) = f * f ^ j := by rw [pow_succ']
        rw [hq, Perm.mul_apply]
      rw [hhdef, Perm.mul_apply, hfp,
        Equiv.swap_apply_of_ne_of_ne hne2 hne1]
  -- The support of h is {z} ∪ support f.
  have hsupp : h.support = insert z f.support := by
    ext y
    simp only [Perm.mem_support, Finset.mem_insert]
    constructor
    · intro hy
      by_cases hyz : y = z
      · exact Or.inl hyz
      · have hfy : f y ≠ y := by
          by_contra hfy
          have h_yne_x : y ≠ x := by
            intro r
            rw [r] at hfy
            exact hx hfy
          have hhy : h y = y := by
            rw [hhdef, Perm.mul_apply, hfy, Equiv.swap_apply_of_ne_of_ne hyz h_yne_x]
          exact hy hhy
        exact Or.inr hfy
    · rintro (rfl | hy)
      · rw [h_hz]; exact hxz
      · have h_yne_z : y ≠ z := by
          intro r
          rw [r] at hy
          exact hy hfz
        by_contra h_eq
        rw [hhdef, Perm.mul_apply] at h_eq
        by_cases c1 : f y = z
        · have hyz : y = z := f.injective (by rw [c1, hfz])
          exact h_yne_z hyz
        · by_cases c2 : f y = x
          · rw [c2, Equiv.swap_apply_right] at h_eq
            exact h_yne_z h_eq.symm
          · rw [Equiv.swap_apply_of_ne_of_ne c1 c2] at h_eq
            exact hy h_eq
  have hcard : h.support.card = f.support.card + 1 := by
    rw [hsupp, Finset.card_insert_of_notMem hz_notin]
  -- h is a single cycle through z.
  have hhcycle : h.IsCycle := by
    refine ⟨z, ?_, ?_⟩
    · rw [h_hz]; exact hxz
    · intro y hy
      have hmem : y = z ∨ y ∈ f.support := by
        rw [← Perm.mem_support, hsupp, Finset.mem_insert] at hy
        exact hy
      rcases hmem with (rfl | hym)
      · exact ⟨0, by simp⟩
      · have hy' : f y ≠ y := Perm.mem_support.mp hym
        have hsc : Perm.SameCycle f x y := by
          obtain ⟨i, hi⟩ := hf.exists_pow_eq hx hy'
          exact ⟨i, hi⟩
        obtain ⟨j, hjl, hfj⟩ := hsc.exists_pow_eq'
        refine ⟨(j + 1 : ℤ), ?_⟩
        have hnat : (h ^ (j + 1)) z = (f ^ j) x := henum j hjl
        have hcast : ((j + 1 : ℤ)) = ↑(j + 1) := by simp
        rw [hcast, zpow_natCast, hnat, hfj]
  have hnle : f.support.card ≤ Fintype.card α := Finset.card_le_univ (s := f.support)
  have hn1 : f.support.card + 1 ≤ Fintype.card α := by
    have hci : (insert z f.support).card = f.support.card + 1 :=
      Finset.card_insert_of_notMem hz_notin
    rw [← hci]
    exact Finset.card_le_univ (s := insert z f.support)
  rw [orbits_cycle α hhcycle, orbits_cycle α hf, hcard]
  omega

end SimpleGraph.OrbitSplit
