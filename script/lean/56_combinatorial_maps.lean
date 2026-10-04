/-
# 56 — Combinatorial maps (rotation systems) from permutations

This builds the *rotation-system* / *dart* layer that scripts 51/53/54 took as a
geometric interface and that script 55 characterized inductively.

A combinatorial map on a finite type `α` of **darts** (half-edges) is

* `edge : Perm α` — the edge involution `τ`, pairing the two darts of each edge
  (fixed-point-free, `τ² = 1`);
* `vert : Perm α` — the vertex rotation `σ`, one cycle per vertex;
* `face := τ * σ⁻¹` — the face permutation `φ`, one cycle per face.

Vertices, edges and faces are then *orbit counts* of permutations. From the
parity formula for the sign of a permutation we prove, with no topology assumed,
the purely algebraic part of the orientable Euler formula:

    V - E + F  is even  for every combinatorial map,

so an integer `genus` exists with `V - E + F = 2 - 2 * genus`. Script 55 proves
`V - E + F = 2` for the inductively planar class; this file shows that for *every*
map the characteristic is `2` modulo `2`, and it exhibits the two genus-zero
seeds (the single link and the single loop) with `V - E + F = 2`.

The remaining topological content — connectedness forcing `genus ≥ 0` (`χ ≤ 2`)
and the genus-zero realization theorem — is stated in the design note and is not
asserted here.

Everything is kernel-verified: no `sorry`, no warnings.
-/

import Mathlib

open Equiv

namespace SimpleGraph.CombiMap

variable (α : Type*) [Fintype α] [DecidableEq α]

/-- Number of cycles (orbits) of a permutation, counting fixed points as
one-element cycles. `cycleType` lists the lengths of the nontrivial cycles;
the remaining `card α - sum cycleType` points are fixed points. -/
def orbits (p : Perm α) : ℕ :=
  Multiset.card p.cycleType + (Fintype.card α - p.cycleType.sum)

private lemma multiset_two_le_sum :
    ∀ (m : Multiset ℕ), (∀ x ∈ m, 2 ≤ x) → 2 * Multiset.card m ≤ m.sum := by
  intro m
  induction m using Multiset.induction_on with
  | empty => intro _; norm_num
  | cons a m ih =>
    intro h
    have ha : 2 ≤ a := h a (Multiset.mem_cons_self a m)
    have hm : ∀ x ∈ m, 2 ≤ x := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.card_cons, Multiset.sum_cons]
    linarith [ih hm]

private lemma multiset_sum_eq_two_card :
    ∀ (m : Multiset ℕ), (∀ x ∈ m, x = 2) → m.sum = 2 * Multiset.card m := by
  intro m
  induction m using Multiset.induction_on with
  | empty => intro _; rfl
  | cons a m ih =>
    intro h
    have ha : a = 2 := h a (Multiset.mem_cons_self a m)
    have hm : ∀ x ∈ m, x = 2 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.sum_cons, Multiset.card_cons, ha, ih hm]; ring

lemma orbits_le_card (p : Perm α) : orbits α p ≤ Fintype.card α := by
  have h2 : ∀ x ∈ p.cycleType, 2 ≤ x := fun _ hx => Perm.two_le_of_mem_cycleType hx
  have hsc : 2 * Multiset.card p.cycleType ≤ p.cycleType.sum :=
    multiset_two_le_sum p.cycleType h2
  have hsn : p.cycleType.sum ≤ Fintype.card α := Perm.sum_cycleType_le p
  simp [orbits]; omega

lemma orbits_one : orbits α (1 : Perm α) = Fintype.card α := by
  rw [orbits, Perm.cycleType_one]; simp

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
  simp; omega

private lemma neg_one_pow_mod_two (n : ℕ) :
    (-1 : ℤˣ)^n = if n % 2 = 0 then (1 : ℤˣ) else -1 := by
  by_cases h : n % 2 = 0
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    simp [pow_mul, pow_two]
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    simp [pow_add, pow_mul, pow_two]

private lemma neg_one_pow_eq_iff {a b : ℕ} :
    (-1 : ℤˣ)^a = (-1 : ℤˣ)^b ↔ a % 2 = b % 2 := by
  constructor
  · intro h
    rw [neg_one_pow_mod_two a, neg_one_pow_mod_two b] at h
    by_cases ha : a % 2 = 0
    · by_cases hb : b % 2 = 0
      · exact ha.trans hb.symm
      · simp only [ha, hb] at h
        exact False.elim ((by decide : (1 : ℤˣ) ≠ -1) h)
    · by_cases hb : b % 2 = 0
      · simp only [ha, hb] at h
        exact False.elim ((by decide : (-1 : ℤˣ) ≠ 1) h)
      · have ha1 : a % 2 = 1 := by omega
        have hb1 : b % 2 = 1 := by omega
        exact ha1.trans hb1.symm
  · intro h
    rw [neg_one_pow_mod_two a, neg_one_pow_mod_two b, h]

/-- `sign p = (-1)^(card α - orbits p)`, up to parity of the exponent. -/
lemma sign_exponent_parity (p : Perm α) :
    (p.cycleType.sum + Multiset.card p.cycleType) % 2 =
      (Fintype.card α - orbits α p) % 2 := by
  set s := p.cycleType.sum with hs
  set c := Multiset.card p.cycleType with hc
  have h2 : ∀ x ∈ p.cycleType, 2 ≤ x := fun _ hx => Perm.two_le_of_mem_cycleType hx
  have hsc : 2 * c ≤ s := multiset_two_le_sum p.cycleType h2
  have hcs : c ≤ s := by omega
  have hsn : s ≤ Fintype.card α := Perm.sum_cycleType_le p
  have ho : orbits α p = c + (Fintype.card α - s) := by simp [orbits, hc, hs]
  rw [ho]
  have hsub : Fintype.card α - (c + (Fintype.card α - s)) = s - c := by omega
  rw [hsub]
  have heq : s + c = (s - c) + 2 * c := by omega
  rw [heq]
  simp [Nat.add_mod]

/-- A combinatorial (orientable) map: darts with a fixed-point-free edge
involution `edge` and a vertex rotation `vert`. -/
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

/-- Number of vertices = cycles of σ. -/
def vertices : ℕ := orbits α M.vert

/-- Number of edges = cycles of τ (each a 2-cycle). -/
def edges : ℕ := orbits α M.edge

/-- Number of faces = cycles of φ. -/
def faces : ℕ := orbits α M.face

/-- Every nontrivial cycle of an involution has length 2. -/
lemma cycle_length_two {n : ℕ} (hn : n ∈ M.edge.cycleType) : n = 2 := by
  have hdiv : n ∣ orderOf M.edge := Perm.dvd_of_mem_cycleType hn
  have hord : orderOf M.edge ∣ 2 := orderOf_dvd_of_pow_eq_one M.edge_invol
  have h2 : n ∣ 2 := dvd_trans hdiv hord
  have hge : 2 ≤ n := Perm.two_le_of_mem_cycleType hn
  have hle : n ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  omega

/-- The edge involution moves every dart, hence its support is everything. -/
lemma edge_support_univ : M.edge.support = Finset.univ := by
  ext x
  simp only [Perm.mem_support, Finset.mem_univ]
  exact ⟨fun _ => trivial, fun _ => M.edge_noFix x⟩

/-- `2 · E = #darts`; in particular the number of darts is even and
`E = #darts / 2`. -/
lemma two_edges_eq_card : 2 * M.edges = Fintype.card α := by
  set c := Multiset.card M.edge.cycleType with hc
  have hall : ∀ x ∈ M.edge.cycleType, x = 2 := fun _ hn => cycle_length_two α M hn
  have hsc : M.edge.cycleType.sum = 2 * c :=
    multiset_sum_eq_two_card M.edge.cycleType hall
  have hsN : M.edge.cycleType.sum = Fintype.card α := by
    rw [Perm.sum_cycleType, M.edge_support_univ]; simp
  have h2c : 2 * c = Fintype.card α := by linarith
  have hE : M.edges = c := by simp [edges, orbits, hsN, hc]
  rw [hE]
  exact h2c

lemma edges_eq_half_card : M.edges = Fintype.card α / 2 := by
  have h := M.two_edges_eq_card
  omega

/-- The orientable Euler characteristic `V - E + F` is even. -/
theorem chi_even : Even ((M.vertices : ℤ) - M.edges + M.faces) := by
  set N := Fintype.card α with hN
  set V := M.vertices with hV
  set E := M.edges with hE
  set F := M.faces with hF
  set χ : ℤ := (V : ℤ) - E + F with hχ
  have hVN : V ≤ N := orbits_le_card α M.vert
  have hFN : F ≤ N := orbits_le_card α M.face
  have hsign : Perm.sign M.face = Perm.sign M.edge * Perm.sign M.vert := by
    rw [face, Perm.sign_mul, Perm.sign_inv]
  have hpv : (M.vert.cycleType.sum + Multiset.card M.vert.cycleType) % 2 = (N - V) % 2 :=
    sign_exponent_parity α M.vert
  have hpf : (M.face.cycleType.sum + Multiset.card M.face.cycleType) % 2 = (N - F) % 2 :=
    sign_exponent_parity α M.face
  have hv : Perm.sign M.vert = (-1 : ℤˣ)^(N - V) := by
    rw [Perm.sign_of_cycleType]
    exact neg_one_pow_eq_iff.mpr hpv
  have hf : Perm.sign M.face = (-1 : ℤˣ)^(N - F) := by
    rw [Perm.sign_of_cycleType]
    exact neg_one_pow_eq_iff.mpr hpf
  have hsN : M.edge.cycleType.sum = Fintype.card α := by
    rw [Perm.sum_cycleType, M.edge_support_univ]; simp
  have hcE : Multiset.card M.edge.cycleType = E := by simp [edges, orbits, hsN, hE]
  have h2E : 2 * E = Fintype.card α := M.two_edges_eq_card
  have hpe : (M.edge.cycleType.sum + Multiset.card M.edge.cycleType) % 2 = E % 2 := by
    rw [hsN, hcE]
    have h2E' : Fintype.card α = 2 * E := h2E.symm
    rw [h2E']
    simp [Nat.add_mod]
  have he : Perm.sign M.edge = (-1 : ℤˣ)^E := by
    rw [Perm.sign_of_cycleType]
    exact neg_one_pow_eq_iff.mpr hpe
  rw [hf, he, hv] at hsign
  have hmul : (-1 : ℤˣ)^E * (-1 : ℤˣ)^(N - V) = (-1 : ℤˣ)^(E + (N - V)) := by
    rw [← pow_add]
  rw [hmul] at hsign
  have hpar : (N - F) % 2 = (E + (N - V)) % 2 := neg_one_pow_eq_iff.mp hsign
  have h3 : ((N - F : ℕ) : ℤ) % 2 = ((E + (N - V) : ℕ) : ℤ) % 2 := by
    exact_mod_cast hpar
  have h1 : ((N - F : ℕ) : ℤ) = (N : ℤ) - F := Int.ofNat_sub hFN
  have h2 : ((E + (N - V) : ℕ) : ℤ) = (E : ℤ) + N - V := by
    rw [Nat.cast_add, Int.ofNat_sub hVN]; ring
  rw [h1, h2] at h3
  have hdiff : ((N : ℤ) - F) - ((E : ℤ) + N - V) = χ - 2 * F := by
    simp only [hχ]; ring
  have h4 : (((N : ℤ) - F) - ((E : ℤ) + N - V)) % 2 = 0 := by
    rw [Int.sub_emod, h3]; simp
  rw [hdiff] at h4
  have hgoal : χ % 2 = 0 := by omega
  rw [Int.even_iff]
  exact hgoal

/-- Euler characteristic `χ = V - E + F`. -/
def chi : ℤ := (M.vertices : ℤ) - M.edges + M.faces

/-- Combinatorial genus `g = (2 - χ) / 2`; an integer because `χ` is even. -/
noncomputable def genus : ℤ := (2 - M.chi) / 2

theorem chi_eq_two_minus_two_genus : M.chi = 2 - 2 * M.genus := by
  rcases M.chi_even with ⟨k, hk⟩
  have hkk : M.chi = k + k := by simpa [chi] using hk
  have hchi : M.chi = 2 * k := by
    rw [hkk]; ring
  have hq : M.genus = 1 - k := by
    rw [genus, hchi]
    have heq : (2 : ℤ) - 2 * k = 2 * (1 - k) := by ring
    rw [heq]
    omega
  calc
    M.chi = 2 * k := hchi
    _ = 2 - 2 * (1 - k) := by ring
    _ = 2 - 2 * M.genus := by rw [hq]

end Map

private def s2 : Perm (Fin 2) := swap (0 : Fin 2) 1
private theorem hne2 : (0 : Fin 2) ≠ 1 := by decide

/-- The one-edge **link**: two vertices, one edge, one face (`χ = 2`). -/
def linkMap : Map (Fin 2) where
  edge := s2
  edge_invol := by simp [s2, pow_two]
  edge_noFix := by
    intro x
    fin_cases x <;> simp [s2]
  vert := 1

/-- The one-edge **loop**: one vertex, one loop edge, two faces (`χ = 2`). -/
def loopMap : Map (Fin 2) where
  edge := s2
  edge_invol := by simp [s2, pow_two]
  edge_noFix := by
    intro x
    fin_cases x <;> simp [s2]
  vert := s2

example : linkMap.vertices = 2 := by
  show orbits (Fin 2) (1 : Perm (Fin 2)) = 2
  exact orbits_one (Fin 2)

example : linkMap.edges = 1 := by
  show orbits (Fin 2) s2 = 1
  have h := orbits_swap (Fin 2) hne2
  simpa [s2] using h

example : linkMap.faces = 1 := by
  show orbits (Fin 2) (s2 * (1 : Perm (Fin 2))⁻¹) = 1
  have h := orbits_swap (Fin 2) hne2
  simpa [s2] using h

example : linkMap.chi = 2 := by
  have hv : linkMap.vertices = 2 := orbits_one (Fin 2)
  have he : linkMap.edges = 1 := by
    show orbits (Fin 2) s2 = 1
    have h := orbits_swap (Fin 2) hne2
    simpa [s2] using h
  have hf : linkMap.faces = 1 := by
    show orbits (Fin 2) (s2 * (1 : Perm (Fin 2))⁻¹) = 1
    have h := orbits_swap (Fin 2) hne2
    simpa [s2] using h
  simp only [Map.chi, hv, he, hf]; norm_num

example : loopMap.vertices = 1 := by
  show orbits (Fin 2) s2 = 1
  have h := orbits_swap (Fin 2) hne2
  simpa [s2] using h

example : loopMap.edges = 1 := by
  show orbits (Fin 2) s2 = 1
  have h := orbits_swap (Fin 2) hne2
  simpa [s2] using h

example : loopMap.faces = 2 := by
  show orbits (Fin 2) (s2 * s2⁻¹) = 2
  have hi : s2 * s2⁻¹ = (1 : Perm (Fin 2)) := by simp
  rw [hi]
  exact orbits_one (Fin 2)

example : loopMap.chi = 2 := by
  have hv : loopMap.vertices = 1 := by
    show orbits (Fin 2) s2 = 1
    have h := orbits_swap (Fin 2) hne2
    simpa [s2] using h
  have he : loopMap.edges = 1 := by
    show orbits (Fin 2) s2 = 1
    have h := orbits_swap (Fin 2) hne2
    simpa [s2] using h
  have hf : loopMap.faces = 2 := by
    show orbits (Fin 2) (s2 * s2⁻¹) = 2
    have hi : s2 * s2⁻¹ = (1 : Perm (Fin 2)) := by simp
    rw [hi]
    exact orbits_one (Fin 2)
  simp only [Map.chi, hv, he, hf]; norm_num

end SimpleGraph.CombiMap
