/-
72_equiv_transport_falsification.lean — downstream Lean falsification for the
Equiv/transport decision gate (scripts 70/71).

For each shortlisted asymmetric pair we verify the actual Lean facts:
  1. CStarMatrix ↔ Matrix : defeq type copy, witness `Equiv.refl`; "missing"
     Matrix lemmas apply by conversion.
  2. ConnectedComponents ↔ ZerothHomotopy : conditional Equiv from equality of
     the two quotient setoids; the Homeomorph is derivable (proved here).
  3. MaximalSpectrum ↔ PrimeSpectrum : conditional Equiv (Artinian) with
     transport lemmas; general relation is the subtype inclusion.
  4. RegularWreathProduct ↔ (Q → D) × Q : unpacking Equiv used for cardinality.
  5. PSigma ↔ Σ : generic encoding Equiv; instance transport demonstrated.
  6. WithBot ↔ WithTop : order-dual, toDual/ofDual machinery present.

Acceptance: EXIT=0 and zero-byte compile log.
-/
import Mathlib

open Set Function

/-! 1. CStarMatrix is a defeq type copy of Matrix -/
example (m n A : Type*) : CStarMatrix m n A = Matrix m n A := rfl

example (m n A : Type*) :
    CStarMatrix.ofMatrix (m := m) (n := n) (A := A) = Equiv.refl (Matrix m n A) := rfl

-- A "gap" lemma from the Matrix side applies to CStarMatrix with no transport.
example (M : CStarMatrix m n A) {m' n' : Type*} (f : m' → m) (g : n' → n) :
    M.submatrix f g = (M : Matrix m n A).submatrix f g := rfl

/-! 2. Connected components / zeroth homotopy: the Equiv is a Homeomorph where
the two quotient setoids align. -/
def ccHomeomorphZh (X : Type*) [TopologicalSpace X]
    [LocallyPathConnectedSpace X] :
    Homeomorph (ConnectedComponents X) (ZerothHomotopy X) :=
  { connectedComponentsEquivZerothHomotopy with
    continuous_toFun :=
      continuous_quot_map (r := connectedComponentSetoid X)
        (r' := pathSetoid X) (f := id)
        (fun a b h => (connectedComponent_eq_iff_joined a b).mp h) continuous_id
    continuous_invFun :=
      continuous_quot_map (r := pathSetoid X)
        (r' := connectedComponentSetoid X) (f := id)
        (fun a b h => (connectedComponent_eq_iff_joined a b).mpr h) continuous_id }

/-! 3. MaximalSpectrum: subtype representation and the conditional Artinian
equivalence with its transport lemmas. -/
example (R : Type*) [CommRing R] :
    MaximalSpectrum R ≃ { I : Ideal R // I.IsMaximal } :=
  MaximalSpectrum.equivSubtype R

example (R : Type*) [CommRing R] [IsArtinianRing R] :
    PrimeSpectrum R ≃ MaximalSpectrum R :=
  IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := R)

example (R : Type*) [CommRing R] [IsArtinianRing R] :
    MaximalSpectrum.asIdeal ∘ IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := R) =
      PrimeSpectrum.asIdeal :=
  IsArtinianRing.primeSpectrumEquivMaximalSpectrum_comp_asIdeal (R := R)

/-! 4. Regular wreath product: the unpacking Equiv and its cardinality use. -/
example (D Q : Type*) [Group D] [Group Q] :
    RegularWreathProduct D Q ≃ (Q → D) × Q :=
  RegularWreathProduct.equivProd (D := D) (Q := Q)

/-! 5. PSigma / Sigma: the generic Equiv and instance transport. -/
example {α : Sort u} {β : α → Sort v} :
    PSigma β ≃ Σ (x : PLift α), PLift (β x.down) :=
  Equiv.psigmaEquivSigmaPLift β

example (α : Type u) (β : α → Type v) [Inhabited (Σ x, β x)] :
    Inhabited (PSigma β) :=
  ⟨(Equiv.psigmaEquivSigma (β := β)).symm default⟩

/-! 6. WithBot / WithTop: the order-dual machinery. -/
example (α : Type*) : OrderDual (WithTop α) ≃ WithBot (OrderDual α) :=
  WithTop.toDual (α := α)

example (α : Type*) : OrderDual (WithBot α) ≃ WithTop (OrderDual α) :=
  WithBot.toDual (α := α)
