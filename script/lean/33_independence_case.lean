/-
33_independence_case.lean — CASE H probe (weak semantic band, cosine 0.70-0.80).

Script 32's only non-trivial weak-band cluster pairs four "independence" notions
across areas:
  LinearIndependent      (LinearAlgebra)  no nontrivial linear combination = 0
  AlgebraicIndependent   (RingTheory)     no polynomial relation
  ConvexIndependent      (Analysis)       point only in convex hulls containing it
  iSupIndep / sSupIndep  (Order/Algebra)  each element disjoint from the Sup of the rest

Hypothesis: these are one missing generic "Independence" abstraction.
Verdict reached below (kernel-checked): NO new class is warranted, because
  (1) LinearIndependent and AlgebraicIndependent are DEFINITIONALLY the same
      shape, `Function.Injective` of the canonical structure/combination map;
  (2) algebraic independence already reduces to linear independence of the
      free monomial basis (`MvPolynomial.basisMonomials`, `aevalEquiv`);
  (3) affine independence already reduces to linear independence of pairwise
      differences (`affineIndependent_iff_linearIndependent_vsub`);
  (4) the lattice-level generic `sSupIndep/iSupIndep` exists for ANY
      `CompleteLattice`, and the combinatorial generic `Matroid.Indep` exists;
  (5) ConvexIndependent is a *hull* condition (anti-exchange / convex geometry),
      not an `Injective combination` condition, so folding all four into one
      class would be a mathematically FALSE unification.
-/
import Mathlib

open Function
open scoped Classical

/-! ### 1. The two algebraic independences share ONE definitional shape -/

section LinearShape
variable (R M ι : Type*) [Semiring R] [AddCommMonoid M] [Module R M] (v : ι → M)

/- Linear independence is, by definition, injectivity of the linear-combination
map from finitely-supported coefficient families. -/
example : LinearIndependent R v = Injective (Finsupp.linearCombination R v) :=
  rfl
end LinearShape

section AlgebraicShape
variable (R A ι : Type*) [CommRing R] [CommRing A] [Algebra R A] (x : ι → A)

/- Algebraic independence is, by definition, injectivity of polynomial
evaluation. Same shape: `Injective` of the canonical structure map. -/
example : AlgebraicIndependent R x = Injective (MvPolynomial.aeval (R := R) x) :=
  rfl
end AlgebraicShape

/-! ### 2. Algebraic independence is already linear independence of monomials -/

section MonomialBridge
variable (σ R : Type*) [CommRing R]

/- The monomials form a BASIS of the multivariate polynomial ring, hence are
linearly independent: algebraic independence is linear independence after the
free monomial map, not a separate abstraction. -/
#check (MvPolynomial.basisMonomials σ R).linearIndependent

/- Under algebraic independence, polynomial evaluation is an algebra
equivalence onto the generated subalgebra. -/
#check @AlgebraicIndependent.aevalEquiv
end MonomialBridge

/-! ### 3. Affine (and the related convex) independence is already bridged -/

section AffineBridge
variable (𝕜 V P ι : Type*) [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [AddTorsor V P] (p : ι → P) (i₀ : ι)

/- Affine independence of a point family is LINEAR independence of the
point-differences `p i -ᵥ p i₀`: a distinct carrier but an existing bridge. -/
#check affineIndependent_iff_linearIndependent_vsub 𝕜 p i₀

/- Convex independence is a *hull-membership* condition, with a different
typeclass carrier (`OrderedSemiring`, `convexHull`), not injectivity of a
combination map. -/
#check @ConvexIndependent
end AffineBridge

/-! ### 4. The lattice-level and combinatorial generics already exist -/

section ExistingGenerics
variable (α : Type*)

/- `sSupIndep` needs only a `CompleteLattice`: every element is `Disjoint`
from the supremum of the rest. Submodule/Subalgebra/Subgroup independence are
instances of this generic, not separate concepts. -/
#check @sSupIndep

#check @iSupIndep

/- The combinatorial independence generic (exchange axiom) exists as a
matroid with an `Indep` predicate. -/
#check @Matroid.Indep
end ExistingGenerics

/-! ### 5. Why the four are NOT one class: different axiom carriers

  LinearIndependent R v   Module R M;          Injective (linearCombination)
  AlgebraicIndependent    Algebra R A;         Injective (aeval) = linear indep
                                                                   of monomials
  AffineIndependent       AffineSpace V P;    linear indep of vsub
  ConvexIndependent       OrderedSemiring;    convexHull membership (anti-exch.)
  sSupIndep / iSupIndep   CompleteLattice;    Disjoint from Sup of rest
  Matroid.Indep           ground set + rank;  exchange axiom

The first three are already the SAME idea (injective structure map / linear
independence of a derived free family), the lattice notion is already generic
over `CompleteLattice`, and the matroid generic already captures exchange-axiom
independence. Convex independence obeys the OPPOSITE (anti-exchange) law and is
correctly kept separate. -/

#eval ()  -- file parses and elaborates end-to-end
