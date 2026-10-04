/-
# Case study D — `shared_head_analogy`: the cross-area `Equivalence` family.

Community #10 (script 18/19/21) gathers 26 declarations across 10 areas whose
conclusion head is `Equivalence`: homotopy of continuous maps / paths / loops,
permutation same-cycle, list rotation, graph reachability, category zigzag,
subgroup commensurability, Brauer equivalence, sequential computations, …

Reading the proofs shows they are ALL the same trivial three-field bundle of
each relation's OWN refl/symm/trans lemmas:

    ContinuousMap.Homotopic.equivalence = ⟨refl, symm, trans⟩
    Equiv.Perm.SameCycle.equivalence    = ⟨SameCycle.refl, .symm, .trans⟩
    List.IsRotated.eqv                  = Equivalence.mk refl symm trans
    SimpleGraph.reachable_is_equivalence = Equivalence.mk Reachable.refl ...
    IsBrauerEquivalent.is_eqv           = where refl:=refl symm:=symm trans:=trans
    CategoryTheory.zigzag_equivalence   = refl_of/symm_of/trans_of ReflTransGen

This file kernel-checks, downstream (Mathlib untouched):
  1. the generic constructors already exist (`Equivalence.mk`,
     `Relation.EqvGen.is_equivalence`, `Relation.map_equivalence`);
  2. representatives from six different areas all have type `Equivalence R`;
  3. a witness can be rebuilt with nothing but the relation's refl/symm/trans
     through the generic constructor — there is no extra shared lemma to find.

Conclusion (see notes\22_equivalence_witness_case.md): the cross-area
"repetition" is irreducible multiplicity of an existing abstract concept. Each
relation must prove its own refl/symm/trans; the only common step — bundling
them — is already generic. This is why shared_head_analogy is correctly ranked
below structure_lifted_per_carrier as a refactoring target.
-/

import Mathlib

/- 1. Generic constructors. -/
#check @Equivalence.mk
#check @Relation.map_equivalence

example {α : Type*} (r : α → α → Prop) : Equivalence (Relation.EqvGen r) :=
  Relation.EqvGen.is_equivalence r

/- 2. Cross-area witnesses, all of the shape `Equivalence R`. -/
#check ContinuousMap.Homotopic.equivalence
#check Path.Homotopic.equivalence
#check Equiv.Perm.SameCycle.equivalence
#check List.IsRotated.eqv
#check SimpleGraph.reachable_is_equivalence
#check CategoryTheory.zigzag_equivalence

/- 3. Rebuild a witness from only the relation's own refl/symm/trans: the
generic bundle adds no mathematical content. -/
example {α : Type*} : Equivalence (@List.IsRotated α) :=
  Equivalence.mk List.IsRotated.refl List.IsRotated.symm List.IsRotated.trans

/- The same generic bundle for graph reachability. -/
example {V : Type*} (G : SimpleGraph V) : Equivalence G.Reachable :=
  Equivalence.mk (@SimpleGraph.Reachable.refl V G)
    (@SimpleGraph.Reachable.symm V G) (@SimpleGraph.Reachable.trans V G)

/- And for permutation same-cycle. -/
example {α : Type*} (f : Equiv.Perm α) : Equivalence (Equiv.Perm.SameCycle f) :=
  Equivalence.mk (Equiv.Perm.SameCycle.refl f)
    Equiv.Perm.SameCycle.symm Equiv.Perm.SameCycle.trans
