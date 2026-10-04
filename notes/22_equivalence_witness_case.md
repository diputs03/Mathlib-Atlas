# Case study D — the cross-area `Equivalence` family (shared_head_analogy)

## What the Atlas flagged

After scripts 19/21, the widest `shared_head_analogy` community is **#10
`Equivalence`**: 26 declarations across **10 areas** (Topology, GroupTheory,
Data, Logic, CategoryTheory, Combinatorics, AlgebraicGeometry, Algebra, Order,
…). Every member concludes `Equivalence R` for a different relation:

| area | relation | witness |
|---|---|---|
| Topology | homotopy of continuous maps | `ContinuousMap.Homotopic.equivalence` |
| Topology | path homotopy | `Path.Homotopic.equivalence` |
| Topology | loop homotopy | `GenLoop.Homotopic.equiv`, `TopPair.Homotopic.equivalence` |
| GroupTheory | same cycle of a permutation | `Equiv.Perm.SameCycle.equivalence` |
| GroupTheory | subgroup commensurability | `Subgroup.Commensurable.equivalence`, `AddSubgroup.…` |
| Data | list rotation | `List.IsRotated.eqv` |
| Combinatorics | graph reachability | `SimpleGraph.reachable_is_equivalence` |
| CategoryTheory | zigzag connectedness | `CategoryTheory.zigzag_equivalence` |
| Algebra | Brauer equivalence | `IsBrauerEquivalent.is_eqv` |
| Data/Logic | computation / weak-seq equiv, lift relations | `Computation.Equiv.equivalence`, `Stream'.WSeq.*`, `Computation.LiftRel.equiv` |

## What the source shows: one uniform trivial bundle

Every witness packages that relation's *own* already-proven `refl / symm /
trans` lemmas and nothing else:

```
ContinuousMap.Homotopic.equivalence = ⟨refl, by apply symm, by apply trans⟩
Equiv.Perm.SameCycle.equivalence    = ⟨SameCycle.refl f, .symm, .trans⟩
List.IsRotated.eqv                  = Equivalence.mk IsRotated.refl .symm .trans
SimpleGraph.reachable_is_equivalence = Equivalence.mk (@Reachable.refl _ G) …
IsBrauerEquivalent.is_eqv           = where refl := refl; symm := symm; trans := trans
CategoryTheory.zigzag_equivalence   = where refl := refl_of (ReflTransGen _)
                                                symm := symm_of (ReflTransGen _)
                                                trans := trans_of (ReflTransGen _)
```

Generic constructors already exist for the non-direct cases:
`Equivalence.mk` (bundle three lemmas), `Relation.EqvGen.is_equivalence`
(equivalence closure), `Relation.map_equivalence` / `preimage_equivalence`
(push/pull along functions), and `Relation.ReflTransGen.{refl_of,symm_of,
trans_of}` used by the zigzag witness.

## Kernel verification (`script/lean/22_equivalence_witness.lean`)

Compiled downstream, **exit 0, no errors/warnings**. It kernel-checks:

1. the generic constructors' types (`Equivalence.mk`,
   `Relation.map_equivalence`) and that `Relation.EqvGen r` is an equivalence
   for *any* relation `r`;
2. that six cross-area witnesses (homotopy of maps, path homotopy, permutation
   same-cycle, list rotation, graph reachability, category zigzag) all have the
   single type `Equivalence R`;
3. that three witnesses can be rebuilt with **only** the relation's own
   `refl/symm/trans` through `Equivalence.mk` (list rotation, graph
   reachability, permutation same-cycle) — i.e. the bundling step contributes
   no mathematical content.

## Interpretation

- The cross-area "repetition" here is **irreducible multiplicity of an existing
  abstraction**. The genuinely relation-specific work — proving reflexivity,
  symmetry, transitivity — cannot be shared across homotopy, cycle membership,
  rotation and reachability; the only common step (the 3-field bundle) is
  already the generic `Equivalence.mk`.
- Contrast with case C (`structure_lifted_per_carrier`): there the *operation
  laws themselves* were rebuilt per carrier from different lift primitives
  (`image2_*` vs `map₂_*`), leaving a real shared-abstraction gap. Here the
  laws are per-relation by nature and the packaging is already generic.
- This validates the script-21 ranking: `shared_head_analogy` (and specifically
  the trivial-bundle families such as Equivalence / GaloisInsertion /
  IsInitial) is correctly a **lower-priority** refactoring target than
  structure-lifted families; the second-stage triage avoids sending effort
  after 348 communities that are mostly an existing concept used many times.
- A small automatable opportunity *does* exist and is noted, not forced: a
  handful of witnesses spell out `⟨refl, symm, trans⟩` with slightly different
  syntax rather than calling `Equivalence.mk`; this is cosmetic, not a missing
  theorem.
