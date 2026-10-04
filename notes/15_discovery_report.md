# 15 - Discovery experiments report

Joined node set: 574391 Mathlib declarations (13 features + 09 skeletons + 14 stats).
216838 elaborator-generated declarations (13 isGenerated: _simp_N, ._proof_N, .match_N, Lean.Macro/ParserDescr, macroRules auxiliaries) are excluded from the mathematical-construction experiments A/B/C, leaving 357553 human-authored; they are retained for bridge (E) and anomaly (D) analyses.
All results are *candidate structural hypotheses*, ranked deterministically.

## A. Repeated type signatures (candidate missing abstractions)
Signature = kind, exact binder counts, multiset of typeclass constraints, conclusion head. Clusters (size>=6, >=3 namespaces): **4738**. Ranked with constraint-bearing / non-Eq-Iff clusters first.

Top 15 (most semantically specific first):
| size | ns | areas | kind | nPi | constraints | conclusion |
|---|---|---|---|---|---|---|
| 49 | 40 | 11 | definition | 2 | Inhabited×1 | Inhabited |
| 55 | 37 | 3 | definition | 6 | CategoryTheory.Category×1 | Quiver.Hom |
| 51 | 30 | 3 | definition | 3 | CategoryTheory.Category×1 | CategoryTheory.Functor |
| 35 | 29 | 4 | definition | 5 | CategoryTheory.Category×1 | CategoryTheory.Iso |
| 41 | 27 | 4 | definition | 3 | CategoryTheory.Category×1 | CategoryTheory.Iso |
| 32 | 24 | 7 | definition | 2 | DecidableEq×1 | DecidableEq |
| 55 | 24 | 4 | definition | 2 | CategoryTheory.Category×1 | CategoryTheory.Functor |
| 35 | 23 | 4 | definition | 5 | CategoryTheory.Category×1 | Quiver.Hom |
| 34 | 23 | 3 | definition | 7 | CategoryTheory.Category×1 | CategoryTheory.Iso |
| 34 | 23 | 2 | definition | 4 | CategoryTheory.Category×1 | Quiver.Hom |
| 26 | 19 | 3 | definition | 4 | CategoryTheory.Category×1 | CategoryTheory.Functor |
| 19 | 19 | 3 | definition | 5 | CategoryTheory.Category×1 | CategoryTheory.Functor |
| 28 | 19 | 1 | theorem | 6 | TopologicalSpace×2 | Continuous |
| 25 | 18 | 2 | definition | 7 | CategoryTheory.Category×1 | Quiver.Hom |
| 17 | 17 | 5 | definition | 2 | LinearOrder×1 | LinearOrder |

## B. Cross-area structural twins (candidate analogies)
Signature abstracts names and conclusion head, keeps arity/constraints and log-binned type/value size and proof style; human-authored members must span multiple areas and namespaces: **5557 twin groups**, constraint-bearing ranked first.

Top 15 by area spread (with one exemplar per area):
- **15 members across 8 areas** (theorem, nPi=8, constraints=['IsZeroApply'], rfl=False): Algebra:Eq(LieModule.Weight.zero_apply); Analysis:Eq(AddGroupSeminorm.zero_apply); Analysis:Eq(GroupSeminorm.zero_apply); Analysis:Eq(NonarchAddGroupSeminorm.zero_apply); Analysis:Eq(SchwartzMap.zero_apply); Analysis:Eq(Seminorm.zero_apply)
- **25 members across 7 areas** (theorem, nPi=3, constraints=['SizeOf'], rfl=False): Algebra:Eq(CartanMatrix.Generators.E.sizeOf_spec); Algebra:Eq(CartanMatrix.Generators.F.sizeOf_spec); Algebra:Eq(CartanMatrix.Generators.H.sizeOf_spec); Algebra:Eq(PreOpposite.op'.sizeOf_spec); Algebra:Eq(PreQuasiregular.mk.sizeOf_spec); Algebra:Eq(Rack.PreEnvelGroup.incl.sizeOf_spec)
- **20 members across 7 areas** (theorem, nPi=11, constraints=['IsSMulApply'], rfl=False): Analysis:Eq(AddGroupSeminorm.smul_apply); Analysis:Eq(GroupSeminorm.smul_apply); Analysis:Eq(NonarchAddGroupSeminorm.smul_apply); Analysis:Eq(SchwartzMap.smul_apply); Analysis:Eq(Seminorm.smul_apply); Data:Eq(smul_apply)
- **19 members across 7 areas** (theorem, nPi=10, constraints=['FunLike', 'IsSMulApply', 'SMul'], rfl=False): Analysis:Eq(AddGroupSeminorm.coe_smul); Analysis:Eq(ContDiffMapSupportedIn.coe_smul); Analysis:Eq(GroupSeminorm.coe_smul); Analysis:Eq(NonarchAddGroupSeminorm.coe_smul); Analysis:Eq(Seminorm.coe_smul); Analysis:Eq(TestFunction.coe_smul)
- **18 members across 7 areas** (theorem, nPi=10, constraints=['IsAddApply'], rfl=False): Analysis:Eq(AddGroupNorm.add_apply); Analysis:Eq(AddGroupSeminorm.add_apply); Analysis:Eq(GroupNorm.add_apply); Analysis:Eq(GroupSeminorm.add_apply); Analysis:Eq(SchwartzMap.add_apply); Analysis:Eq(Seminorm.add_apply)
- **18 members across 7 areas** (theorem, nPi=7, constraints=['FunLike', 'IsZeroApply', 'Zero'], rfl=False): Algebra:Eq(LieModule.Weight.coe_zero); Analysis:Eq(AddGroupSeminorm.coe_zero); Analysis:Eq(ContDiffMapSupportedIn.coe_zero); Analysis:Eq(GroupSeminorm.coe_zero); Analysis:Eq(NonarchAddGroupSeminorm.coe_zero); Analysis:Eq(SchwartzMap.coeFn_zero)
- **91 members across 6 areas** (inductive, nPi=2, constraints=['TopologicalSpace'], rfl=False): AlgebraicTopology:None(SimplyConnectedSpace); Analysis:None(ContinuousENorm); Analysis:None(ENormedAddCommMonoid); Analysis:None(ENormedAddMonoid); Analysis:None(ENormedCommMonoid); Analysis:None(ENormedMonoid)
- **27 members across 6 areas** (inductive, nPi=2, constraints=['CommRing'], rfl=False): Algebra:None(AlgCat); Algebra:None(BialgCat); Algebra:None(CoalgCat); Algebra:None(CommAlgCat); Algebra:None(CommBialgCat); Algebra:None(CommHopfAlgCat)
- **15 members across 6 areas** (theorem, nPi=9, constraints=['Add', 'FunLike', 'IsAddApply'], rfl=False): Analysis:Eq(AddGroupNorm.coe_add); Analysis:Eq(AddGroupSeminorm.coe_add); Analysis:Eq(ContDiffMapSupportedIn.coe_add); Analysis:Eq(GroupNorm.coe_add); Analysis:Eq(GroupSeminorm.coe_add); Analysis:Eq(Seminorm.coe_add)
- **11 members across 6 areas** (theorem, nPi=10, constraints=['IsSubApply'], rfl=False): Analysis:Eq(SchwartzMap.sub_apply); Data:Eq(sub_apply); LinearAlgebra:Eq(MultilinearMap.sub_apply); LinearAlgebra:Eq(QuadraticMap.sub_apply); MeasureTheory:Eq(MeasureTheory.VectorMeasure.sub_apply); NumberTheory:Eq(CuspForm.sub_apply)
- **11 members across 6 areas** (theorem, nPi=9, constraints=['IsNegApply'], rfl=False): Analysis:Eq(SchwartzMap.neg_apply); Data:Eq(neg_apply); LinearAlgebra:Eq(MultilinearMap.neg_apply); LinearAlgebra:Eq(QuadraticMap.neg_apply); MeasureTheory:Eq(MeasureTheory.VectorMeasure.neg_apply); NumberTheory:Eq(CuspForm.neg_apply)
- **7 members across 6 areas** (definition, nPi=2, constraints=['Inhabited'], rfl=False): Algebra:Inhabited(GenContFract.IntFractPair.inhabited); CategoryTheory:Inhabited(CategoryTheory.instInhabitedMkId); Computability:EmptyCollection(Turing.ListBlank.hasEmptyc); Computability:Inhabited(Turing.ListBlank.inhabited); Data:Semiquot(Semiquot.univ); Lean:Inhabited(instInhabitedState_mathlib)
- **18 members across 5 areas** (definition, nPi=2, constraints=['Inhabited'], rfl=False): Algebra:GenContFract.Pair(GenContFract.instInhabitedPair.default); Algebra:Inhabited(AddOpposite.instInhabited); Algebra:Inhabited(FreeAddMagma.instInhabited); Algebra:Inhabited(FreeAddSemigroup.instInhabited); Algebra:Inhabited(FreeMagma.instInhabited); Algebra:Inhabited(FreeSemigroup.instInhabited)
- **13 members across 5 areas** (definition, nPi=2, constraints=['DecidableEq'], rfl=False): Algebra:DecidableEq(WithZero.decidableEq); Algebra:DecidableEq(instDecidableEqFreeAddMagma); Algebra:DecidableEq(instDecidableEqFreeMagma); CategoryTheory:DecidableEq(CategoryTheory.instDecidableEqBicone); CategoryTheory:DecidableEq(CategoryTheory.instDecidableEqPairwise); Data:DecidableEq(Sym2.instDecidableEq)
- **13 members across 5 areas** (theorem, nPi=2, constraints=['SizeOf'], rfl=False): Algebra:Eq(Rack.PreEnvelGroup.unit.sizeOf_spec); CategoryTheory:Eq(CategoryTheory.Bicone.left.sizeOf_spec); CategoryTheory:Eq(CategoryTheory.Bicone.right.sizeOf_spec); CategoryTheory:Eq(CategoryTheory.FreeMonoidalCategory.NormalMonoidalObject.unit.sizeOf_spec); CategoryTheory:Eq(CategoryTheory.Limits.WalkingParallelFamily.one.sizeOf_spec); CategoryTheory:Eq(CategoryTheory.Limits.WalkingParallelFamily.zero.sizeOf_spec)

## C. Generalization families
Same namespace + conclusion head + constraints with an arity ladder (spread>=2): **10924 families**.
Top 15:
| namespace | conclusion | size | arities |
|---|---|---|---|
| Set | Eq | 1135 | [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 20] |
|  | Eq | 960 | [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] |
| Nat | Eq | 942 | [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] |
| Real | Eq | 893 | [0, 1, 2, 3, 4, 5, 6, 7, 9] |
| Complex | Eq | 893 | [0, 1, 2, 3, 4, 5, 6, 7, 9] |
| Fin | Eq | 762 | [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] |
| Polynomial | Eq | 603 | [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] |
| Set | Iff | 576 | [1, 2, 3, 4, 5, 6, 7, 8, 9, 12] |
| List | Eq | 502 | [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13] |
|  | Iff | 487 | [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] |
|  | Iff | 464 | [2, 3, 4, 5, 6, 7, 8, 9] |
| ENNReal | Eq | 416 | [0, 1, 2, 3, 4, 5, 6] |
| Equiv | Eq | 415 | [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11] |
| Finset | Eq | 386 | [2, 3, 4, 5, 6, 7, 8, 9, 10, 11] |
| MeasureTheory | Eq | 379 | [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] |

## E. Bridge declarations (area reach >=8): 16464
Top 20:
| reach (out+in) | out areas | in areas | name | area |
|---|---|---|---|---|
| 31 | 2 | 29 | Nat.instLinearOrder | Data |
| 31 | 2 | 29 | Nat.instPreorder | Data |
| 30 | 2 | 28 | Equiv.instEquivLike | Logic |
| 30 | 2 | 28 | Nat.instPartialOrder | Data |
| 30 | 1 | 29 | Preorder.toLE | Order |
| 30 | 1 | 29 | PartialOrder.toPreorder | Order |
| 29 | 1 | 28 | Finset.instSetLike | Data |
| 29 | 1 | 28 | EquivLike.toFunLike | Data |
| 29 | 1 | 28 | SetLike.instMembership | Data |
| 29 | 1 | 28 | DFunLike.coe | Data |
| 29 | 1 | 28 | Equiv.symm | Logic |
| 29 | 1 | 28 | Set.instMembership | Data |
| 28 | 1 | 27 | Bot.bot | Order |
| 28 | 1 | 27 | Set.instSingletonSet | Data |
| 28 | 0 | 28 | Equiv | Logic |
| 28 | 1 | 27 | Preorder.toLT | Order |
| 28 | 1 | 27 | Equiv.mk | Logic |
| 28 | 1 | 27 | OrderBot.toBot | Order |
| 28 | 1 | 27 | AddZeroClass.toAddZero | Algebra |
| 28 | 1 | 27 | AddCommSemigroup.toAddCommMagma | Algebra |

## D. Anomaly counts
reduction_heavy_rfl / giant_term = value walk hit the 50,000-node cap (13 valueTruncated), split by whether the proof closes by rfl; recursion_heavy = recRefs+caseRefs>=200; theorem_hub = top human theorems by distinct dependents.
- reduction_heavy_rfl: 107
- giant_term: 26801 (capped at 200 in file)
- theorem_hub: 200
- recursion_heavy: 46

Top reduction-heavy rfl proofs:
  - valueNodes=50000 AlgebraicGeometry.SpecModulesToSheafFullyFaithful._proof_6 [Mathlib.AlgebraicGeometry.Modules.Tilde]
  - valueNodes=50000 PresheafOfModules.Monoidal.tensorObj_map_tmul [Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal]
  - valueNodes=50000 LieAlgebra.of_add [Mathlib.Algebra.Lie.Extension]
  - valueNodes=50000 IntermediateField.liftAlgEquiv._proof_11 [Mathlib.FieldTheory.IntermediateField.Basic]
  - valueNodes=50000 TopCat.isLimitConeOfForget._proof_3 [Mathlib.Topology.Category.TopCat.Limits.Basic]
  - valueNodes=50000 FDRep.forget₂HomLinearEquiv._proof_7 [Mathlib.RepresentationTheory.FDRep]
  - valueNodes=50000 groupCohomology.cocycles₁IsoOfIsTrivial._proof_9 [Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree]
  - valueNodes=50000 Ideal.powQuotSuccInclusion._proof_5 [Mathlib.NumberTheory.RamificationInertia.Basic]
  - valueNodes=50000 ContinuousCohomology.d₀kerIso._proof_4 [Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree]
  - valueNodes=50000 AddMonCat.forget_createsLimit._proof_6 [Mathlib.Algebra.Category.MonCat.Limits]

Top theorem hubs (theorems most used by distinct others):
  - inNeighbors=9513 RingHomInvPair.ids [Mathlib.Algebra.Ring.CompTypeclasses]
  - inNeighbors=7609 smulCommClass_self [Mathlib.Algebra.Group.Action.Defs]
  - inNeighbors=7343 CategoryTheory.Category.assoc [Mathlib.CategoryTheory.Category.Basic]
  - inNeighbors=7265 Nat.instAtLeastTwoHAddOfNat [Mathlib.Data.Nat.Init]
  - inNeighbors=6094 SeminormedAddCommGroup.toIsTopologicalAddGroup [Mathlib.Analysis.Normed.Group.Uniform]
  - inNeighbors=5950 IsScalarTower.left [Mathlib.Algebra.Group.Action.Defs]
  - inNeighbors=5934 IsOrderedAddMonoid.toAddLeftMono [Mathlib.Algebra.Order.Monoid.Defs]
  - inNeighbors=5751 IsScalarTower.right [Mathlib.Algebra.Algebra.Defs]
  - inNeighbors=5591 Algebra.to_smulCommClass [Mathlib.Algebra.Algebra.Basic]
  - inNeighbors=4459 Real.instIsStrictOrderedRing [Mathlib.Data.Real.Basic]

