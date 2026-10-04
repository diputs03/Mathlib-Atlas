/-
37_generalization_boundary.lean — check of script-36's one repeated family.

Script 36 found a single genuinely repeated statement shape:
  (G : <concrete algebraic category>) [Subsingleton G] : IsZero G
for GrpCat / CommGrpCat / AddGrpCat / AddCommGrpCat / SemiNormedGrp / ModuleCat.
Hypothesis: a generic category-theory lemma is missing and these are redundant
specializations. This probe shows why NO such generic lemma exists.

`IsZero X` is a CATEGORICAL condition: unique morphism in and out of X
(`unique_to`/`unique_from`, i.e. `Unique (X ⟶ Y)` and `Unique (Y ⟶ X)` for every
Y). `[Subsingleton X]` is a TYPE-theoretic condition: all *elements* of the
carrier type X are equal. In an arbitrary category the latter says nothing about
the hom-sets X ⟶ Y, so `Subsingleton X → IsZero X` is not provable. Each concrete
category can bridge the two only through its OWN hom extensionality (`ext x`,
`map_one`), which is why the lemma is necessarily repeated per category.
-/
import Mathlib

open CategoryTheory CategoryTheory.Limits

/- The categorical zero-object requirement: unique maps each way, for every Y. -/
#check @IsZero
#check @IsZero.unique_to
#check @IsZero.unique_from

/- The concrete lemmas exist at their expected types (same shape, per category):
   each proof uses that category's element-level extensionality. -/
#check GrpCat.isZero_of_subsingleton
#check CommGrpCat.isZero_of_subsingleton
#check ModuleCat.isZero_of_subsingleton

/- Contrast: in an ARBITRARY category, `Subsingleton X` (equal elements of the
   type X) does not provide unique homs; there is deliberately no
   `isZero_of_subsingleton` in CategoryTheory.Limits. The generic categorical
   notion that WOULD suffice is already `IsZero` itself (unique_to/unique_from),
   so introducing a "generic" lemma would be circular. -/

#eval ()
