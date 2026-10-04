import Mathlib

/-!
# 16 (case study B) — The repeated FunLike "apply API" twin family

## What the unsupervised scan found
Script 15 experiment B flagged, with no labels, the pointwise "evaluation"
family (`zero_apply / add_apply / sum_apply / coe_add / coe_sum / …`) as the
strongest cross-area twin family, independently repeated for Seminorm,
MultilinearMap, QuadraticMap, VectorMeasure, Kernel, ContinuousMap,
NormedAddGroupHom, … across 6–8 top-level areas. Corpus scale (human-authored,
script 13): 1,282 declarations in the apply/coe family.

## What the library actually contains (evidence)
The generic abstraction is real and recent (files dated 2026, Moritz Doll):
* classes `IsZeroApply / IsAddApply / IsMulApply / …` in
  `Mathlib.Data.FunLike.IsApply`;
* the generic collective lemma `prod_apply` / `sum_apply` and
  `FunLike.coe_prod` / `FunLike.coe_sum` in `Mathlib.Algebra.BigOperators.Pi`
  (section `FunLike`).
Most per-type lemmas are now `rfl` `Is*Apply` instances plus
`@[deprecated] protected alias` (153 deprecated apply aliases in 24 files;
95 `Is*Apply` instances in 21 files). So the scan independently re-discovered a
family a human refactor is actively deduplicating — external validation.

## The remaining gap this file kernel-checks
Not every bundled type has been migrated. `NormedAddGroupHom` (Analysis) still
has hand-written `add_apply` (already `rfl`), `coe_sum` and `sum_apply`, but is
missing the `IsZeroApply` / `IsAddApply` instances. We add those two instances
DOWNSTREAM (Mathlib stays read-only) with `rfl`, and then derive its bespoke
`sum_apply` / `coe_sum` purely from the existing generic lemma — proving the
per-type copies are eliminable. We also show a migrated type from a different
area (LinearAlgebra's `MultilinearMap`) is covered by the same generic lemma.
-/

open scoped BigOperators

-- The generic collective lemma already exists for every bundled `FunLike`:
#check @sum_apply   -- [FunLike F α β] [AddCommMonoid β] [AddCommMonoid F]
                    --   [IsZeroApply F α β] [IsAddApply F α β] → ...
#check @prod_apply
#check @FunLike.coe_sum

section MigratedLinearAlgebra
/-- `MultilinearMap` (LinearAlgebra) already has `IsZeroApply`/`IsAddApply`,
so its (deprecated) `MultilinearMap.sum_apply` is just the generic lemma. -/
example {ι ι' R : Type*} {M₁ : ι' → Type*} {M₂ : Type*} [Semiring R]
    [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂]
    [∀ i, Module R (M₁ i)] [Module R M₂]
    (s : Finset ι) (f : ι → MultilinearMap R M₁ M₂) (v : ∀ i, M₁ i) :
    (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v :=
  sum_apply s f v
end MigratedLinearAlgebra

section StragglerAnalysis
variable {V₁ V₂ : Type*} [SeminormedAddCommGroup V₁] [SeminormedAddCommGroup V₂]

/-- The two instances `NormedAddGroupHom` is missing; both close by `rfl`
because its pointwise `zero`/`add` are already definitionally pointwise. -/
instance : IsZeroApply (NormedAddGroupHom V₁ V₂) V₁ V₂ where
  zero_apply _ := rfl

instance : IsAddApply (NormedAddGroupHom V₁ V₂) V₁ V₂ where
  add_apply _ _ _ := rfl

/-- Its binary lemma is now the generic class projection. -/
example (f g : NormedAddGroupHom V₁ V₂) (v : V₁) :
    (f + g) v = f v + g v :=
  IsAddApply.add_apply f g v

/-- Its coercion lemma is the generic norm_cast lemma. -/
example {ι : Type*} (s : Finset ι) (f : ι → NormedAddGroupHom V₁ V₂) :
    (↑(∑ i ∈ s, f i) : V₁ → V₂) = ∑ i ∈ s, (f i : V₁ → V₂) :=
  FunLike.coe_sum s f

/-- Its bespoke `NormedAddGroupHom.sum_apply` (Hom.lean:536) is now obtained
with NO Analysis-specific proof, from the generic FunLike lemma. -/
example {ι : Type*} (s : Finset ι) (f : ι → NormedAddGroupHom V₁ V₂) (v : V₁) :
    (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v :=
  sum_apply s f v

end StragglerAnalysis
