# Case study B — the repeated `FunLike` "apply API" promoted to a generic lemma

**Status: kernel-verified.** Lean probe: `script/lean/16_isapply_abstraction.lean`
(compiles with exit 0, no errors/warnings; log `notes/16_isapply_abstraction.log`).
Mathlib commit `bbcd1968…`, Lean `v4.34.0-rc2`, Windows, no WSL. `external/mathlib4`
was only read, never modified.

## 1. What the unsupervised engine flagged

Script 15 experiment B (cross-area twins), with no labels and only structural
signatures, ranked the pointwise "evaluation" family as its strongest repeated
cross-area family: `zero_apply / add_apply / sub_apply / neg_apply / smul_apply /
coe_zero / coe_add / sum_apply / prod_apply`, repeated for `Seminorm`,
`GroupSeminorm`, `MultilinearMap`, `ContinuousMultilinearMap`, `QuadraticMap`,
`VectorMeasure`, `OuterMeasure`, `Kernel`, `SchwartzMap`, `ModularForm`,
`CuspForm`, `SlashInvariantForm`, `ContinuousLinearMap`, `UniformConvergenceCLM`,
… across 6–8 top-level areas.

Corpus scale (script 13 features, human-authored only): **1,282** declarations
in the apply/coe family. Largest suffixes:

| suffix | n | suffix | n | suffix | n |
|---|--:|---|--:|---|--:|
| coe_zero | 118 | coe_one | 103 | coe_smul | 90 |
| coe_mul | 110 | coe_add | 105 | coe_neg | 85 |
| zero_apply | 77 | smul_apply | 76 | coe_sub | 73 |
| add_apply | 72 | neg_apply | 61 | mul_apply | 57 |
| one_apply | 53 | sub_apply | 53 | **prod_apply** | **47** |
| inv_apply | 25 | vadd_apply | 15 | **sum_apply** | **28** |

## 2. What the library actually contains (evidence, read-only)

The generic abstraction is real and **recent (files dated 2026, Moritz Doll)**:

* Classes `IsZeroApply / IsOneApply / IsAddApply / IsMulApply / IsSubApply /
  IsNegApply / IsSMulApply / …` in `Mathlib/Data/FunLike/IsApply.lean`. Each
  bundled type gets an instance whose field proof is `rfl`, e.g.
  `LinearAlgebra/Multilinear/Basic.lean:189`
  `instance : IsAddApply (MultilinearMap R M₁ M₂) … where add_apply _ _ _ := rfl`.
* The generic **collective** lemmas `prod_apply` / `sum_apply` and
  `FunLike.coe_prod` / `FunLike.coe_sum` in
  `Algebra/BigOperators/Pi.lean:235-251` (section `FunLike`), stated once over
  `[FunLike F α β] [AddCommMonoid β] [AddCommMonoid F] [IsZeroApply F α β]
  [IsAddApply F α β]`.
* The per-type binary lemmas are being turned into deprecated aliases of the
  generic ones. Footprint from source: **95 `Is*Apply` instances across 21
  files**; **153 `@[deprecated] … alias … apply/coe_*` lines across 24 files**
  (e.g. `MultilinearMap.sum_apply` is now a deprecated alias whose type is the
  fully generic `sum_apply`; `VectorMeasure`, `QuadraticMap`, `GroupSeminorm`
  show the same pattern).

**Interpretation.** An unsupervised structural scan independently re-discovered
exactly the family a human refactor is actively deduplicating in 2026. That is
external validation of experiment B's signal: the repeated-signature ranking
surfaces genuine abstraction opportunities, not coincidental name collisions.

## 3. The remaining gap, and its kernel verification

The migration is **incomplete**. `Analysis/Normed/Group/Hom.lean` gives
`NormedAddGroupHom` a `FunLike` (l.88), pointwise `Add`/`Zero`/`AddCommGroup`
(l.285/310/500), and already-`rfl` `add_apply` (l.303) and `coe_add` (l.299),
but it has **no `IsZeroApply` / `IsAddApply` instance**, and still carries
hand-written `coe_sum` (l.531) and `sum_apply` (l.536, proved via
`simp only [coe_sum, Finset.sum_apply]`).

The probe promotes this straggler **downstream** (Mathlib untouched):

```lean
instance : IsZeroApply (NormedAddGroupHom V₁ V₂) V₁ V₂ where zero_apply _ := rfl
instance : IsAddApply  (NormedAddGroupHom V₁ V₂) V₁ V₂ where add_apply  _ _ _ := rfl
```

Both close by `rfl`, after which the bespoke lemmas follow from the *existing*
generic API with no Analysis-specific proof:

* `(f + g) v = f v + g v`                         := `IsAddApply.add_apply f g v`
* `↑(∑ i, f i) = ∑ i, (f i : V₁ → V₂)`            := `FunLike.coe_sum s f`
* `(∑ i ∈ s, f i) v = ∑ i ∈ s, f i v`             := generic `sum_apply s f v`
  — i.e. the statement of `NormedAddGroupHom.sum_apply` is obtained for free.

A migrated type from a different area, `MultilinearMap` (LinearAlgebra), is shown
to be covered by the **same** generic `sum_apply`. The three `#check`s print the
generic `sum_apply` / `prod_apply` / `FunLike.coe_sum` types, confirming the
abstraction that subsumes the per-type copies.

## 4. What this demonstrates for the Atlas loop

1. **Discovery → external corroboration:** the engine's top twin family matches
   a live maintainer refactor, with a measurable remaining footprint.
2. **Discovery → a concrete, finished piece of work:** one straggler type is
   identified and its missing instances + generic derivations are
   kernel-checked; the same recipe (add `Is*Apply` rfl instances, delete the
   bespoke `coe_*`/`*_apply`) applies to the other not-yet-migrated bundled
   types that still define concrete `sum_apply`/`prod_apply`
   (e.g. several in the corpus list of 28/47).
3. **Correctness boundary stays in the kernel:** Atlas proposes; Lean verifies.

## 5. Scope / limits

* This is one family, promoted as an end-to-end exemplar of the
  hypothesis → formalize → verify loop; it is not a claim that every
  `prod_apply` is subsumed (binary "pairing" lemmas such as
  `MonoidHom.prod_apply : f.prod g x = (f x, g x)` are a different lemma).
* No change was made to `external/mathlib4`; upstreaming the two
  `NormedAddGroupHom` instances would be a separate Mathlib PR.
