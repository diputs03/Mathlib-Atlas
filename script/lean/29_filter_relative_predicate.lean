import Mathlib

/-!
# Case F probe: one generic “predicate relative to a locus filter”

Script 28 (semantic analogy track) surfaced a 304-pair “locus-relative” family:
the same mathematical predicate restated *globally*, *on a set* (`…On`), *at a
point* (`…At` / `…WithinAt`), and *almost everywhere* (`AE…` / `…ᵐ`). This probe
asks the case-E question in a new setting: is there ONE generic abstraction of
which these are all instances, and, if so, where does the ladder stop?

## The claim (positive part)

For a **unary pointwise** proposition `q : α → Prop`, every locus is just a
`Filter α`, and the relative statement is `Filter.Eventually q l`
(`∀ᶠ x in l, q x`). The four Mathlib idioms differ *only* by the filter:

| idiom                                   | locus filter `l`            |
|-----------------------------------------|-----------------------------|
| global `∀ x, q x`                       | `⊤`                         |
| on a set `∀ x ∈ s, q x` (`…On`)         | `𝓟 s` (principal)           |
| at a point / within (`…At`, `…WithinAt`)| `𝓝 x`, `𝓝[s] x = 𝓝 x ⊓ 𝓟 s`|
| almost everywhere (`∀ᵐ x ∂μ, q x`)      | `ae μ`                      |

`EventuallyEq` is exactly the relative statement for the point proposition
`f x = g x`; continuity is recovered by taking `q x := ContinuousAt f x` (a
pointwise `Tendsto`) and placing it under `⊤` / `𝓟 s`.

## The two boundaries (negative part)

1. **Arity.** `Monotone` / `StrictMono` quantify over *pairs*, so their locus
   filter lives on `α × α` (`𝓟 (s ×ˢ s)`), not `α`. The abstraction is uniform
   over point-arity `n` (put the filter on `α^n`), which is precisely why there
   is no `MonotoneAt x`: a single point supplies no ordered pair.
2. **Modulo a filter vs. relative to a filter.** `AEStronglyMeasurable` does
   *not* say a pointwise condition holds eventually; it existentially picks a
   globally-good `g` and only requires `f =ᵐ[μ] g` — a statement in the
   *quotient by the ae-equivalence relation*. `QuasiMeasurePreserving` is higher
   still: it compares two measures via `map f ≪`. These are a different generic
   (quotient/measure level), not an `AtLocus`.

Everything below is kernel-checked (no `sorry`).
-/

open Filter Set MeasureTheory Topology

namespace Atlas

/-- A pointwise proposition `q` stated relative to a **locus filter** `l`.
An `abbrev` so it is transparent and the existing `Filter.Eventually` lemmas
apply directly. -/
abbrev AtLocus {α : Type*} (l : Filter α) (q : α → Prop) : Prop :=
  ∀ᶠ x in l, q x

section UnaryLadder
variable {α β : Type*} (q : α → Prop) (s : Set α)

/-- Global = top filter: `AtLocus ⊤ q ↔ ∀ x, q x`. -/
theorem atLocus_top : AtLocus (⊤ : Filter α) q ↔ ∀ x, q x :=
  Filter.eventually_top

/-- On-a-set = principal filter: `AtLocus (𝓟 s) q ↔ ∀ x ∈ s, q x`. -/
theorem atLocus_principal : AtLocus (𝓟 s) q ↔ ∀ x ∈ s, q x :=
  Filter.eventually_principal

/-- Global is “on the whole set”. -/
theorem atLocus_top_eq_univ :
    AtLocus (⊤ : Filter α) q ↔ AtLocus (𝓟 (univ : Set α)) q := by
  rw [atLocus_top, atLocus_principal]
  simp

/-- `EventuallyEq l f g` is `AtLocus` of the equality point-proposition. -/
theorem eventuallyEq_atLocus (l : Filter α) (f g : α → β) :
    EventuallyEq l f g ↔ AtLocus l (fun x => f x = g x) :=
  Iff.rfl

end UnaryLadder

section PointAndContinuity
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (f : X → Y) (s : Set X) (x : X)

/-- “Within `s` at `x`” is the lattice meet of the point locus `𝓝 x` and the
set locus `𝓟 s`: loci form a filter lattice. -/
theorem nhdsWithin_is_meet : 𝓝[s] x = 𝓝 x ⊓ 𝓟 s :=
  rfl

/-- `ContinuousOn f s` is a pointwise `Tendsto` predicate (`ContinuousWithinAt`)
placed under the principal filter of `s`. -/
theorem continuousOn_atLocus :
    ContinuousOn f s ↔ AtLocus (𝓟 s) (fun x => ContinuousWithinAt f s x) :=
  Filter.eventually_principal.symm

/-- Global `Continuous f` is the same predicate under the top filter. -/
theorem continuous_atLocus_top :
    Continuous f ↔ AtLocus (⊤ : Filter X) (fun x => ContinuousAt f x) :=
  continuous_iff_continuousAt.trans Filter.eventually_top.symm

end PointAndContinuity

section ArityBoundary
variable {α β : Type*} [Preorder α] [Preorder β] (f : α → β) (s : Set α)

/-- `MonotoneOn f s` is a **binary** pointwise condition under the product
principal filter `𝓟 (s ×ˢ s)` on `α × α`. -/
theorem monotoneOn_product_locus :
    MonotoneOn f s ↔
      AtLocus (𝓟 (s ×ˢ s)) (fun p : α × α => p.1 ≤ p.2 → f p.1 ≤ f p.2) := by
  constructor
  · intro h
    exact Filter.eventually_principal.mpr
      fun p hp hle => h hp.1 hp.2 hle
  · intro h a ha b hb hab
    exact Filter.eventually_principal.mp h (a, b) ⟨ha, hb⟩ hab

/-- Global `Monotone f` is `MonotoneOn f univ` (same top/principal identity). -/
theorem monotone_eq_on_univ : Monotone f ↔ MonotoneOn f univ := by
  constructor
  · intro h a _ b _ hab
    exact h hab
  · intro h a b hab
    exact h (mem_univ a) (mem_univ b) hab

/-- Strict version rides the same product-filter ladder. -/
theorem strictMonoOn_product_locus :
    StrictMonoOn f s ↔
      AtLocus (𝓟 (s ×ˢ s)) (fun p : α × α => p.1 < p.2 → f p.1 < f p.2) := by
  constructor
  · intro h
    exact Filter.eventually_principal.mpr
      fun p hp hlt => h hp.1 hp.2 hlt
  · intro h a ha b hb hab
    exact Filter.eventually_principal.mp h (a, b) ⟨ha, hb⟩ hab

end ArityBoundary

section ModuloBoundary
variable {α β : Type*} [MeasurableSpace α] [TopologicalSpace β]
  (μ : Measure α) (f : α → β)

/-- `AEStronglyMeasurable f μ` unfolds to an *existential* over a second,
globally-good `g` that equals `f` only along `ae μ`. It is a statement modulo
the ae filter, not `AtLocus` of a pointwise condition on `f` alone. -/
theorem aeStronglyMeasurable_unfold :
    AEStronglyMeasurable f μ ↔
      ∃ g : α → β, StronglyMeasurable g ∧ EventuallyEq (ae μ) f g :=
  Iff.rfl

/-- Easy direction of the quotient relationship: globally good ⇒ good modulo
the filter (take `g := f`). -/
theorem atlas_stronglyMeasurable_imp_ae (hf : StronglyMeasurable f) :
    AEStronglyMeasurable f μ :=
  hf.aestronglyMeasurable

end ModuloBoundary

section QmpBoundary
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (f : α → β) (μa : Measure α) (μb : Measure β)

/- `QuasiMeasurePreserving` lives one level up: it relates two *measures* via
absolute continuity of the pushforward (`μa.map f ≪ μb`), with no pointwise
locus filter on `α`. It is therefore outside the `AtLocus` generic. -/
#check Measure.QuasiMeasurePreserving (f := f) (μa := μa) (μb := μb)

end QmpBoundary

end Atlas
