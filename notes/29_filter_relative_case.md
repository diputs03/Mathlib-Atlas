# Case F — Is there one generic “predicate relative to a locus filter”?

**Probe:** `script/lean/29_filter_relative_predicate.lean` — kernel-checks,
exit 0, no warnings, no `sorry`.
**Trigger:** script 28’s semantic track; 304 of 627 hidden candidates (48%) are
the same predicate restated globally / on-a-set (`…On`) / at-a-point
(`…At`,`…WithinAt`) / almost-everywhere (`AE…`,`…ᵐ`).

## Grounded definitions (this Mathlib, commit bbcd196)

- `Filter.Eventually p f := {x | p x} ∈ f` — `Order/Filter/Defs.lean:281`
- `EventuallyEq l f g := ∀ᶠ x in l, f x = g x` — `Order/Filter/Defs.lean:297`;
  `f =ᵐ[μ] g` unfolds to `EventuallyEq (ae μ) f g` — `OuterMeasure/AE.lean:70`
- `ContinuousAt f x := Tendsto f (𝓝 x) (𝓝 (f x))`,
  `ContinuousWithinAt f s x := Tendsto f (𝓝[s] x) (𝓝 (f x))`,
  `ContinuousOn f s := ∀ x ∈ s, ContinuousWithinAt f s x`
  — `Topology/Defs/Filter.lean:179-192`; `nhdsWithin x s = 𝓝 x ⊓ 𝓟 s` (l.138)
- `Monotone f := ∀ a b, a ≤ b → f a ≤ f b`;
  `MonotoneOn f s := ∀ a∈s, b∈s, a ≤ b → f a ≤ f b`; `StrictMonoOn` analogous
  — `Order/Monotone/Defs.lean:62-100`
- `AEStronglyMeasurable f μ := ∃ g, StronglyMeasurable g ∧ f =ᵐ[μ] g`
  — `Function/StronglyMeasurable/AEStronglyMeasurable.lean:66`
- `Measure.QuasiMeasurePreserving f μa μb := Measurable f ∧ μa.map f ≪ μb`
  — `Measure/QuasiMeasurePreserving.lean:43`

## Positive ladder (all kernel-checked)

Define the transparent `abbrev AtLocus l q := ∀ᶠ x in l, q x`. Then the whole
unary family is ONE shape with four concrete loci:

| theorem in probe | statement |
|---|---|
| `atLocus_top` | `AtLocus ⊤ q ↔ ∀ x, q x` via `Filter.eventually_top` |
| `atLocus_principal` | `AtLocus (𝓟 s) q ↔ ∀ x ∈ s, q x` via `Filter.eventually_principal` |
| `atLocus_top_eq_univ` | global = “on `univ`” |
| `eventuallyEq_atLocus` | `EventuallyEq l f g ↔ AtLocus l (fun x => f x = g x)` by `Iff.rfl` |
| `nhdsWithin_is_meet` | `𝓝[s] x = 𝓝 x ⊓ 𝓟 s` by `rfl` — loci form a filter lattice |
| `continuousOn_atLocus` | `ContinuousOn f s ↔ AtLocus (𝓟 s) (ContinuousWithinAt f s ·)` |
| `continuous_atLocus_top` | `Continuous f ↔ AtLocus ⊤ (ContinuousAt f ·)` |

So **global / on-set / at-point / within-set / almost-everywhere differ only by
the choice of `Filter α`** (`⊤`, `𝓟 s`, `𝓝 x`, `𝓝 x ⊓ 𝓟 s`, `ae μ`), and
`EventuallyEq`/continuity are recovered with no new construction.

## Boundary 1 — arity (order predicates live on α × α)

`Monotone`/`StrictMono` quantify over **pairs**. The probe kernel-checks that the
“on `s`” version is the same shape only after moving the locus to the product:

- `monotoneOn_product_locus`:
  `MonotoneOn f s ↔ AtLocus (𝓟 (s ×ˢ s)) (fun p => p.1 ≤ p.2 → f p.1 ≤ f p.2)`
- `strictMonoOn_product_locus`: same with `<`.
- `monotone_eq_on_univ`: `Monotone f ↔ MonotoneOn f univ`.

The generic is therefore uniform over **point-arity n** (put the filter on
`α^n`). This is exactly why there is no `MonotoneAt x`: a unary neighbourhood
`𝓝 x` supplies one coordinate, but monotonicity needs an ordered *pair*. The
“missing `…At`” members of the 304-family are not an oversight — they have no
unary content.

## Boundary 2 — “modulo a filter” is a different generic from “relative to” it

- `aeStronglyMeasurable_unfold` (by `Iff.rfl`) shows `AEStronglyMeasurable` is
  **existential**: pick a globally-good `g` and require `EventuallyEq (ae μ) f g`.
  It is a statement in the **quotient by the ae-equivalence relation**, not
  `AtLocus` of any pointwise condition on `f` alone.
- `atlas_stronglyMeasurable_imp_ae`: global-good ⇒ quotient-good (take `g := f`);
  the converse needs an existential witness and is not an `AtLocus`.
- `QuasiMeasurePreserving f μa μb = Measurable f ∧ μa.map f ≪ μb` compares **two
  measures** (pushforward and absolute continuity); the `#check` confirms its
  type `(α→β) → Measure α → Measure β → Prop`. There is no pointwise locus on
  `α` at all — it sits one level up, on filters/measures modulo null sets.

## Verdict

Unlike case E (which produced a genuinely absent class `PointwiseLift`), case F
finds that **the unifying abstraction already exists and is `Filter.Eventually`**
(with `⊤ / 𝓟 / 𝓝 / ae` as the loci). The 304 semantic pairs are therefore:

1. **unary pointwise predicates + continuity** — already one generic; the
   multiplicity is naming/notation residue (`P` vs `POn` vs `PAt`), not missing
   machinery;
2. **pair-quantified order predicates** — the same generic on `α × α`, with no
   meaningful `At` member (arity boundary);
3. **almost-everywhere / quasi-measure-preserving** — a strictly different,
   quotient/measure-level generic (modulo a filter), correctly not collapsed.

**No new Lean class is warranted.** The actionable residue is a *presentation*
opportunity (state new `POn`/`PAt` lemmas through the corresponding filter and
reuse `eventually_top`/`eventually_principal` rather than re-proving them), plus
a design rule: “restricted predicate” should be recognised as filter
parameterisation, with arity and quotient level checked before assuming a new
abstraction. This closes case F as a **negative/structural result with a
kernel-verified boundary**, complementing case E’s positive construction.
