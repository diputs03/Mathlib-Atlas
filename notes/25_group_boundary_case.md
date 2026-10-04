# Case study E (cont. 2) — how far the generic ladder goes: the Group boundary

`script/lean/25_group_ladder.lean`, **exit 0, no errors/warnings**.

## Question

23/24 lifted `Semigroup → CommMonoid` from a binary lift. Adding a *unary*
lift (`Set.image` / `Filter.map`), how much further does the generic
construction go — in particular, can a pointwise **Group** be derived once for
both `Set` and `Filter`?

## What lifts

**(1) `DivInvMonoid` lifts generically.** A subclass `PointwiseLiftInv` adds
`lift1` (the unary lift) and an antidistributive fusion law. Then

```
divInvMonoid : [PointwiseLiftInv T] → [DivInvMonoid α] → DivInvMonoid (T α)
  inv := lift1 Inv.inv
  div := fun x y => lift2 (·*·) x (lift1 Inv.inv y)   -- mul-of-inverse
  div_eq_mul_inv := rfl
```

kernel-checks for both carriers (`#check` prints both).

**(2) The inverse law `(x*y)⁻¹ = y⁻¹*x⁻¹` lifts as a lemma** `invMul`, from the
identical fusion lemmas
`Set.image_image2_antidistrib` (Data/Set/NAry.lean l.274) and
`Filter.map_map₂_antidistrib` (Order/Filter/NAry.lean l.245), both of shape

```
lift1 k (lift2 f x y) = lift2 f' (lift1 g₁ y) (lift1 g₂ x)
  when ∀ a b, k (f a b) = f' (g₁ b) (g₂ a)
```

instantiated with the underlying group's `mul_inv_rev : (a*b)⁻¹ = b⁻¹*a⁻¹`.
Explicit `image`/`image2` and `map`/`map₂` goals for both carriers are
discharged by this one generic lemma.

## Where it stops: `Group` does NOT lift

`Group` (Algebra/Group/Defs.lean l.33) extends `DivInvMonoid` with a single
extra field, a **diagonal cancellation law**:

```
protected inv_mul_cancel : ∀ a, a⁻¹ * a = 1
```

Pointwise this would require, for every `s : Set α`,
`lift1 inv s * s = pure 1 = {1}`. That is false. For `s = ∅`:

```
image2 (·*·) (image Inv.inv ∅) ∅ = ∅            (by simp)
∅ ≠ singleton 1                                 (Set.empty_ne_singleton)
```

The image of the empty set is empty and `image2 _ ∅ ∅ = ∅`, never the nonempty
unit `{1}`. The probe kernel-checks exactly this counterexample. Filters have
the analogous obstruction (a general filter `f` satisfies neither
`map inv f ⊗ f = pure 1`).

## Interpretation

- The generic pointwise construction is valid precisely through
  **`DivInvMonoid`**: every law up to that point is a *pointwise/relational*
  transport (associativity, commutativity, unit, division-as-mul-inverse,
  antidistributive inversion), and those all follow from the binary/unary lift
  fusion lemmas.
- `Group` instead demands a *diagonal* law tying two uses of the **same**
  carrier object and forcing collapse to the unit; this is not preserved by
  image/map (which do not force every point to cancel to one value). This is a
  genuine mathematical boundary, not a missing lemma — and it explains why
  Mathlib supplies pointwise monoids/comm-monoids for Set and Filter but never
  pointwise groups.
- Discovery-loop value: the structural clustering flagged "the monoid ladder is
  duplicated across Set/Filter"; the positive construction (23–25) shows both
  the extent of the eliminable duplication (through DivInvMonoid) and its exact
  limit (Group), turning a similarity signal into a precise abstraction with a
  proven scope.

## Carrier / scope notes (unchanged)

Set/Filter are the two primitive lifts; Finset inherits via
`Function.Injective.*`, Ultrafilter via Filter. `npow`/`zpow` use structure
defaults (Mathlib threads explicit instances for the «pointwise nat action»
choice). `open scoped Pointwise` remains off, so all examples use explicit
`image2`/`image`/`map₂`/`map` and there is no diamond.
