# Case study E (cont.) — generic pointwise monoid ladder

`script/lean/24_monoid_ladder.lean`, **exit 0, no errors/warnings**.

## Extending `PointwiseLift` to the unit

`23_binary_lift.lean` derived `Semigroup`/`CommSemigroup` once. The unit laws
are likewise duplicated between the two primitive lifts:

| | left identity | right identity | unit of a point `a` |
|---|---|---|---|
| Set | `Set.image2_left_identity` (Data/Set/NAry.lean l.306) | `image2_right_identity` l.312 | `{a}` = `Set.singleton a` |
| Filter | `Filter.map₂_left_identity` (Order/Filter/NAry.lean l.275) | `map₂_right_identity` l.280 | `pure a` |

Both state: if `a` is a left/right identity for `f`, then `{a}` / `pure a` is a
left/right identity for the lifted binary operation.

A subclass captures this:

```
class PointwiseLiftOne T extends PointwiseLift T where
  pure        : α → T α                                   -- Set.singleton / Filter.pure
  liftLeftId  : (h : ∀ b, f a b = b) → lift2 f (pure a) y = y
  liftRightId : (h : ∀ a, f a b = a) → lift2 f x (pure b) = x
```

`Set` and `Filter` both instantiate it from their existing identity lemmas
(Filter's `pure` is its `Applicative`/`Pure` instance value).

## Generic hierarchy, written once

```
mulOneClass : [PointwiseLiftOne T] → [MulOneClass α] → MulOneClass (T α)
    one := pure 1;  one_mul := liftLeftId  (·*·) 1 one_mul
                    mul_one := liftRightId (·*·) 1 mul_one
monoid      := { mulOneClass, semigroup with }
commMonoid  := { commSemigroup, monoid with }
```

## Kernel verification

`lake env lean script\lean\24_monoid_ladder.lean` → exit 0. It checks, for
**both** `Set α` and `Filter α`:

- `PointwiseLift.monoid : Monoid (Set α)` / `Monoid (Filter α)`;
- `PointwiseLift.commMonoid : CommMonoid …` for both;
- `pure 1 = {1}` for Set (`rfl`);
- the generic builder's `one_mul`/`mul_one` prove the explicit
  `image2 (·*·) (singleton 1) t = t` and `map₂ (·*·) (pure 1) l = l` goals;
- associativity and commutativity fields discharge the explicit `image2`/
  `map₂` goals.

So the entire **Semigroup → CommSemigroup → MulOneClass → Monoid → CommMonoid**
ladder that Mathlib writes separately for Set and Filter (Set/Basic.lean
l.570–640, Filter/Pointwise.lean l.559–569) is produced by one parametric
builder; only the 3+3 transport-law methods differ per carrier.

## Notes / boundaries

- `npow` is left to the structure default here. Mathlib's real
  `Set.monoid`/`Filter.monoid` explicitly thread `instNPow` because of the
  documented «pointwise nat action» choice (repeated pointwise multiplication
  vs pointwise scalar action, Set/Basic.lean l.56). A production class would
  make that choice a parameter too.
- As in 23, `open scoped Pointwise` is deliberately off, so examples use
  explicit `Set.image2`/`Set.singleton`/`Filter.map₂`/`pure` and there is no
  diamond with Mathlib's scoped instances.
- Carrier layering is unchanged: Set and Filter are the two primitive
  `PointwiseLiftOne`s; Finset still inherits via `Function.Injective.*` from
  Set and Ultrafilter from Filter.
