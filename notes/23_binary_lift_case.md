# Case study E — the Set/Filter binary-lift abstraction (positive construction)

## Goal

Case C established that `Set` and `Filter` are the two **primitive** pointwise
lifts and that the operation laws are duplicated between them (Finset instead
inherits from Set through `Function.Injective.*`). This case designs and
kernel-checks the missing common abstraction downstream.

## The two primitive lemmas are the same lemma shape

`Set.image2_assoc` (`Data/Set/NAry.lean` l.207) and `Filter.map₂_assoc`
(`Order/Filter/NAry.lean` l.178):

```
Set.image2_assoc (h : ∀ a b c, f (g a b) c = f' a (g' b c)) :
    image2 f (image2 g s t) u = image2 f' s (image2 g' t u)
Filter.map₂_assoc (h : ∀ a b c, m (n a b) c = m' a (n' b c)) :
    map₂ m (map₂ n f g) h = map₂ m' f (map₂ n' g h)
```

Identical statement, differing only in the lift primitive (`image2` vs
`map₂`). `image2_comm` / `map₂_comm` (l.212 / l.185) are likewise parallel.

## The abstraction (`script/lean/23_binary_lift.lean`)

A minimal class abstracts a type constructor `T` equipped with a binary lift
that transports reassociation and commutation:

```
class PointwiseLift (T : Type u → Type u) where
  lift2     : (α → β → γ) → T α → T β → T γ
  liftAssoc : (h : ∀ a b c, f (g a b) c = f' a (g' b c)) →
              lift2 f (lift2 g x y) z = lift2 f' x (lift2 g' y z)
  liftComm  : (h : ∀ a b, f a b = g b a) → lift2 f x y = lift2 g y x
```

Both primitive lifts satisfy it using their *existing* lemmas — no new
mathematics:

```
instance : PointwiseLift Set    where lift2 := Set.image2;  liftAssoc _ _ _ _ h := Set.image2_assoc h;  liftComm _ _ h := Set.image2_comm h
instance : PointwiseLift Filter where lift2 := Filter.map₂; liftAssoc _ _ _ _ h := Filter.map₂_assoc h; liftComm _ _ h := Filter.map₂_comm h
```

The algebraic hierarchy is then written **once**:

```
@[instance_reducible]
def PointwiseLift.semigroup [PointwiseLift T] [Semigroup α] : Semigroup (T α) where
  mul x y   := lift2 (·*·) x y
  mul_assoc := liftAssoc (·*·) (·*·) (·*·) (·*·) (fun _ _ _ => mul_assoc ..)
```

and `commSemigroup` analogously.

## Kernel verification

`lake env lean script\lean\23_binary_lift.lean` → **exit 0, no errors or
warnings**. It checks:

- `PointwiseLift.semigroup : Semigroup (Set α)` and `: Semigroup (Filter α)`
  from the *same* builder;
- the associativity law for each carrier is produced by that builder
  (`(PointwiseLift.semigroup (T := Set)).mul_assoc`, and Filter analog) — i.e.
  `Set.semigroup`'s `image2_assoc mul_assoc` and `Filter.semigroup`'s
  `map₂_assoc mul_assoc` are two instances of one generic proof;
- the same for commutativity via `commSemigroup`.

The probe deliberately does **not** `open scoped Pointwise`, so Mathlib's
scoped pointwise instances are absent and there is no diamond; the derived
structures are constructed explicitly.

## What this shows

1. The duplication flagged structurally by scripts 17–19 is real *and*
   eliminable: a 3-method `PointwiseLift` class lets the semigroup/comm-semigroup
   ladder be derived once and reused by every carrier with a binary lift. This
   is the positive counterpart to cases B/C/D (which mostly found existing
   abstractions): here the Atlas identified a generic interface that is not
   currently a Mathlib typeclass.
2. The same extension pattern covers the rest of the ladder: `MulOneClass`
   needs a `pure`/singleton with `lift2_left/right_identity` (parallel
   `image2_left_identity` / `map₂_left_identity`), `Monoid` adds `npow`, and so
   on — each field has an already-proven `image2_*`/`map₂_*` counterpart.
3. Carrier coverage: `Set` and `Filter` become instances directly; `Finset`
   would still prefer its `Function.Injective` transfer out of `Set` (case C),
   and `Ultrafilter` inherits from `Filter`. So the final design is layered:
   two primitive `PointwiseLift` instances + injective transfer for the rest.

## Why it is a design opportunity, not a drop-in PR

- Mathlib keeps pointwise instances in the `Pointwise` scope precisely to
  control the documented «pointwise nat action» ambiguity (`Set/Basic.lean`
  l.56); promoting a global `PointwiseLift` class interacts with that decision.
- `Set.image2` and `Filter.map₂` have different definitional foundations
  (existential membership vs filter map); the class hides that behind the
  transported-law interface, which is exactly the point but changes instance
  search and `simp` normal forms.
- The probe is therefore a **viability proof**: the abstraction type-checks and
  derives the laws; production integration (scoping, the full ladder,
  `to_additive`, instance priorities) is a separate engineering step.
