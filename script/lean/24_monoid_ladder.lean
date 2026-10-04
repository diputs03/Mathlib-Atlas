/-
# Case study E (cont.) — generic pointwise MONOID ladder from `PointwiseLift`.

`23_binary_lift.lean` derived `Semigroup`/`CommSemigroup` once for any binary
lift. Here we add the unit: `Set.image2_left/right_identity`
(Data/Set/NAry.lean l.306/312) and `Filter.map₂_left/right_identity`
(Order/Filter/NAry.lean l.275/280) are again parallel, with `{a}` =
`Set.singleton a` corresponding to `Filter.pure a`.

A subclass `PointwiseLiftOne` adds `pure` and the two identity transport laws;
`MulOneClass`, `Monoid`, `CommMonoid` are then derived GENERICALLY and shown for
both `Set` and `Filter`. Mathlib is never modified and `open scoped Pointwise`
is intentionally avoided (no instance diamond).
-/

import Mathlib

universe u

set_option linter.unusedVariables false in
class PointwiseLift (T : Type u → Type u) where
  lift2 : {α β γ : Type u} → (α → β → γ) → T α → T β → T γ
  liftAssoc : ∀ {α β γ δ ε ε' : Type u}
      (f : δ → γ → ε) (g : α → β → δ)
      (f' : α → ε' → ε) (g' : β → γ → ε')
      (h : ∀ a b c, f (g a b) c = f' a (g' b c))
      (x : T α) (y : T β) (z : T γ),
      lift2 f (lift2 g x y) z = lift2 f' x (lift2 g' y z)
  liftComm : ∀ {α β γ : Type u} (f : α → β → γ) (g : β → α → γ)
      (h : ∀ a b, f a b = g b a) (x : T α) (y : T β),
      lift2 f x y = lift2 g y x

instance : PointwiseLift Set where
  lift2 := Set.image2
  liftAssoc := fun _ _ _ _ h _ _ _ => Set.image2_assoc h
  liftComm := fun _ _ h _ _ => Set.image2_comm h

instance : PointwiseLift Filter where
  lift2 := Filter.map₂
  liftAssoc := fun _ _ _ _ h _ _ _ => Filter.map₂_assoc h
  liftComm := fun _ _ h _ _ => Filter.map₂_comm h

set_option linter.unusedVariables false in
/-- A pointwise lift with a unit (`singleton` / `pure`). -/
class PointwiseLiftOne (T : Type u → Type u) extends PointwiseLift T where
  pure : {α : Type u} → α → T α
  liftLeftId : ∀ {α β : Type u} (f : α → β → β) (a : α),
      (∀ b, f a b = b) → ∀ (y : T β), lift2 f (pure a) y = y
  liftRightId : ∀ {α β : Type u} (f : α → β → α) (b : β),
      (∀ a, f a b = a) → ∀ (x : T α), lift2 f x (pure b) = x

instance : PointwiseLiftOne Set where
  pure := Set.singleton
  liftLeftId := fun _ _ h t => Set.image2_left_identity h t
  liftRightId := fun _ _ h s => Set.image2_right_identity h s

instance : PointwiseLiftOne Filter where
  pure := fun a => @pure Filter _ _ a
  liftLeftId := fun _ _ h l => Filter.map₂_left_identity h l
  liftRightId := fun _ _ h l => Filter.map₂_right_identity h l

namespace PointwiseLift

@[instance_reducible]
def semigroup [PointwiseLift T] [Semigroup α] : Semigroup (T α) where
  mul x y := lift2 (· * ·) x y
  mul_assoc x y z :=
    liftAssoc (· * ·) (· * ·) (· * ·) (· * ·)
      (fun a b c => mul_assoc a b c) x y z

@[instance_reducible]
def commSemigroup [PointwiseLift T] [CommSemigroup α] : CommSemigroup (T α) where
  mul x y := lift2 (· * ·) x y
  mul_assoc x y z :=
    liftAssoc (· * ·) (· * ·) (· * ·) (· * ·)
      (fun a b c => mul_assoc a b c) x y z
  mul_comm x y := liftComm (· * ·) (· * ·) (fun a b => mul_comm a b) x y

@[instance_reducible]
def mulOneClass [PointwiseLiftOne T] [MulOneClass α] : MulOneClass (T α) where
  one := PointwiseLiftOne.pure (1 : α)
  mul x y := lift2 (· * ·) x y
  one_mul := PointwiseLiftOne.liftLeftId (· * ·) 1 one_mul
  mul_one := PointwiseLiftOne.liftRightId (· * ·) 1 mul_one

/-- Generic pointwise monoid: semigroup + unit, written once. -/
@[instance_reducible]
def monoid [PointwiseLiftOne T] [Monoid α] : Monoid (T α) :=
  { mulOneClass, semigroup with }

/-- Generic pointwise commutative monoid. -/
@[instance_reducible]
def commMonoid [PointwiseLiftOne T] [CommMonoid α] : CommMonoid (T α) :=
  { commSemigroup, monoid with }

end PointwiseLift

/-! ### The full monoid ladder for BOTH carriers, from one generic builder -/

section
variable {α : Type u} [Monoid α]

#check (PointwiseLift.monoid : Monoid (Set α))
#check (PointwiseLift.monoid : Monoid (Filter α))

/-- Unit is `{1}` / `pure 1`. -/
example : PointwiseLiftOne.pure (1 : α) = ({1} : Set α) := rfl

/-- Left/right unit laws produced by the generic builder. -/
example (t : Set α) : Set.image2 (· * ·) (Set.singleton 1) t = t :=
  (PointwiseLift.mulOneClass (T := Set)).one_mul t
example (t : Set α) : Set.image2 (· * ·) t (Set.singleton 1) = t :=
  (PointwiseLift.mulOneClass (T := Set)).mul_one t
example (l : Filter α) : Filter.map₂ (· * ·) (@pure Filter _ _ 1) l = l :=
  (PointwiseLift.mulOneClass (T := Filter)).one_mul l
example (l : Filter α) : Filter.map₂ (· * ·) l (@pure Filter _ _ 1) = l :=
  (PointwiseLift.mulOneClass (T := Filter)).mul_one l

/-- Associativity + unit together: a genuine `Monoid` for each carrier. -/
example (s t u : Set α) :
    Set.image2 (· * ·) (Set.image2 (· * ·) s t) u =
      Set.image2 (· * ·) s (Set.image2 (· * ·) t u) :=
  (PointwiseLift.monoid (T := Set)).mul_assoc s t u
example (f g h : Filter α) :
    Filter.map₂ (· * ·) (Filter.map₂ (· * ·) f g) h =
      Filter.map₂ (· * ·) f (Filter.map₂ (· * ·) g h) :=
  (PointwiseLift.monoid (T := Filter)).mul_assoc f g h

end

section
variable {α : Type u} [CommMonoid α]

#check (PointwiseLift.commMonoid : CommMonoid (Set α))
#check (PointwiseLift.commMonoid : CommMonoid (Filter α))

example (s t : Set α) :
    Set.image2 (· * ·) s t = Set.image2 (· * ·) t s :=
  (PointwiseLift.commMonoid (T := Set)).mul_comm s t
example (f g : Filter α) :
    Filter.map₂ (· * ·) f g = Filter.map₂ (· * ·) g f :=
  (PointwiseLift.commMonoid (T := Filter)).mul_comm f g

end
