/-
# Case study E — the Set/Filter binary-lift abstraction.

Cases C/D showed `Set α` and `Filter α` are the two *primitive* pointwise
lifts: each rebuilds the algebraic hierarchy from its own binary-lift primitive
(`Set.image2` / `Filter.map₂`), while `Finset` avoids this by inheriting from
`Set` through `Function.Injective.*`.

Reading the source, the two primitive lemmas have the *exact same shape*:

  Set.image2_assoc (h : ∀ a b c, f (g a b) c = f' a (g' b c)) :
      image2 f (image2 g s t) u = image2 f' s (image2 g' t u)
  Filter.map₂_assoc (h : ∀ a b c, m (n a b) c = m' a (n' b c)) :
      map₂ m (map₂ n f g) h = map₂ m' f (map₂ n' g h)

(and `image2_comm` / `map₂_comm` likewise). This file introduces, DOWNSTREAM
(Mathlib untouched), a minimal `PointwiseLift` class capturing that common
shape, instantiates it for both `Set` and `Filter` using their existing lemmas,
and derives `Semigroup` / `CommSemigroup` ONCE generically. Both primitive
lifts then obtain the structure from the same builder — the missing
abstraction is viable and is kernel-checked below.

We deliberately do NOT `open scoped Pointwise`, so Mathlib's scoped instances
stay out of scope and there is no diamond; we construct the derived structures
explicitly.
-/

import Mathlib

universe u

set_option linter.unusedVariables false in
/-- The common interface satisfied by `Set.image2` and `Filter.map₂`: a binary
lift of operations, with reassociation and commutation transported from the
underlying operations. -/
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

/-- `Set` is a pointwise lift through `Set.image2`. -/
instance : PointwiseLift Set where
  lift2 := Set.image2
  liftAssoc := fun _ _ _ _ h _ _ _ => Set.image2_assoc h
  liftComm := fun _ _ h _ _ => Set.image2_comm h

/-- `Filter` is a pointwise lift through `Filter.map₂`. -/
instance : PointwiseLift Filter where
  lift2 := Filter.map₂
  liftAssoc := fun _ _ _ _ h _ _ _ => Filter.map₂_assoc h
  liftComm := fun _ _ h _ _ => Filter.map₂_comm h

namespace PointwiseLift

/-- Generic pointwise semigroup: written ONCE, works for every PointwiseLift. -/
@[instance_reducible]
def semigroup [PointwiseLift T] [Semigroup α] : Semigroup (T α) where
  mul x y := lift2 (· * ·) x y
  mul_assoc x y z :=
    liftAssoc (· * ·) (· * ·) (· * ·) (· * ·)
      (fun a b c => mul_assoc a b c) x y z

/-- Generic pointwise commutative semigroup. -/
@[instance_reducible]
def commSemigroup [PointwiseLift T] [CommSemigroup α] :
    CommSemigroup (T α) where
  mul x y := lift2 (· * ·) x y
  mul_assoc x y z :=
    liftAssoc (· * ·) (· * ·) (· * ·) (· * ·)
      (fun a b c => mul_assoc a b c) x y z
  mul_comm x y := liftComm (· * ·) (· * ·) (fun a b => mul_comm a b) x y

end PointwiseLift

/-! ### Both primitive lifts fit the same generic builder -/

section
variable {α : Type u} [Semigroup α]

#check (PointwiseLift.semigroup : Semigroup (Set α))
#check (PointwiseLift.semigroup : Semigroup (Filter α))

/-- Associativity for `Set`, produced by the GENERIC builder (this is exactly
what `Set.semigroup` proves by hand via `image2_assoc mul_assoc`). -/
example (s t u : Set α) :
    Set.image2 (· * ·) (Set.image2 (· * ·) s t) u =
      Set.image2 (· * ·) s (Set.image2 (· * ·) t u) :=
  (PointwiseLift.semigroup (T := Set)).mul_assoc s t u

/-- Associativity for `Filter`, produced by the SAME generic builder (this is
exactly what `Filter.semigroup` proves by hand via `map₂_assoc mul_assoc`). -/
example (f g h : Filter α) :
    Filter.map₂ (· * ·) (Filter.map₂ (· * ·) f g) h =
      Filter.map₂ (· * ·) f (Filter.map₂ (· * ·) g h) :=
  (PointwiseLift.semigroup (T := Filter)).mul_assoc f g h

end

section
variable {α : Type u} [CommSemigroup α]

#check (PointwiseLift.commSemigroup : CommSemigroup (Set α))
#check (PointwiseLift.commSemigroup : CommSemigroup (Filter α))

/-- Commutativity, again from one generic builder. -/
example (s t : Set α) :
    Set.image2 (· * ·) s t = Set.image2 (· * ·) t s :=
  (PointwiseLift.commSemigroup (T := Set)).mul_comm s t

example (f g : Filter α) :
    Filter.map₂ (· * ·) f g = Filter.map₂ (· * ·) g f :=
  (PointwiseLift.commSemigroup (T := Filter)).mul_comm f g

end
