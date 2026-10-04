/-
# Case study E (cont. 2) — how far does the generic ladder go? (the boundary)

23/24 derived Semigroup..CommMonoid from a binary lift. Here we add a UNARY
lift (`Set.image` / `Filter.map`) and ask whether inversion and groups lift.

Findings (all kernel-checked below):
  (1) `DivInvMonoid` DOES lift generically: `inv := lift1 Inv.inv`,
      `div := mul-of-inverse`, and `div_eq_mul_inv` is `rfl`.
  (2) The antidistributive inverse law `(x*y)⁻¹ = y⁻¹*x⁻¹` also lifts, from the
      identical fusion lemmas `Set.image_image2_antidistrib`
      (Data/Set/NAry.lean l.274) / `Filter.map_map₂_antidistrib`
      (Order/Filter/NAry.lean l.245).
  (3) `Group` does NOT lift. Its only extra field is `inv_mul_cancel : a⁻¹*a=1`
      (Algebra/Group/Defs.lean l.34) — a DIAGONAL cancellation law. Pointwise it
      would require `lift1 inv s * s = pure 1` for every s, which fails: for the
      empty set the LHS is empty and the RHS is the nonempty singleton `{1}`.
      This is exactly why Mathlib gives Set/Filter pointwise monoids but never
      pointwise groups. The generic ladder stops at DivInvMonoid for a genuine
      mathematical reason, not for lack of a lemma.

`open scoped Pointwise` stays off (no diamond).
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

set_option linter.unusedVariables false in
/-- Unary lift (`image` / `map`) with antidistributive fusion across the binary
lift — transports the inversion law `(x*y)⁻¹ = y⁻¹*x⁻¹`. -/
class PointwiseLiftInv (T : Type u → Type u) extends PointwiseLiftOne T where
  lift1 : {α β : Type u} → (α → β) → T α → T β
  lift1Anti : ∀ {α β γ α' β' : Type u}
      (k : γ → β') (f : α → β → γ) (f' : β' → α' → β')
      (g₁ : β → β') (g₂ : α → α')
      (h : ∀ a b, k (f a b) = f' (g₁ b) (g₂ a))
      (x : T α) (y : T β),
      lift1 k (lift2 f x y) = lift2 f' (lift1 g₁ y) (lift1 g₂ x)

instance : PointwiseLiftInv Set where
  lift1 := Set.image
  lift1Anti := fun _ _ _ _ _ h _ _ => Set.image_image2_antidistrib h

instance : PointwiseLiftInv Filter where
  lift1 := Filter.map
  lift1Anti := fun _ _ _ _ _ h _ _ => Filter.map_map₂_antidistrib h

namespace PointwiseLift

@[instance_reducible]
def semigroup [PointwiseLift T] [Semigroup α] : Semigroup (T α) where
  mul x y := lift2 (· * ·) x y
  mul_assoc x y z :=
    liftAssoc (· * ·) (· * ·) (· * ·) (· * ·)
      (fun a b c => mul_assoc a b c) x y z

@[instance_reducible]
def mulOneClass [PointwiseLiftOne T] [MulOneClass α] : MulOneClass (T α) where
  one := PointwiseLiftOne.pure (1 : α)
  mul x y := lift2 (· * ·) x y
  one_mul := PointwiseLiftOne.liftLeftId (· * ·) 1 one_mul
  mul_one := PointwiseLiftOne.liftRightId (· * ·) 1 mul_one

@[instance_reducible]
def monoid [PointwiseLiftOne T] [Monoid α] : Monoid (T α) :=
  { mulOneClass, semigroup with }

/-- Generic pointwise DivInvMonoid: inversion is the unary lift, division is
mul-of-inverse, so `div_eq_mul_inv` is definitional. (zpow uses the default
recursor.) -/
@[instance_reducible]
def divInvMonoid [PointwiseLiftInv T] [DivInvMonoid α] : DivInvMonoid (T α) :=
  { monoid with
    inv := fun x => PointwiseLiftInv.lift1 Inv.inv x
    div := fun x y => lift2 (· * ·) x (PointwiseLiftInv.lift1 Inv.inv y)
    div_eq_mul_inv := fun _ _ => rfl }

/-- The transported antidistributive inverse law `(x*y)⁻¹ = y⁻¹*x⁻¹`. -/
lemma invMul [PointwiseLiftInv T] [Group α] (x y : T α) :
    PointwiseLiftInv.lift1 Inv.inv (lift2 (· * ·) x y) =
      lift2 (· * ·) (PointwiseLiftInv.lift1 Inv.inv y)
        (PointwiseLiftInv.lift1 Inv.inv x) :=
  PointwiseLiftInv.lift1Anti Inv.inv (· * ·) (· * ·) Inv.inv Inv.inv
    (fun a b => mul_inv_rev a b) x y

end PointwiseLift

/-! ### (1)+(2) DivInvMonoid and the inverse law lift for BOTH carriers -/

section
variable {α : Type u} [DivInvMonoid α]

#check (PointwiseLift.divInvMonoid : DivInvMonoid (Set α))
#check (PointwiseLift.divInvMonoid : DivInvMonoid (Filter α))

end

section
variable {α : Type u} [Group α]

example (s t : Set α) :
    Set.image Inv.inv (Set.image2 (· * ·) s t) =
      Set.image2 (· * ·) (Set.image Inv.inv t) (Set.image Inv.inv s) :=
  PointwiseLift.invMul (T := Set) s t

example (f g : Filter α) :
    Filter.map Inv.inv (Filter.map₂ (· * ·) f g) =
      Filter.map₂ (· * ·) (Filter.map Inv.inv g) (Filter.map Inv.inv f) :=
  PointwiseLift.invMul (T := Filter) f g

/-! ### (3) Why `Group` does NOT lift: the diagonal cancellation law fails.

A pointwise group would need `s⁻¹ * s = {1}` for every set `s`. For `s = ∅`: -/

example : Set.image2 (· * ·) (Set.image Inv.inv (∅ : Set α)) (∅ : Set α) = ∅ := by simp

/-- ...but the required unit `{1}` is nonempty, so the equality cannot hold for
the empty set. (`∅ ≠ {1}`.) -/
example : (∅ : Set α) ≠ Set.singleton (1 : α) := Set.empty_ne_singleton 1

end
