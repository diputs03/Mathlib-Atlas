/-
# Case study C — pointwise-algebra families: where the generic API is reused
  and where the structure is lifted independently per carrier.

Atlas scripts 17–19 cluster the cross-area "pointwise algebra" communities
(`Add/Mul/Zero/One/Neg/Inv/Sub/Div`, `Semigroup/Monoid/CommMonoid`,
`MulAction`, …) across the carriers `Set`, `Finset`, `Filter`, `Ultrafilter`,
`Equiv`, `Finsupp`. Reading the source shows three *different* construction
mechanisms that the name-level graph cannot distinguish:

  • `Set α`    — PRIMITIVE pointwise lift: laws from `Set.image2_assoc` etc.
                 (Mathlib/Algebra/Group/Pointwise/Set/Basic.lean)
  • `Filter α` — PRIMITIVE pointwise lift: laws from `Filter.map₂_assoc` etc.
                 (Mathlib/Order/Filter/Pointwise.lean)
  • `Finset α` — does NOT re-prove the hierarchy. It embeds into `Set α` by the
                 injective coercion `(↑ : Finset α → Set α)` and pulls every
                 structure down through the generic one-sided transfer API
                 `Function.Injective.*` (the InjSurj communities, e.g.
                 `Finset.semigroup = coe_injective.semigroup _ coe_mul`).

This file kernel-checks, downstream (Mathlib is never modified):
  1. the generic transfer lemma exists;
  2. Set / Filter carry the primitive instances;
  3. the Finset instance is rebuilt here from the generic transfer;
  4. the SAME algebraic law holds in all three carriers — the empirical
     "analogy" the embeddings found is a real kernel-level fact.

Note: pointwise `Finset` operations require `DecidableEq α` (they are built on
`Finset.image2`); `Set` and `Filter` do not.
-/

import Mathlib

open scoped Pointwise

variable {α : Type*}

/- The generic one-sided structure-transfer API (InjSurj family). -/
#check @Function.Injective.semigroup

section Semigroup

variable [Semigroup α] [DecidableEq α]

/- `Set α`: primitive pointwise lift (associativity via `image2_assoc`). -/
#check (Set.semigroup : Semigroup (Set α))

/- `Filter α`: the other primitive pointwise lift (via `map₂_assoc`). -/
#check (Filter.semigroup : Semigroup (Filter α))

/- `Finset α`: rebuilt here from the generic injective transfer out of
`Set α` — exactly the construction used by Mathlib's `Finset.semigroup`. -/
#check (Finset.semigroup : Semigroup (Finset α))
example : Semigroup (Finset α) :=
  Finset.coe_injective.semigroup _ Finset.coe_mul

/- The shared associativity law, kernel-checked in every carrier. -/
example (s t u : Set α)    : (s * t) * u = s * (t * u) := mul_assoc s t u
example (s t u : Finset α) : (s * t) * u = s * (t * u) := mul_assoc s t u
example (f g h : Filter α) : (f * g) * h = f * (g * h) := mul_assoc f g h

/- Under the Finset→Set coercion the Finset law is literally the Set law,
which is *why* the injective transfer suffices. -/
example (s t u : Finset α) :
    (↑((s * t) * u) : Set α) = ↑(s * (t * u)) := by
  rw [Finset.coe_mul, Finset.coe_mul, Finset.coe_mul, Finset.coe_mul,
    mul_assoc]

end Semigroup

section Monoid

variable [Monoid α] [DecidableEq α]

/- Same picture one level up: Set/Filter primitive, Finset transferred. -/
#check (Set.monoid : Monoid (Set α))
#check (Filter.monoid : Monoid (Filter α))
example : Monoid (Finset α) :=
  Finset.coe_injective.monoid _ Finset.coe_one Finset.coe_mul Finset.coe_pow

example (s : Set α)    : 1 * s = s := one_mul s
example (s : Finset α) : 1 * s = s := one_mul s
example (f : Filter α) : 1 * f = f := one_mul f

end Monoid
