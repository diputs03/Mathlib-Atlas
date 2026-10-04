# Case study E — a generic pointwise-lift abstraction for Set/Filter (consolidated)

This memo consolidates probes 23–25. It records (i) the structural signal that
motivated the construction, (ii) the abstraction and the algebraic ladder it
generates, (iii) its proven boundary, and (iv) what production integration into
Mathlib would require. All claims below are kernel-checked downstream;
`external/mathlib4` was never modified.

Probes: `script/lean/23_binary_lift.lean`, `24_monoid_ladder.lean`,
`25_group_ladder.lean` (each `lake env lean …` → exit 0, no warnings).

## 1. Signal

Scripts 17–19 clustered cross-area analogies by type/structure. Triage bucket
`structure_lifted_per_carrier` (29 communities) is pointwise algebra rebuilt
separately on Set / Finset / Filter / Ultrafilter / Equiv / Finsupp. Case C
(script 20) showed the two **primitive** lifts are `Set` (via `Set.image2`) and
`Filter` (via `Filter.map₂`); Finset inherits from Set through
`Function.Injective.*`, Ultrafilter from Filter. Reading the source, the
primitive transport lemmas are textually identical up to the lift name.

## 2. The shared interface

Binary lift (associativity/commutativity transport), unit, and unary lift with
antidistributive fusion form a three-level class hierarchy:

```
class PointwiseLift T where
  lift2     : (α→β→γ) → T α → T β → T γ
  liftAssoc : (h : ∀ a b c, f (g a b) c = f' a (g' b c)) →
              lift2 f (lift2 g x y) z = lift2 f' x (lift2 g' y z)
  liftComm  : (h : ∀ a b, f a b = g b a) → lift2 f x y = lift2 g y x

class PointwiseLiftOne T extends PointwiseLift T where
  pure        : α → T α                                   -- Set.singleton / Filter.pure
  liftLeftId  : (h : ∀ b, f a b = b) → lift2 f (pure a) y = y
  liftRightId : (h : ∀ a, f a b = a) → lift2 f x (pure b) = x

class PointwiseLiftInv T extends PointwiseLiftOne T where
  lift1    : (α→β) → T α → T β                            -- Set.image / Filter.map
  lift1Anti: (h : ∀ a b, k (f a b) = f' (g₁ b) (g₂ a)) →
             lift1 k (lift2 f x y) = lift2 f' (lift1 g₁ y) (lift1 g₂ x)
```

Both primitive lifts instantiate every class from their **existing** lemmas:

| method | Set | Filter |
|---|---|---|
| lift2 | `Set.image2` | `Filter.map₂` |
| liftAssoc | `image2_assoc` (Data/Set/NAry.lean:207) | `map₂_assoc` (Order/Filter/NAry.lean:178) |
| liftComm | `image2_comm:212` | `map₂_comm:185` |
| pure | `Set.singleton` | `pure` (Applicative Filter) |
| liftLeftId/RightId | `image2_left/right_identity:306/312` | `map₂_left/right_identity:275/280` |
| lift1 | `Set.image` | `Filter.map` |
| lift1Anti | `image_image2_antidistrib:274` | `map_map₂_antidistrib:245` |

## 3. The ladder, written once

A single parametric builder per structure, generic over `T`:

```
semigroup      = { mul := lift2 (·*·); mul_assoc := liftAssoc … mul_assoc }
commSemigroup  = semigroup + mul_comm := liftComm … mul_comm
mulOneClass    = { one := pure 1; one_mul := liftLeftId … one_mul
                                ; mul_one := liftRightId … mul_one }
monoid         = { mulOneClass, semigroup with }
commMonoid     = { commSemigroup, monoid with }
divInvMonoid   = { monoid with inv := lift1 Inv.inv
                                 ; div := mul-of-inverse (div_eq_mul_inv := rfl) }
invMul (lemma) = lift1Anti … mul_inv_rev           -- (x*y)⁻¹ = y⁻¹*x⁻¹
```

Kernel checks (`#check` + explicit `image2`/`map₂` goals) confirm each builder
produces the structure for **both** `Set α` and `Filter α`. The hand-written
per-carrier ladders in `Algebra/Group/Pointwise/Set/Basic.lean` (l.570–640) and
`Order/Filter/Pointwise.lean` (l.559–569) are therefore two specializations of
one construction; only the transport-law methods differ per carrier.

## 4. Proven boundary: stops at DivInvMonoid

`Group` adds exactly one field, the **diagonal cancellation law**
`inv_mul_cancel : a⁻¹*a = 1` (Algebra/Group/Defs.lean:34). It does not survive
the pointwise lift: it would force `lift1 inv s * s = {1}` for every `s`, but
for `s = ∅`, `image2 (·*·) (image inv ∅) ∅ = ∅ ≠ {1}`
(`Set.empty_ne_singleton`). Probe 25 kernel-checks this counterexample (and the
Filter analogue is the same shape). The distinction is structural:

- laws through DivInvMonoid are **relational transports** between lifted
  operations — preserved by image/map;
- cancellation is a **diagonal** law that identifies two occurrences of the same
  object and forces collapse to the unit — not preserved.

This explains why Mathlib has pointwise monoids/comm-monoids but no pointwise
groups for Set/Filter. The abstraction's scope is thus exact.

## 5. Carrier layering

- Primitive `PointwiseLift(One)(Inv)` instances: **Set**, **Filter**.
- **Finset** should keep inheriting from Set via `Function.Injective.*`
  (case C) — it needs `[DecidableEq α]` and its instances are
  `coe_injective.<class>`; making Finset a direct PointwiseLift would duplicate
  that mechanism.
- **Ultrafilter** inherits from Filter.
So production design is: two primitive instances + injective transfer for the
rest.

## 6. What production integration would require (design, not started)

1. **Scoping.** Mathlib keeps pointwise instances in the `Pointwise` scope to
   control the «pointwise nat action» choice (Set/Basic.lean:56). A promoted
   class must decide global vs scoped and avoid the resulting diamonds.
2. **npow/zpow.** The probes use structure defaults; real `Set.monoid` /
   `Filter.monoid` thread explicit `instNPow` (repeated pointwise multiplication
   vs pointwise scalar action). The class should parameterize this choice.
3. **to_additive.** Each multiplicative builder needs its additive counterpart
   (`AddSemigroup`, `SMul`/`nsmul`, …); the probes are multiplicative only.
4. **Instance priorities / simp normal forms.** Routing `Set.image2`/
   `Filter.map₂` through a generic class changes instance search and the
   `simp` lemmas that canonicalize pointwise expressions; these need auditing.
5. **Definitional hiding.** `image2` (existential membership) and `map₂`
   (filter map) have different foundations; the class hides them behind
   transported laws, which is the intent but must not regress decidability/ext.

## 7. Discovery-loop significance

This is the arc's first **positive** result (cases B/C/D mostly re-found
abstractions that already exist): an embedding/clustering similarity was turned
into a concrete, kernel-checked generic interface that Mathlib does not
currently have, together with a proof of exactly how far it reaches. It is a
template for later communities: propose the unifying class, instantiate it from
existing lemmas, derive the shared API once, and locate — by kernel failure if
necessary — the precise point at which the analogy ends.
