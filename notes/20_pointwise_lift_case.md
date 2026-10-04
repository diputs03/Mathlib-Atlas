# Case study C — pointwise algebra: generic transfer vs. per-carrier lift

## What the Atlas flagged

Scripts 17–19 grouped the cross-area **pointwise algebra** communities and
script 19 labeled 29 of them `structure_lifted_per_carrier`: the same
algebraic operation/structure is instantiated on several carrier types across
different areas. Representative communities:

- pointwise operations `Add/Mul/Zero/One/Neg/Inv/Sub/Div` across
  `Equiv, Filter, Finset, Set, Ultrafilter, FreeAlgebra.Pre` (#220/#222/#286/
  #289/#292/#293/#296/#298);
- `Semigroup/AddSemigroup` on `Filter, Set, Ultrafilter` (#392/#414);
- the whole monoid ladder as Set↔Filter pairs (#574–#602: `MulOneClass`,
  `Semigroup`, `Monoid`, `CommSemigroup`, `CommMonoid`, `DivisionMonoid`, …);
- actions `MulAction` (#84, 9 members / 7 carriers), `AddAction` (#140),
  `DistribMulAction` (#243/#185).

At name level these look like one repeated pattern ("build structure X on each
container"). Reading the source shows they are **not** all constructed the
same way.

## Three construction mechanisms

| carrier | how its pointwise hierarchy is built | source |
|---|---|---|
| `Set α` | **primitive lift** — laws from `Set.image2_assoc / image2_comm / image2_left_identity` | `Algebra/Group/Pointwise/Set/Basic.lean` (`Set.semigroup` l.570, `Set.monoid` l.640) |
| `Filter α` | **primitive lift** — laws from `Filter.map₂_assoc / map₂_comm / map₂_left_identity` | `Order/Filter/Pointwise.lean` (`Filter.semigroup`, `Filter.monoid` l.569) |
| `Finset α` | **reuses a generic API** — the whole hierarchy is `coe_injective.<class> … coe_mul`, inheriting from `Set α` through the injective coercion | `Algebra/Group/Pointwise/Finset/Basic.lean` l.719–1020 |

Concretely, Finset never repeats an algebraic law:

```
Finset.semigroup       = coe_injective.semigroup _ coe_mul                 (l.719)
Finset.commSemigroup   = coe_injective.commSemigroup _ coe_mul            (l.729)
Finset.mulOneClass     = coe_injective.mulOneClass _ (coe_singleton 1) coe_mul (l.749)
Finset.monoid          = coe_injective.monoid _ coe_one coe_mul coe_pow   (l.813)
Finset.commMonoid      = coe_injective.commMonoid _ coe_one coe_mul coe_pow (l.940)
Finset.divisionMonoid  = coe_injective.divisionMonoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow (l.965)
```

`coe_injective.<class>` is the generic **one-sided structure-transfer** API
`Function.Injective.*` from `Algebra/Group/InjSurj.lean` (and its Ring /
GroupWithZero / Order.Ring siblings) — which the embeddings clustered
*separately* as the `Function.Injective/Surjective.*` communities
(#7824–#8168). So two apparently unrelated cluster families are linked by an
implementation relationship: Finset's pointwise instances are a consumer of
the InjSurj transfer API, with Set as the base model.

`Set` and `Filter` remain two **independent primitive lifts**: Set defines the
operation by existential membership (`image2`), Filter by `map₂`; there is no
shared "binary lift preserves algebra" abstraction, so each rebuilds the
hierarchy from its own associativity/comm/identity lemmas. The library note
«pointwise nat action» (`Set/Basic.lean` l.56) already names `Set, Finset,
Filter` as the pointwise-monoid trio, but no common typeclass unifies the two
primitive constructions.

## Kernel verification (`script/lean/20_pointwise_lift.lean`)

Compiled downstream with `lake env lean` (Mathlib untouched), **exit 0, no
errors or warnings**. It kernel-checks:

1. the generic transfer lemma exists:
   `@Function.Injective.semigroup : [Mul M₁] → [Semigroup M₂] → (f : M₁→M₂) →
    Function.Injective f → (∀ x y, f (x*y) = f x*f y) → Semigroup M₁`;
2. `Set.semigroup : Semigroup (Set α)` and `Filter.semigroup : Semigroup
   (Filter α)` are the primitive instances;
3. the Finset instance is rebuilt from the generic API —
   `example : Semigroup (Finset α) := Finset.coe_injective.semigroup _
   Finset.coe_mul` (and the `Monoid` analogue) — type-checks, i.e. Finset's
   construction really is an instance of the generic transfer and needs no
   algebraic law of its own;
4. the shared associativity law holds in all three carriers
   (`(s*t)*u = s*(t*u)` for Set / Finset / Filter), and under the Finset→Set
   coercion the Finset law is definitionally the Set law
   (`rw [coe_mul ×4, mul_assoc]`).

A required side condition surfaced by the kernel (not visible in the cluster
data): pointwise `Finset` operations carry `[DecidableEq α]` because they are
defined via `Finset.image2`, whereas `Set`/`Filter` do not — a concrete reason
the three carriers cannot be collapsed into one identical instance signature.

## Interpretation for Atlas

- The detector's "one family" is correct at the **statement-shape** level but
  hides three distinct *construction* relationships. Distinguishing
  "primitive lift" from "transferred via a generic API" is exactly the kind of
  proof/body signal (value head `image2` vs `map₂` vs `coe_injective.*`) the
  raw-Expr corpus preserves and name-only analysis would lose — direct support
  for the project's preserve-everything principle.
- The genuine residual duplication is **Set vs Filter** (and Ultrafilter, which
  extends Filter). A unifying abstraction would have to abstract over the
  binary-lift primitive (`image2`/`map₂`) and its assoc/comm/identity lemmas;
  that is a real design opportunity, not a mechanical alias, and is left as a
  candidate rather than forced.
- This is the second time the pipeline re-found prior art and then localized
  the actual gap (case B: Is*Apply API + the `NormedAddGroupHom` straggler;
  case C: InjSurj transfer already used by Finset, Set/Filter still
  independent). It validates both the embedding/cluster detector and the
  triage step that separates `generic_api_exists` from
  `structure_lifted_per_carrier`.
