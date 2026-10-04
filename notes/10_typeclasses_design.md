# 10 — Typeclass / instance structure

## Purpose

Scripts 07–09 treat every declaration uniformly (nodes, edges, expression
roles). Script 10 extracts the **typeclass layer** specifically, using Lean's own
environment extensions rather than guessing from names:

1. the **class hierarchy** — every registered class, its direct superclasses
   (`extends` parents), projection fields and out-parameter positions;
2. the **instance registry** — every `@[instance]`, the canonical class it
   implements, the type constructor it instantiates that class on, its priority
   and attribute kind.

This is a *reference layer* spanning core / Std / Mathlib (Mathlib's algebra
rests on core classes like `Inhabited`, `Decidable`, `Coe`), so all classes and
instances are emitted even though the main corpus (07) is Mathlib-only. Every
row still carries its source `module` and a `mathlib` flag for filtering.

## Verified Lean 4.34.0-rc2 API

All confirmed by compiling against the toolchain core source and a prelude
probe (`Lean.Class.lean`, `Lean/Meta/Instances.lean`, `Lean/Structure.lean`):

- Classes: `(Lean.classExtension.getState env).outParamMap.toList` gives
  `(className, outParams : Array Nat)`; `Lean.isClass env n : Bool`.
- Parents / fields: `Lean.getStructureInfo? env n` → `.parentInfo`
  (each `{structName, subobject, projFn}`) and `.fieldNames`.
- Instances: `(Meta.instanceExtension.getState env).instanceNames.toList` gives
  `(instName, InstanceEntry)` with `.priority`, `.attrKind`, `.globalName?`.
  An `InstanceEntry` has **no class field** — the implemented class is read
  structurally: peel binders off the instance's own type and take the
  application-spine head. `Meta.isInstanceCore env n` also exists.
- Prelude alone (`import Lean`) already contains 418 classes / 9,851 instances.

## The abbrev-alias subtlety (important)

A first full run found 2,487 instances whose head was **not** in
`classExtension`, and 09's constraints named 251 such classes
(`DecidableEq`, `FunLike`, `FiniteDimensional`, `CategoryTheory.SmallCategory`,
`DecidablePred`, `IsFractionRing`, …). A targeted probe proved these are all
`abbrev` definitions, not `class` declarations, so they are never registered in
`classExtension`:

| raw head (abbrev)              | canonical class it unfolds to        |
|--------------------------------|--------------------------------------|
| `DecidableEq`/`DecidablePred`/`DecidableRel` | `Decidable`            |
| `FunLike`                      | `DFunLike`                           |
| `FiniteDimensional`            | `Module.Finite`                      |
| `CategoryTheory.SmallCategory` | `CategoryTheory.Category`            |
| `CategoryTheory.Limits.HasPullbacks` | `CategoryTheory.Limits.HasLimitsOfShape` |
| `IsDirectedOrder`              | `IsDirected`                         |
| `AddLeftMono`                  | `CovariantClass`                     |
| `IsFractionRing`               | `IsLocalization` → (chain) …         |

Mechanism: a `defnInfo` with `hints = .abbrev` has a value that, after peeling
`forallE` **and** `lam`/`letE` binders (peeling only `forallE` leaves the
`fun α => …` wrapper and misses the head), has a registered class as its head.
Chains exist (`IsFractionRing → IsLocalization → …`), so resolution is a bounded
fixed point (`atlasAliasMaxHops = 8`).

The extractor therefore:
- resolves every instance head to its **canonical** class (`className`), and
  records the raw name separately as `classAlias` when it differed;
- emits one extra class row per abbrev that resolves to a class, with
  `isAlias=true`, `aliasOf=<canonical>`, empty fields/parents/outParams and
  `nInstances` = number of instances stated *via that alias*.

## Output schemas

### `data/atlas_classes.jsonl` — one row per canonical class or alias

| field       | meaning |
|-------------|---------|
| name        | class / alias name |
| module      | source module from `getModuleIdxFor?` (or null) |
| mathlib     | module starts with `Mathlib` |
| isAlias     | true for an abbrev alias, false for a registered class |
| aliasOf     | canonical class when `isAlias`, else null |
| hasStructure| `getStructureInfo?` succeeded |
| outParams   | positions of `outParam` arguments |
| fields      | projection field names |
| parents     | direct `extends` parents: `{name, subobject, projFn}` |
| nInstances  | canonical: instances resolving here; alias: via that alias |

### `data/atlas_instances.jsonl` — one row per registered instance

| field       | meaning |
|-------------|---------|
| name        | instance declaration name |
| module      | source module (or null) |
| mathlib     | module starts with `Mathlib` |
| className   | **canonical** implemented class (null only if unresolvable) |
| classAlias  | raw abbrev head when different from `className`, else null |
| targetHead  | head const of the class's first argument (best-effort; the type the instance is *for*), null when that argument is a variable/non-const |
| priority    | instance priority |
| attrKind    | global / scoped / local |

## Full-run results (Lean 4.34.0-rc2, Mathlib bbcd1968)

- **2,422 canonical classes** (1,991 Mathlib); **326 abbrev aliases** → 2,748
  class rows. 613 classes have parents (1,049 parent edges; 3 edges go to a
  plain non-class structure — `IsLocalization'→Submonoid.IsLocalizationMap`,
  `GroupFilterBasis`/`AddGroupFilterBasis→FilterBasis` — which is legitimate).
- **43,221 instances** (33,215 Mathlib), all `global`; **2,487 stated via an
  abbrev alias; 0 unresolvable** (was 2,487 before alias resolution).
- 274 canonical classes declare outParams; 2,413/2,422 have structure info.
- Largest classes by instance count: `SizeOf` 3,732, `Inhabited` 2,104,
  `Decidable` 1,004 (folds in all `Decidable*` aliases), `IsIso` 448, `Repr`
  441, `BEq` 352, `IsScalarTower` 336, `SMul` 335.
- Most-instantiated target types: `Subtype` 1,369, `Prod` 542, `Set.Elem` 447,
  `Nat` 392, `Functor` 326, `Int` 299.
- Priorities: 41,350 at default 1000; 1,429 at 100; the rest scattered.
- Cross-check vs 09: of 2,341 distinct classes appearing in type skeletons'
  `constraints`, 2,340 resolve in this registry and the remaining one is the
  built-in marker `outParam` (58 slots; definitionally its argument, never a
  class). 961,046 constraint slots total.

## Verification

    python script\python\verify_typeclasses.py data\atlas_classes.jsonl `
        data\atlas_instances.jsonl --skeletons data\atlas_type_skeletons.jsonl

Asserts: no duplicate/malformed rows; every `aliasOf` and instance `className`
is a canonical class; every `classAlias` is a known alias;
Σ canonical `nInstances` == instances with a resolved class (43,221);
Σ alias `nInstances` == via-alias count (2,487); every 09 constraint head
resolves (apart from the `outParam` marker). Result: **VERIFICATION OK**
(`notes\10_verify.log`).

## Notes / non-goals

- Parents are **direct, one-hop** `extends` edges only; transitive superclass
  closure is a downstream derived view (consistent with 08/09).
- `targetHead` is best-effort structural, not a full target-type parse.
- Kernel/reduction is never invoked: alias resolution follows only the syntactic
  head of `abbrev` values, so it stays cheap and does not conflate definitional
  equality with a class relation.
