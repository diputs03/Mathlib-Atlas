# 38 — Namespace / module / theory structure (plan item 11)

## Question
The transfer note (§4, §27) insists that **module, namespace and theory are three
different things**. Item 11 makes that distinction quantitative over the whole
corpus and locates where the three partitions diverge.

* **Module** — source file, from environment provenance (`env.getModuleIdxFor?`),
  e.g. `Mathlib.NumberTheory.Divisors`.
* **Namespace** — the name prefix a declaration is opened inside (`Nat`, `Set`,
  `Finset`, …), which can be opened across many files and nested.
* **Theory** — a coherent conceptual body; it may span many modules *and* many
  namespaces, and one module may mix many namespaces.

Input: `atlas_features.jsonl` (name/namespace/module/kind for every decl).
Area = the segment after `Mathlib` in the module path (32 areas).

## Headline counts (574,391 Mathlib declarations)
| layer | count |
|---|---|
| modules | **8,287** |
| full (possibly nested) namespaces | **100,229** |
| root namespaces | **10,972** |
| top-level decls (no namespace) | 34,951 |

There are **more root namespaces than modules** (10,972 vs 8,287) and ~12× as
many fully-qualified namespaces — already proof that namespace and module are
not the same partition. Namespace depth peaks at 1–2 (210,582 / 205,776) with a
thin tail to depth 15.

## Namespaces spread across areas (portable abstractions)
How many of the 32 top-level areas a single root namespace appears in:

| #areas | 1 | 2 | 3 | ≥3 total | max |
|---|---|---|---|---|---|
| #root-namespaces | 10,146 | 458 | 158 | **368** | 19 |

So 92% of root namespaces are local to one area, but a core of **368 portable
abstractions** cut across ≥3 areas. The most cross-cutting:

| root | areas | modules | decls | dominant-area share |
|---|---|---|---|---|
| Function | 19 | 217 | 3,338 | 0.36 (evenly spread) |
| Nat | 18 | 247 | 6,091 | 0.56 |
| Finset | 17 | 243 | 8,920 | 0.45 |
| Equiv | 17 | 167 | 4,124 | 0.35 |
| Fin | 17 | 69 | 2,475 | 0.44 |
| List | 16 | 152 | 6,284 | 0.88 (mostly Data) |
| Set | 15 | 331 | 10,471 | 0.45 |
| CategoryTheory | 14 | 1,229 | 83,722 | 0.90 (self-contained) |

`Function`/`Equiv` are the most *uniformly* cross-cutting (no dominant area),
i.e. genuine theory-independent machinery; `List` and `CategoryTheory` are large
but mostly stay in their home area.

## Modules mix many namespaces
Distinct root namespaces per module: 3,890 modules contain exactly one root,
1,454 contain two, with a long mixed tail. The most mixed:

| module | ns-roots | decls |
|---|---|---|
| GroupTheory.OrderOfElement | 95 | 581 |
| Order.Bounds.Basic | 87 | 419 |
| Analysis.CStarAlgebra.CFC.Unital | 80 | 558 |
| Order.Heyting.Basic | 79 | 497 |
| Algebra.Group.Basic | 75 | 546 |

A single "basic" file routinely pulls in dozens of concept namespaces — the
module is a *topic file*, not a namespace container.

## Theory ≠ both: the area rollup
An area (the closest directory-level proxy for a "theory") bundles namespaces and
modules in strikingly different regimes:

| area | decls | modules | namespace roots |
|---|---|---|---|
| Algebra | 101,414 | 1,344 | **2,252** |
| CategoryTheory | 77,929 | 1,099 | **115** |
| Analysis | 51,069 | 797 | 2,130 |
| Topology | 48,514 | 683 | 2,233 |
| Data | 44,751 | 632 | 517 |

Algebra/Topology/Analysis reach across *thousands* of concept namespaces (broad,
many-concept theories), whereas CategoryTheory has comparable size but only 115
namespace roots (a few deeply-developed concepts). Organization regime is itself
a structural signal.

## Concrete namespace↔module divergence
Declarations whose concept-namespace sits in a different area than their file:
* `Nat.one_mem_properDivisors_iff_one_lt` — namespace **Nat**, module
  **Mathlib.NumberTheory.Divisors** (the canonical transfer-note example, confirmed).
* `Set.MapsTo.smul_setₛₗ` — namespace **Set**, module **GroupTheory…Pointwise**.
* `Real.contDiffAt_rpow_of_ne` — namespace **Real**, module
  **Analysis.SpecialFunctions.Pow.Deriv**.
* `Set.sdiff_singleton_eq_self` — namespace **Set**, module **Order.BooleanAlgebra.Set**.

These confirm why provenance must come from the environment, never from the
name prefix: a `Nat.*` theorem is not necessarily in a `Data.Nat` module.

## Consequence for Atlas
* Provenance layer must keep **three keys per declaration** (module, namespace,
  inferred theory/area), not collapse them.
* The 368 cross-area namespaces are the natural "bridge concept" list and a
  strong prior for the theory-bridge / analogy work (16–33): cross-cutting roots
  like `Equiv`, `Set`, `Finset` are exactly where shared structure is expected.
* Directory area is only a first approximation of theory; CategoryTheory's
  low-namespace-root regime vs Algebra's high-root regime shows that theory
  coherence cannot be read off either module count or namespace count alone —
  it must ultimately be inferred from types/relations (later plan items).

## Verification & files
Independent `verify_namespace_structure.py` rebuilds both aggregations, checks
headline counts, conservation (decls summed over namespaces / modules / areas
all = 574,391), row-by-row bijection and deterministic sort → VERIFICATION OK.
* `script/python/38_namespace_theory_structure.py`
* `script/python/verify_namespace_structure.py`
* `data/namespace_structure_summary.json`, `data/namespace_crosscutting.jsonl`
  (10,972 rows), `data/module_namespace_mix.jsonl` (8,287 rows)
