# 13 — Semantic / structural features (per declaration)

Script 13 produces the compact, analysis-ready **feature layer** that graph
analysis (14) and discovery experiments (15) consume. It is computed in Lean,
while both the type and the value/proof `Expr` are available, so that no large
expression text has to be re-parsed downstream. One bounded walk of the type
and one of the value yields a single feature record per Mathlib declaration.

* Extractor: `script/lean/13_features.lean`
* Verifier:  `script/python/verify_features.py`
* Output:    `data/atlas_features.jsonl` (574,391 rows, Mathlib only)

## Scope and non-scope

* **Intrinsic** features only — the shape of a declaration's own type and
  value/proof term, plus environment flags and name/namespace metadata.
* Graph-topological features (in/out degree, centrality, cluster membership)
  are deliberately left to 14, where 08/09 edges are assembled.
* No aggressive simplification: counters are kept separate (lambdas,
  applications, recursors, …) rather than collapsed, so different derived
  views can be built later.

## Bounded walker

`walkFeat` is a single recursive traversal in the same 50,000-node envelope as
08/09, returning `(Feat, nodes, depth, remainingBudget, truncated)`:

* `nodes` — Expr nodes visited; `depth` — maximum AST nesting depth.
* `consts` — total `Expr.const` occurrences; `distinct` — distinct constants.
* `lams / foralls / apps / lets / lits / projs` — constructor counts.
* `recRefs` — constants whose last name segment is one of
  `rec, recOn, brecOn, ndrecOn, ndrecOnOn, below, ibelow` (structural
  recursion/induction machinery).
* `caseRefs` — constants whose last segment is `casesOn`.

Truncation is counted and flagged per layer (`typeTruncated`,
`valueTruncated`), never silent. The type's outer-Pi spine is peeled separately
(`peelPis`) for binder counts by `BinderInfo` and the conclusion head, exactly
as in 09; the value's binders are peeled (`peelBinders`) only to locate its
body head.

## Reflexivity / definitional-equality signal

A central Atlas distinction is a theorem closed by **definitional equality**
(`rfl`) versus one that applies a **named lemma**. After peeling the value's
binders, `valueHead` is the head constant of the body and `valueIsRfl` is true
when that head's last segment is `rfl` (covers `rfl`, `Eq.refl`, `Iff.rfl`,
`HEq.rfl`, …). This is *not* a hidden theorem edge (kernel conversion is not a
declaration dependency); it is an intrinsic proof-style feature.

## Schema (36 fields)

Identity / metadata:
`name, kind, module, namespace, nameDepth`.

Type shape:
`typeNodes, typeDepth, typeConsts, typeDistinct, nPi, nDefault, nImplicit,
nStrictImplicit, nInstImplicit, conclusionHead, typeTruncated`.

Value/proof shape (zeroed / null when there is no value):
`hasValue, valueNodes, valueDepth, valueConsts, valueDistinct, valueLams,
valueForalls, valueApps, valueLets, valueLits, valueProjs, recRefs, caseRefs,
valueHead, valueIsRfl, valueTruncated`.

Flags:
`isClass (Lean.isClass), isInstance (Meta.isInstanceCore), isInstName (last
segment starts with "inst"), isGenerated (name contains .match_/._proof/.eq_/
.splitter/.brecOn or last segment starts with "_")`.

`namespace` is taken after `Lean.privateToUserName?` recovers private-mangled
names; the raw `name` is preserved unchanged.

## Full-run results (Lean 4.34.0-rc2, Mathlib bbcd1968)

Scanned 777,326 constants → **574,391 Mathlib feature rows**; extraction
8,302,047 ms (~138 min, excl. import); total elapsed 9,139 s.

Kinds: theorem 444,432 · definition 116,091 · inductive 4,068 · constructor
5,099 · recursor 4,071 · opaque 630 (sum = 574,391). Exactly 561,153 have a
value; the 13,238 without are precisely inductives+constructors+recursors
(4,068+5,099+4,071).

* Reflexivity-closed proofs: **27,185**.
* Truncated walks: type **2,535**, value **26,908** (same envelope as 08/09).
* `isClass` **1,991** and `isInstance` **33,215** match script 10's Mathlib
  class/instance counts exactly (1,991 canonical Mathlib classes; 33,215
  Mathlib instances) — independent corroboration of both extractors.
* Generated-name heuristic flags 216,838 declarations.

Distributions (median / p90 / p99 / max):

| field | median | p90 | p99 | max |
|---|---|---|---|---|
| typeNodes | 143 | 1,407 | 21,451 | 50,000 |
| valueNodes | 305 | 12,779 | 50,000 | 50,000 |
| nPi | 6 | 13 | 23 | 98 |
| typeDepth | 19 | 36 | 56 | 164 |
| valueDepth | 24 | 50 | 79 | 76,309 |

## Verification

`verify_features.py` checks: required fields, unique names, exact 574,391 row
count, every module starts with `Mathlib`, the ordering
nodes ≥ consts ≥ distinct, the binder sum `nPi = nDefault+nImplicit+
nStrictImplicit+nInstImplicit`, value gating (no value ⇒ zero value fields /
null head / not rfl), truncation envelopes, and prints distributions. With
`--skeletons` it joins every row against 09's `atlas_type_skeletons.jsonl` and
requires identical binder counts, conclusion head, and type-truncation flag.

Result: **VERIFICATION OK** — 0 duplicates/malformed, all internal checks pass;
09 join matched 574,391 with 0 missing / 0 mismatches.

## Reproduce

```
lake env lean script\lean\13_features.lean
python script\python\verify_features.py data\atlas_features.jsonl `
    --skeletons data\atlas_type_skeletons.jsonl
```
