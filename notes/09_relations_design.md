# 09 — Richer Expr relationships

Extractor: `script/lean/09_expr_relations.lean`
Outputs:
* `data/atlas_relations.jsonl` — role-labelled reference relations
* `data/atlas_type_skeletons.jsonl` — per-declaration type skeleton
Verifier: `script/python/verify_relations.py` (reconciles against 08 edges)

## Motivation

08 records *that* constant B occurs in declaration A (type vs value, with
multiplicity). 09 records the **structural role** of each occurrence without
discarding anything: it is a strictly finer, lossless decomposition of the same
`Expr.const` references. The four type-role counts on a relation row sum to
08's `typeCount`, and the four value-role counts sum to `valueCount`.

## Role axes

Two context bits are threaded through the bounded expression walk:

* **isHead** — the constant is at the head of an application spine
  (follow `.app.fn`); arguments lose head status.
* **inBinder** — the occurrence is inside the type of a `forallE`/`lam` binder
  (a hypothesis/constraint) rather than the main conclusion/body reached after
  peeling binders.

Their 2×2 product, per layer:

| role | type meaning | value/proof meaning |
|---|---|---|
| `headMain` | head of the conclusion (`Eq`, `Iff`, `LE.le`, `Membership.mem` …) | lemma/constructor applied as a proof step |
| `argMain` | appears in the conclusion term, not its head | passed as an argument |
| `headBinder` | head of a hypothesis type (`Group` in `[Group G]`) | head of a lambda-intro hypothesis type |
| `argBinder` | nested inside a hypothesis type | nested in a lambda binder type |

### Relation row schema (`atlas_relations.jsonl`)

`source, target, targetKind, isSelf`, then eight counts:
`typeHeadMain, typeArgMain, typeHeadBinder, typeArgBinder,
valueHeadMain, valueArgMain, valueHeadBinder, valueArgBinder`.
One row per ordered `(source,target)` (same pairing as 08).

## Type skeleton (`atlas_type_skeletons.jsonl`)

For each declaration we peel only the OUTER `forallE` spine (the declaration's
own parameters/hypotheses):

| field | meaning |
|---|---|
| `name, kind, module` | provenance (module from the environment) |
| `nPi` | number of outer binders |
| `nDefault / nImplicit / nStrictImplicit / nInstImplicit` | binders by `BinderInfo` (`nPi` = their sum) |
| `constraints` | `[{class, count}]` — head constant of every `instImplicit` binder, i.e. the typeclass constraints `[Foo …]` the declaration assumes (read from binders, not the instance attribute) |
| `conclusionHead` | head constant of the conclusion after the outer binders, or null |
| `typeRolesTruncated / valueRolesTruncated` | bounded-walk flags |

`conclusionHead` is the relation/predicate a theorem establishes; `constraints`
is the exact set of typeclass hypotheses. Together they are high-signal
features for 10 (typeclass structure), 12 (generalization families) and 13
(structural/semantic features).

## Scope / non-goals

Direct one-hop references only; transitive/axiom/reduction analyses remain
downstream (same boundary as 08). Same node-bounded traversal
(`atlasNodeBudget = 50_000`), with truncation counted per layer. Instance
*resolution* (which concrete instance was synthesized) is still not modelled —
09 captures the constraints a declaration *assumes*; the instances provided are
a separate matter for 10.

## Validation

### 5,000-declaration Mathlib sample

* 139,465 relation rows — exactly the 08 sample's edge count; 0 duplicates,
  0 bad rows; skeletons for all 5,000 (the 4 zero-reference decls have a
  skeleton but no relations, as expected).
* **Lossless refinement proven**: reconciling against the matching 08 sample,
  global type/value sums match exactly and the per-pair join over all 139,465
  pairs reports **0 mismatches** (each pair's role counts sum to 08's counts).
* 3,562 decls carry typeclass constraints (10,652 instImplicit binders).
* Conclusion heads (sample): Eq 2,224; Iff 321; LE.le 153; Membership.mem 84;
  Exists 57; null 427 (sorts/type-returning defs).
* Truncation 21 type / 232 value — identical to 08.
* Sizes: relations 36.6 MB / skeletons 1.7 MB per 5,000 → full projections
  ~4.2 GB / ~0.2 GB.

### Full run (COMPLETE, verified)

Scanned 777,315 constants; **574,391 Mathlib sources** (matches 06/07/08) in
~105 min extraction, producing **16,316,230 relation rows** (`atlas_relations.jsonl`,
4.19 GB) and **574,391 type skeletons** (`atlas_type_skeletons.jsonl`, 0.19 GB).

`verify_relations.py --edges atlas_edges.jsonl --join-prefix CategoryTheory.`
→ **VERIFICATION OK**:

* 16,316,230 relation rows, 0 duplicates / 0 bad; row count equals 08 exactly.
* **Lossless refinement proven at scale**: global sum of type roles
  126,671,357 = 08's total `typeCount`; value roles 625,704,857 = total
  `valueCount`; and the per-pair join over 1,848,210 CategoryTheory pairs has
  **0 mismatches**.
* 574,391 skeletons, 0 bad; the **839** skeletons with no relations equal 08's
  839 zero-edge declarations exactly.
* Typeclass constraints: **411,068 declarations** assume at least one
  typeclass; 1,255,032 `instImplicit` binders → 1,220,872 constraint slots.
* Conclusion heads (whole corpus): Eq 261,768; (none — sort/type-returning)
  47,011; Iff 36,354; LE.le 18,825; Membership.mem 7,899; Exists 6,488;
  LT.lt 5,538.
* Role totals: type — headMain 527,372 / argMain 92,144,706 / headBinder
  4,817,823 / argBinder 29,181,456; value — headMain 545,852 / argMain
  534,003,180 / headBinder 14,203,102 / argBinder 76,952,723. Head-of-spine
  roles are deliberately sparse and high-signal; argument roles carry the
  repetition.
* Truncation 2,535 type / 26,908 value — identical to 07/08.

The Atlas now has three aligned layers: nodes (`atlas_corpus.jsonl` + large-type
sidecar), flat labelled edges (`atlas_edges.jsonl`), and role-decomposed
relations + type skeletons (09).
