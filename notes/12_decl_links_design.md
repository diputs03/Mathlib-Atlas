# 12 — Structural declaration links

## Purpose

The earlier corpora capture *occurrence* relations: 08 records that B occurs in
A's type/value, 09 labels the structural role of each occurrence, and 10 records
typeclass `extends`. Script 12 captures the **structural links the environment
itself encodes between declarations** — family membership and generated
companions that are not merely "B's term mentions A". These are the deterministic
skeleton on which later generalization/analogy analysis (13–15) can build, and
they let downstream distinguish "same inductive family" / "generated equation
lemma" / "alternate name" from ordinary proof references.

All links are **direct, one-hop and labelled** (no transitive closure,
consistent with 08–11).

## Verified Lean 4.34.0-rc2 facts

From toolchain source (`Lean/Declaration.lean`, `Lean/Meta/Eqns.lean`,
`Lean/ResolveName.lean`, `Lean/Structure.lean`), confirmed by a compiled probe:

- `ConstantInfo.inductInfo v`: `v.ctors : List Name`, `v.all : List Name`
  (mutual block), `numParams/numIndices`; there is **no** `v.rec` field — the
  recursor name is the conventional `Name.str name "rec"`, used only when
  `env.contains` confirms it.
- `.ctorInfo v`: `v.induct` (owning inductive), `v.cidx`, `v.numFields`.
- `.recInfo v`: `v.all` (covered inductives), `v.rules` (each `.ctor`),
  `v.getMajorInduct`.
- Equation lemmas: `Lean.Meta.declFromEqLikeName env name` is a **pure** inverse
  returning `some (parent, suffix)` for `eq_1/eq_2/…` and the `eq_def`/
  `eq_unfold` unfolding lemmas. It also recovers **private-mangled** equation
  lemmas (it tries both the name and `privateToUserName`).
- Aliases/exports: `Lean.getAliasState env : SMap Name (List Name)` maps an
  alias name to its canonical declaration(s) (covers both `alias` and
  `export … (…)`).
- Structure layout: `getStructureInfo?` gives `parentInfo` (`.structName`,
  `.subobject`) and `fieldInfo` (`.fieldName`, `.projFn`).
- A nested match on `some (.inductInfo v)` fails to elaborate; bind `some ci`
  then match `ci`. A `let mut` cannot be mutated inside a closure, so the row
  writer is a top-level IO def and the closure only writes.

## Relation labels

| relation         | direction | meaning |
|------------------|-----------|---------|
| `constructor`    | inductive → ctor | one of its constructors |
| `memberInductive`| ctor → inductive | inverse of the above (carries cidx in `detail`) |
| `recursor`       | inductive → recursor | its `.rec` (when present) |
| `recursorOf`     | recursor → inductive | inductive(s) in its mutual block |
| `recursorRule`   | recursor → ctor | one reduction rule per constructor |
| `mutualInductive`| inductive → inductive | other members of a mutual block |
| `structExtends`  | structure → parent structure | `extends` for **all** structures (`detail`="subobject" when bundled) |
| `projection`     | structure → proj. function | one per field (`detail`=field name) |
| `equationLemma`  | definition → `eq_N` | generated equational theorem |
| `unfoldLemma`    | definition → `eq_def`/`eq_unfold` | unfolding lemma |
| `alias`          | alias/export name → canonical | same declaration, alternate name |

Row schema (`data/atlas_decl_links.jsonl`):
`{source, target, relation, detail, module, mathlib}` where module/mathlib
describe the **source**.

## Full-run results (Lean 4.34.0-rc2, Mathlib bbcd1968)

777,233 constants scanned → **80,374 links** (48,375 Mathlib-tagged), 40,536
distinct sources / 58,106 distinct targets:

| relation | count | | relation | count |
|---|--:|---|---|--:|
| constructor | 9,627 | | recursorRule | 9,808 |
| memberInductive | 9,627 | | structExtends | 1,640 |
| equationLemma | 17,850 | | unfoldLemma | 1,663 |
| projection | 15,156 | | mutualInductive | 222 |
| recursor | 6,835 | | alias | 639 |
| recursorOf | 7,307 | | | |

- 16,481 declarations have equation/unfolding lemmas; 5,779 structures have
  projections; 1,119 structures extend another.
- 6,835 inductives have a recursor (script 11 counted 6,837 inductives; the
  remaining two have no `.rec`). `recursorOf` (7,307) exceeds the inductive
  count because mutual-block recursors point at every member of the block.
- 181 `recursorRule` edges target constructors of **nested** types
  (`List.cons`, `Array.mk`, `Prod.mk`, …) appearing inside the recursed type —
  legitimate, reported separately by the verifier.

## Verification

    python script\python\verify_decl_links.py data\atlas_decl_links.jsonl `
        --classes data\atlas_classes.jsonl

Asserts: unique well-formed rows; correct mathlib flags; perfect
constructor↔memberInductive and recursor↔recursorOf symmetry; every
recursorRule target is a real constructor; equation/unfold suffix consistency;
no self-alias; projections carry a field name; extends detail valid. The
`--classes` cross-check confirms **all 1,049 class parent edges from script 10
appear as `structExtends` links here (0 missing)**. Result: **VERIFICATION OK**
(`notes\12_verify.log`).

## Non-goals

- No transitive family closure and no semantic generalization detection (same
  statement under weaker assumptions) — that is a 13/15 feature/clustering task.
- Body/proof references remain exclusively in 08/09; this file is only the
  environment-encoded structural skeleton, so the two edge kinds stay separate
  rather than being collapsed.
