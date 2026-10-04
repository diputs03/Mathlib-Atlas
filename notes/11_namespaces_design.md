# 11 — Namespace / theory-structure substrate

## Purpose

A declaration has **four distinct addresses**, which must not be conflated:

- *module* — the source file it was elaborated in (from the environment,
  scripts 05/07);
- *namespace* — the hierarchical segments of its user-facing `Name`;
- *theory* — a conceptual mathematical area, potentially spanning many modules
  and namespaces (inferred later, not here);
- the declaration itself.

Script 11 builds the deterministic **namespace** layer and, crucially, the
many-to-many **namespace↔module incidence** that measures how far the two axes
diverge — the substrate on which later "theory" clustering (13–15) can build. It
does **not** infer theories and does not derive namespace from name *prefixes
alone* for provenance: module provenance still comes from the environment; only
the namespace tree comes from `Name` structure.

## Verified Lean 4.34.0-rc2 facts

- `Name.getPrefix` drops the last segment; a single-segment name's prefix is
  `Name.anonymous` (`getNumParts = 0`). `getNumParts`, `getRoot`, `components`
  and the `getPrefix` ancestor walk all behave as expected.
- `Name.anonymous.toString` renders `[anonymous]`; the extractor maps it to "".
- Private declarations are stored internally as
  `_private.<module>.<hash>.<userName>`, which would create meaningless deep
  "namespaces". `Lean.privateToUserName?` recovers the user name for **100%** of
  private declarations (59,991/59,991 in a prelude probe); names are normalised
  with it before the namespace is derived.
- A quoted identifier `«…»` is a *single* name component even when its escaped
  spelling contains dots (one generated aux declaration is like this); the
  verifier counts segments quote-aware rather than by raw dots.

## Method

One pass over `env.constants`. For each declaration:

1. recover the user-facing name (`privateToUserName?`), take its prefix as the
   direct namespace, and materialise every missing ancestor (so the tree is
   complete even for prefixes that declare nothing directly);
2. classify the `ConstantInfo` kind (axiom / definition / opaque / theorem /
   quotient / inductive / constructor / recursor);
3. get the source module from the environment and update (a) the namespace node
   and (b) the `(namespace, module)` incidence pair; also track the reverse
   module→{namespaces} set for the mismatch summary.

## Output schemas

### `data/atlas_namespaces.jsonl` — one row per namespace node (root included)

| field    | meaning |
|----------|---------|
| name     | dotted namespace path; "" is the anonymous root |
| parent   | parent node ("" for depth-1 nodes; null for the root) |
| depth    | number of `Name` segments (root = 0) |
| root     | top-level segment (coarsest grouping) |
| nDecls   | declarations whose **direct** namespace is this node |
| nMathlib | of those, whose module starts with `Mathlib` |
| nModules | distinct source modules contributing directly |
| kinds    | direct declaration counts by ConstantInfo kind |

### `data/atlas_namespace_modules.jsonl` — one row per (namespace, module)

| field     | meaning |
|-----------|---------|
| namespace | namespace node name |
| module    | source module |
| mathlib   | module starts with `Mathlib` |
| nDecls / nMathlib | declarations in this pair |
| kinds     | counts by kind |

## Full-run results (Lean 4.34.0-rc2, Mathlib bbcd1968)

- 777,280 constants scanned → **168,662 namespace nodes** (142,436 with direct
  declarations; 26,226 pure ancestor nodes) and **170,569 incidence rows**.
- Totals reconcile exactly: Σ node `nDecls` = 777,280; global kinds
  theorem 538,153 / definition 212,618 / constructor 9,629 / recursor 6,960 /
  inductive 6,837 / opaque 3,064 / axiom 15 / quotient 4 = 777,280. Mathlib
  counts (node and pair) = **574,391**, matching 06/07. 61 prelude/helper
  constants have no module and appear only in node totals.
- Depth distribution peaks at depth 2 (65,144); max depth 26 (generated nested
  names). 11,559 depth-1 segments; note many depth-1 "namespaces" are
  top-level declaration names carrying generated children (`.proof_1`,
  `.match_1`, …) — faithful to the kernel, to be filtered when clustering.
- **Module ≠ namespace, quantified (the key result):**
  - 6,604 namespaces span more than one module (4,586 within Mathlib); the root
    spans 2,789, `CategoryTheory` 396, `Nat` 258, `Finset` 232, `List` 228;
  - 9,662 of 10,262 modules host more than one namespace (7,806 of 8,287 in
    Mathlib) — e.g. `Std.Data.DTreeMap.Internal.Lemmas` hosts 1,050 namespaces.
  This rules out treating module folders as namespaces (or vice versa).
- Largest namespaces by direct declarations: root 37,340, `List` 5,804,
  `Set` 5,725, `Finset` 5,532, `Nat` 4,939, `MeasureTheory` 4,120,
  `CategoryTheory` 3,751.

## Verification

    python script\python\verify_namespaces.py data\atlas_namespaces.jsonl `
        data\atlas_namespace_modules.jsonl

Asserts: unique nodes; the tree closes (root present, every parent exists,
parent depth = depth−1, quote-aware depth and root-segment consistency);
Σ kinds = nDecls and nMathlib ≤ nDecls; incidence pairs unique, reference a
known namespace, and carry a correct mathlib flag; Σ node decls = scanned
constants; Mathlib totals = 574,391 (node and pair). Result: **VERIFICATION OK**
(`notes\11_verify.log`).

## Non-goals

- No transitive subtree rollups are baked in (the parent tree lets downstream
  compute them); no theory inference; no name-prefix-based module guesses.
- Generated sub-names (`.proof_*`, `.match_*`, `_private`) are handled
  deterministically but left visible rather than silently deleted, consistent
  with the project's "don't discard raw structure" principle.
