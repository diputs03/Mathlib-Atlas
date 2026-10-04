# 07 — Persistent Atlas corpus: design, schema and measured sizes

Lean toolchain: `leanprover/lean4:v4.34.0-rc2` (Windows, no WSL).
Mathlib commit: `bbcd1968ee6950abe88b85dba6995da346c4b2a8`.
Extractor: `script/lean/07_persistent_corpus.lean`.
Validator: `script/python/validate_corpus.py`.

## How to run

From the repository root (note: scripts live under `script\lean\`, not `script\`):

```
lake env lean script\lean\07_persistent_corpus.lean
```

`import Mathlib` is loaded once; the whole environment is traversed in that same
process. Configuration are the top-level `def atlas...` constants:

| flag | default | meaning |
|---|---|---|
| `atlasOutPath` | `data/atlas_corpus.jsonl` | main corpus (JSON Lines) |
| `atlasLargeExprsPath` | `data/atlas_large_exprs.jsonl` | sidecar shard |
| `atlasMathlibOnly` | `true` | keep only decls whose **source module** starts with `Mathlib` |
| `atlasLimit` | `none` | cap emitted records (`.some 5000` for a sample) |
| `atlasIncludeValue` | `true` | consider values/proofs at all |
| `atlasStoreValues` | `false` | actually store proof **terms** (opt-in; see size notes) |
| `atlasExprNodeCap` | `50 000` | Expr nodes above which a term is "oversized" and never built |
| `atlasAstInlineCap` | `64 000` | AST bytes kept inline in the main record |
| `atlasStrInlineCap` | `200 000` | pretty-string bytes kept inline |

## Main-corpus record schema (one JSON object per declaration)

Identity / provenance (from the environment, never name-prefix inference):
- `name` (string), `namespace` (name minus last component), `kind`
  (`axiom|definition|opaque|theorem|quotient|inductive|constructor|recursor`),
  `module` (source module, e.g. `Mathlib.NumberTheory.Divisors`, or null),
  `levelParams` (list of universe-parameter names),
  `isUnsafe`, `isPartial`, `hints` (`opaque|abbrev|regular`).

Type layer (always present):
- `typeStr` pretty-printed signature, `typeAst` structural encoding;
- `typeNodeCount`, `typeAstBytes`, `typeStrBytes`,
  `typeSharded`, `typeOversized`.

Value/proof layer:
- with `atlasStoreValues=false` (default): only `valueNodeCount` and
  `valueOversized` are populated (proof size is measured, term not stored);
- with `atlasStoreValues=true`: `valueStr`/`valueAst` plus
  `valueAstBytes`,`valueStrBytes`,`valueSharded`,`valueOversized`.

### Structural AST

Every `Expr` constructor is encoded faithfully: `bvar` (de Bruijn index),
`fvar`,`mvar`,`sort` (with structured universe `Level`), `const` (name + list of
universe levels), `app`, `lam`/`forallE` (binder name + `BinderInfo` + type +
body), `letE` (incl. `nonDep`), `litNat`/`litStr`, `mdata`, `proj`. Nothing is
flattened to a name prematurely.

## Size tiers (applied uniformly to type and value)

1. **inline** — AST ≤ `atlasAstInlineCap` and string ≤ `atlasStrInlineCap`:
   both live in the main record.
2. **sharded** — node count ≤ cap but too large to inline: the FULL expression
   is written to the sidecar keyed by `(name, slot)` (`slot` = `type|value`),
   carrying only the withheld piece (no duplication); main keeps counts/flags
   and whichever piece was small enough.
3. **oversized** — node count > cap: the bounded counter `sizeWithin` visits at
   most the cap's nodes and then gives up; the term is never built or
   pretty-printed (a single Mathlib proof term is ~1.6 GB / tens of millions of
   nodes). Main records `...Oversized=true` and a sentinel node count.

Nothing is dropped silently: an oversized term is still *known* and can be
extracted on demand later.

## Measured sizes (COMPLETE full run)

Environment totals from `06_module_statistics`:
**574,391 Mathlib declarations across 8,287 modules** (of 777,282 total constants
scanned).

Raw elaborated terms have an extreme heavy tail: the median record is ~8 KB, but
structural ASTs are ~3.7x the size of pretty strings, and one
`Rep.indCoindIso._proof_2` term alone serializes to 1,595 MB.

The complete default (signature-layer) extraction, verified with
`script/python/verify_full_corpus.py` (**VERIFICATION OK**):

| output | records | size |
|---|---|---|
| `data/atlas_corpus.jsonl` (main) | 574,391 (all names unique) | 9.9 GB (p50 8 KB, max 200 KB) |
| `data/atlas_large_exprs.jsonl` (sidecar) | 51,738 (all `type`) | 16.2 GB |

Kind distribution: 444,432 theorems; 116,091 definitions; 5,099 constructors;
4,071 recursors; 4,068 inductives; 630 opaques.
Tiering: 51,738 declarations had a large type AST moved to the sidecar; 2,535
had an oversized type (> 50k nodes, not built); 26,907 had an oversized proof
term (measured via node count only, since `atlasStoreValues=false`). Every
sharded main record has exactly one matching sidecar entry and vice-versa
(0 orphans each way); every main record has a `Mathlib.*` source module.

Layer-size projections from a 5,000-declaration sample (why the default is the
signature layer):

| layer | projected full size |
|---|---|
| metadata only | ~0.3 GB |
| + pretty type signatures (`typeStr`) | ~4.4 GB |
| + structural types (`typeAst`)  ← default main corpus | ~9.5 GB (measured 9.9) |
| + pretty proof terms (`valueStr`) | ~17.3 GB |
| + structural proof terms inline | ~22.6 GB (remaining heavy tail → sidecar, tens of GB) |

Flip `atlasStoreValues := true` to also preserve full proof terms (opt-in; much
larger).

## Runtime

The complete run scanned 777,282 constants and wrote 574,391 records + 51,738
sidecar records in **5,589 s (~93 min) wall-clock** on this machine, most of
which is traversal/encoding (the one-time `import Mathlib` is a few minutes).
Streaming to file handles keeps memory bounded (~3 GB working set). A bounded
5,000-record run takes ~2–2.5 min and is the fast way to iterate.
