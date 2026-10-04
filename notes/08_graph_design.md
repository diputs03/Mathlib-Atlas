# 08 — Persistent labelled dependency graph

Extractor: `script/lean/08_dependency_graph.lean`
Output: `data/atlas_edges.jsonl` (JSON Lines, one edge per line)
Verifier: `script/python/verify_edges.py`

## What this graph is

The **direct, named-declaration** dependency graph of Mathlib. For every Mathlib
declaration `source`, we walk its type and its value/proof term
(`ConstantInfo.value? true`) and record one edge for every distinct constant
`target` reached via an `Expr.const`. These are one-hop references exactly as
they appear in the elaborated kernel term.

This is instrumentation for discovery, not a reduction of mathematics to
name-pairs: the edges are *labelled* and kept separate (transfer note §18–21).

## Edge schema

One record per ordered `(source, target)`:

| field | meaning |
|---|---|
| `source` | Mathlib declaration name |
| `target` | referenced constant name |
| `inType` | bool — target occurs in the source's **type** |
| `inValue` | bool — target occurs in the source's **value/proof body** |
| `typeCount` | occurrence multiplicity inside the type |
| `valueCount` | occurrence multiplicity inside the value/proof |
| `targetKind` | target's `ConstantInfo` kind: axiom/definition/opaque/theorem/quotient/inductive/constructor/recursor, or `unknown` |
| `isSelf` | source == target (recursive definitions / well-founded fixpoints) |

The two layers (`inType` vs `inValue`) are kept as independent flags with their
own multiplicities rather than collapsed into a single "depends on".

## What is deliberately NOT here (derived later, not conflated)

* **Transitive closure** — graph algorithm over these edges.
* **Axiom dependency** (`#print axioms`) — transitive reachability to `axiom`
  nodes; derivable by closure restricted to `targetKind = axiom`.
* **Definitional / reduction dependency** — kernel conversion is *not* a hidden
  theorem edge and is intentionally absent.
* **Instance dependency** — a typeclass instance is a def/theorem carrying the
  `instance` attribute. 4.34.0-rc2 has no clean "is this name an instance"
  predicate; rather than guess, instance edges are deferred to a later join
  against an instance list. Constructor/recursor/inductive dependencies are
  already captured via `targetKind`.

## Scope

* Sources are filtered to `Mathlib.*` **source modules** via the environment
  (`getModuleIdxFor?`), never name prefixes. Edges may point at core/Batteries
  targets (the boundary is visible through `targetKind` and the corpus).
* Self-edges are kept.

## Bounded traversal (why and how)

Elaborated proof terms have an extreme heavy tail (one 07 term reached 1,595 MB
/ tens of millions of nodes). Reference collection is therefore node-bounded by
`atlasNodeBudget = 50_000` per expression: beyond it, traversal stops and the
source is counted as truncated (`Sources w/ truncated type/value refs`). At
50k nodes every distinct target is essentially always reached; only
multiplicity on repetitive generated terms is affected, and truncation is
reported, never silent. A 2,000,000 budget was tried and rejected: it retained
only ~4% more edges but made extraction ~5x slower.

## Configuration knobs (top of the Lean file)

`atlasEdgesPath`, `atlasMathlibOnlySources` (default true), `atlasLimit`
(none = full / some N = sample), `atlasIncludeValueEdges` (default true),
`atlasNodeBudget` (default 50_000).

## Measured results

### 5,000-source Mathlib sample (validation)

* 5,000 Mathlib sources → 139,465 unique edges (0 duplicates, 0 inconsistent);
  4,996 sources had ≥1 outgoing edge.
* Extraction (excluding `import Mathlib`): **32.6 s** → full run projects to
  ~60–65 min of extraction.
* Layer mix: value-only 59,092; both 67,726; type-only 12,647.
* Out-degree: p50 = 20, p90 = 57, p99 = 128, max 308, mean 27.9.
* Truncated at 50k: 21 type / 232 value sources (rates match 07's oversized
  counts).

### Full run (COMPLETE, verified)

Scanned 777,240 constants; **574,391 Mathlib source declarations** (matches
scripts 06/07 exactly) producing **16,316,230 unique edges** in
`data/atlas_edges.jsonl` (2.89 GB). Extraction (excluding import) took
8,018 s (~134 min).

`verify_edges.py --corpus` → **VERIFICATION OK**:

* 16,316,230 edges, 0 duplicate `(source,target)`, 0 inconsistent records,
  0 unresolved (`unknown`) targets, **0 edge sources absent from the 07 corpus**.
* 573,552 of 574,391 corpus nodes have ≥1 outgoing edge; the 839 with none are
  749 bare `inductive` declarations (their type is only `Sort`/universe params;
  constructor references live on the separate constructor nodes), 87 primitive
  definitions and 3 theorems — expected graph leaves.
* Self-edges: 1,009.
* Layer mix: value-only 6,823,421; both type+value 8,027,916; type-only
  1,464,893.
* Target kinds: definition 10,137,113; inductive 2,914,517; theorem 2,540,327;
  constructor 624,463; axiom 68,286; recursor 26,966; quotient 2,505;
  opaque 2,053.
* Out-degree: p50 = 21, p90 = 59, p99 = 129, max 409, mean 28.4.
* Bounded traversal truncated 2,535 type and 26,908 value walks at the 50k-node
  budget — matching 07's oversized-type (2,535) and oversized-value (26,907)
  counts, an independent cross-check of the node-bounded walk.

Together with the 07 node corpus this is the labelled declaration graph:
nodes in `atlas_corpus.jsonl` (+ large-type sidecar), edges in
`atlas_edges.jsonl`.
