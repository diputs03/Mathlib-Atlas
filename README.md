# Mathlib Atlas

**Turning Lean's Mathlib into computationally analyzable data for
mathematical discovery.**

Mathlib Atlas loads the entire Mathlib environment, preserves the raw
formal structure (types, proof terms, references, provenance), and runs
adjudicated discovery experiments over it: structural and semantic
detectors propose analogies, missing abstractions, and anomalies; Lean's
kernel then verifies or falsifies every claim downstream.

The long-term objective is not a dependency database. It is to treat a
large formalized mathematical corpus as data, and use its structure to
find new abstractions, relationships, conjectures — and eventually new
mathematics — with kernel verification as the correctness boundary:

```
Mathlib → extraction → formal corpus / graphs / expressions
       → structural + relational + semantic features
       → pattern discovery → clusters / anomalies / analogies / gaps
       → human / AI reasoning → hypotheses
       → formalization → kernel verification → new mathematics
```

## Key facts

- **Corpus:** 574,391 declarations, 8,287 modules, 32 top-level areas,
  16.3 million distinct labeled reference edges; raw Expr retained.
- **Environment:** Windows, no WSL; Lean 4.34.0-rc2; Mathlib pinned at
  commit `bbcd1968`.
- **Method:** one expensive `import Mathlib` process, many extraction
  passes; every detector output is treated as a hypothesis and falsified
  against Lean (exit 0 and zero-byte compile log, no `sorry`).
- **Discipline:** module ≠ namespace ≠ theory; provenance comes from the
  environment, never from name prefixes; edge labels stay separate;
  null results and false positives are recorded as carefully as
  positives.

## Headline results

- **PointwiseLift:** `Set.image2` and `Filter.map₂` are two independent
  realizations of the same pointwise binary lift; a unifying abstraction
  is a genuine design opportunity.
- **Orphan Functors:** six type constructors (Sym2, WithBot, WithTop,
  OnePoint, Stream', Cycle) have a hand-written `map` but no registered
  `Functor` — 6/6 verified downstream as clean omissions.
- **Observability boundary:** five audited campaigns show the mature,
  highly curated corpus is almost perfectly factored at declaration/type/
  API level, and map the exact limits of proof-strategy discovery at the
  current representation layer.
- A kernel-verified planar-combinatorics spine (crossing lemma,
  Szemerédi–Trotter → u(n) = O(n^{4/3}), combinatorial maps, χ ≤ 2,
  incidence chain complex) is built and frozen.

See **[docs/RESULTS.md](docs/RESULTS.md)** for the full findings and
**[docs/ROADMAP.md](docs/ROADMAP.md)** for status and next steps.

## Repository layout

```
Mathlib-Atlas/
├── docs/                 # results and roadmap
├── notes/                # case studies, freeze notes, design memos
│   ├── discovery_track_consolidated.md   # living narrative
│   └── execution.txt                     # execution ledger
├── script/
│   ├── lean/             # downstream kernel-verification experiments
│   └── python/           # extractors, matchers, verifiers
├── data/                 # generated corpus layers (bulk data)
├── external/mathlib4/    # pinned Mathlib — READ ONLY
├── lean-toolchain
└── README.md
```

## Reproducing an experiment

Lean experiments compile downstream without touching Mathlib:

```powershell
lake env lean script\lean\<experiment>.lean
```

Python tooling uses the standard library only; each campaign ships an
independent verifier (e.g.
`script\python\verify_approximate_strategy_campaign.py`) which must pass
before the campaign is closed.
