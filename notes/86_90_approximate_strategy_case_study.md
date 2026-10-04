# 86–90 — Approximate proof-strategy matching: case study and freeze

**Hypothesis under test.** The information needed for cross-theory
proof-strategy correspondence is present in the proof terms but obscured
by superficial syntactic differences; approximate structural matching
should recover it.

## What was built

- **86 — normalized proof representation** over the 282,971 raw theorem
  skeletons (166,948 real theorems after the canonical helper filter):
  leaves B/F/M→V, Ln/Ls→N/S, PRIV→G; projection indices erased;
  interval endpoint constants→P and endpoint suffixes of lemma names
  stemmed (`image_castAdd_Icc`→`image_castAdd_#`); small coercion
  idioms→C; small min/max endpoint constructions→P; `id` wrappers and
  unused lets removed. Two layers emitted: `norm` (identity kept) and
  `core` (C/P pruned, app spines collapsed).
- **87 — positive controls**: the 73 Fin interval wrapper proofs (the
  family that split into 41 fine keys in script 79), the 32 bundled
  category dualEquiv lemmas, and to_additive twins. Exact `core` match
  cannot reunite any family (40 distinct cores among 73; 32 among 32)
  but produces zero noise.
- **88 — two matcher designs**:
  - v1 rare-stem blocking (≥2 shared K stems, document frequency ≤20):
    22,781 matches; control gate failed (Fin 13%, Dual 3%, Twin 0.1%).
    Same-strategy proofs share *common* structure, not rare lemmas.
  - A direct probe showed stemmed **token-multiset cosine is 0.91–1.0
    across the Fin family**, so v2 blocked with 64-bit Charikar simhash
    in 8 bands, gates cos(T) ≥ 0.80 and cos(H) ≥ 0.55.
  - v2 produced **550,975 matches (264,035 cross-area)** while still
    failing the gate: Fin 20.5% coverage with the largest component
    99.9% outsiders; Dual 6.2%; Twin 7.8%.
- **89 — bounded adjudication**: 90 top/random cross-area samples plus
  a 400-pair random census. **99.3–99.6% of shared tokens are generic
  idiom vocabulary** (structural leaves or K tokens shared by ≥100
  proofs). The only rare-token matches (3 pairs sharing
  `some_injective`) are the *already-known* option-tag family
  (OnePoint/WithTop/WithZero/WithOne — the type-tag constructions from
  the script-66 campaign). Concrete failure mechanism documented:
  small computational/decidability proofs normalize to identical tiny
  generic shapes, e.g. `(L KNat (A G V))`, because the mathematical
  content lives in the statement and in private automation, not in the
  retained value.

## Verdict — outcome C

**The proposed normalized proof representation is inadequate for
cross-theory strategy discovery at this extraction layer.** Both matcher
variants fail the pre-stated gate:

```
                 rare-token view      common-token view
precision            high                 catastrophic (99%+ idiom)
control recall      ~zero                 ~20% even under flooding
```

There is no threshold regime at which the features separate "shared
mathematical strategy" from "shared Lean proof idiom." That distinction
is not encoded structurally at this layer: it requires the statement
semantics and the *role* of each referenced lemma (which private lemma
carries the argument, which type drives the construction). Keeping
names/types fragments the matches; normalizing them erases the signal.

This is the third audited result on the proof representation and it
closes the exact/approximate structural line:

| campaign | result |
|---|---|
| 75–76 within-family pilot | positive (Fin family recovered coarsely) |
| 77–79 cross-area exact signatures | null; granularity boundary |
| 80–85 within-theory anomalies | null; weight/API only |
| 86–90 approximate matching | **outcome C; representation inadequate** |

## Freeze and next direction

Per the pre-stated plan, no further matcher tuning, no learned proof-tree
embeddings (they would only make the idiom/strategy distinction less
auditable), and no revival of the 70+ GB full proof dump. Structural
mining of the mature Mathlib corpus is now comprehensively mapped:
declaration/type/API level provisionally saturated (two positives, two
nulls), proof level exhausted at four representational settings.

The next campaign moves to a fundamentally different data regime:
**underdeveloped/frontier corpora**, where humans have not yet finished
organizing the structure — consistent with the standing observation
that semantic methods have the most leverage where structure is
incomplete. That campaign is not started here.
