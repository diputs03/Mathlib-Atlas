# Script 27 — triage of the `weak` cross-area communities (closes the 606)

## Inputs / outputs

- Inputs: the 66 `weak` rows from `data/community_triage.jsonl` (script 19)
  joined to `data/atlas_features.jsonl`.
- Script `script/python/27_weak_triage.py` (stdlib, deterministic); verifier
  `script/python/verify_weak_triage.py` → **VERIFICATION OK**.
- Outputs: `data/weak_triage.jsonl` (66 rows), `data/weak_triage_summary.json`.

## Why these were "weak"

Script 19 marks a cross-area community weak when it shares a conclusion head but
fails the stronger tests: no built class, low suffix coverage, no instances/rfl,
no infra. 60 of 66 are size-2 pairs; cosine is ≥0.90 by construction (median
0.937). The split uses the shared **value head** and affinity to the conclusion
head's own namespace.

| class | criterion | count |
|---|---|---|
| `generic_reuse` | a majority of members already call the same domain generic constructor/lemma as value head, or one member is the head's own API the other builds through | **49** |
| `mechanical_shape` | only shared value head is a logical connective / generic recursion / bind / cast / lattice op (`And.intro`, `Eq.rec`, `Iff.mpr`, `iInf`, `Bind.bind`, `HDiv.hDiv`, …) | **15** |
| `unrelated` | no shared value head and no head-API member | **2** |

### generic_reuse (49) — already abstracted
Examples: piFan family all use `Fan.mk`; ReflectsIsomorphisms pair uses
`ReflectsIsomorphisms.mk`; ShortExact pair uses `ShortExact.mk`; Fintype pair
uses `Fintype.ofFinite`; GeneralLinearGroup pair uses `mkOfDetNeZero`;
Subring pair uses `Subring.mk`; BinaryCofan pair uses `BinaryCofan.mk`;
Cardinal pair uses `Cardinal.mk`; MeasurableEmbedding pair uses
`IsOpenEmbedding.measurableEmbedding`. The differing suffixes are why script
19 did not call them "API", but the proof bodies already route through one
generic builder — same conclusion as script 26's `shared_generic_core`.

### mechanical_shape (15) — shared proof mechanics only
Pairs such as `Multiset.covBy_cons`/`Set.sdiff_singleton_covBy` (both
`And.intro`), `Nat.isLeast_nth`/`Ordinal.isLeast_…` (`And.intro`), two
elaborators (`Bind.bind`), two rational expressions (`HDiv.hDiv`),
`Dynamics.coverMincard`/`Ideal.height` (`iInf`). They share a logical skeleton
or generic operator over unrelated mathematics — embedding artifacts, not
abstractions. The closest to real is `Finset/Set.empty_covBy_singleton`
(`Eq.rec` casts), which is the Finset-via-Set transfer already characterized in
case C.

### unrelated (2)
`AddEquivClass` triple with mixed value heads, and an `Option` pair with no
value head at all — coincidental structural similarity.

**Candidate opportunities: 0.**

## Closing ledger — all 606 cross-area communities

Script 19 labels → refined by scripts 21/26/27:

| 19 label | n | refinement |
|---|---:|---|
| shared_head_analogy | 348 | script 21: mixed 244, head_api 85, repeated_proof 19, bundled_witness 0 |
| generic_api_exists | 144 | generic API already present (case B pattern) |
| structure_lifted_per_carrier | 29 | pointwise algebra; cases C/E — the one positive construction |
| weak | 66 | script 27: generic_reuse 49, mechanical_shape 15, unrelated 2 |
| pointwise_repeated | 11 | script 26: generic_core 6, type_construction 3, strategy_only 2 |
| infra | 8 | tactic/metaprogramming, excluded |
| **total** | **606** | |

### Net finding across the whole cross-area sweep
- The **only** positive, kernel-verified missing abstraction is case E: the
  Set/Filter `PointwiseLift` ladder (scripts 23–25), valid through
  `DivInvMonoid` with a proven `Group` boundary.
- Everywhere else, cross-area multiplicity is either (a) already served by a
  generic class/lemma/constructor (the dominant case: 144 generic API + 85
  head_api + 6 generic core + 49 generic reuse + 3 type constructions + case B
  Is*Apply + case D Equivalence witnesses), or (b) mathematically irreducible
  (19 repeated_proof, 2 strategy_only, 15 mechanical, 2 unrelated, and the
  structure-lifted carriers that legitimately differ).
- This is strong evidence the embedding/triage pipeline has high precision:
  from 265k analogous pairs → 8,216 communities → 606 cross-area → exactly one
  actionable new abstraction, which was then constructed and verified.
