# 21 — Second-stage triage of `shared_head_analogy` (design note)

## Why

Script 19 put **348** cross-area communities in `shared_head_analogy`: members
share a conclusion *head* (e.g. `Equivalence`, `AddHom`, `GaloisInsertion`,
`PullbackCone`) but have no uniform declaration suffix. A shared head is not, by
itself, a missing abstraction — most such communities are either the head's own
generic API or many independent witnesses of one existing predicate. Script 21
splits this bucket so effort goes only to communities that repeat a non-trivial
argument.

## Method

For each shared-head community, using full membership + script-13 features:

- **head root** — last namespace segment of the shared `H:` anchor
  (`AddHom`, `Set.InvOn`, `…PullbackCone`).
- a member is **API** if its own namespace tail equals the head root
  (`AddHom.comp`, `Set.InvOn.mono`, `PullbackCone.flip`); otherwise it is an
  **external** construction/witness.
- among external members, dominant suffix and its coverage; median
  `valueNodes` (proof-term size).

Sub-status (priority):

| sub-status | rule | reading |
|---|---|---|
| `head_api` | ≥½ members are the head's own API | already generic; not a target |
| `repeated_proof` | external, uniform suffix ≥0.5, median valueNodes > 25 | same sizeable argument rebuilt per carrier — inspect |
| `bundled_witness` | external, uniform suffix, tiny terms | trivial constructor bundle (threshold rarely met because witness suffixes vary — these fall in `mixed`) |
| `mixed` | otherwise | case-by-case; includes trivial-bundle families with varied suffixes |

Deterministic ordering; `repeated_proof` first.

## Results (348 communities)

| sub-status | count |
|---|---|
| mixed | 244 |
| head_api | 85 |
| repeated_proof | 19 |
| bundled_witness | 0 |

### `head_api` (85) — already generic
The morphism/limit/relation APIs: `AddHom` (#8), `MulHom` (#14), `ZeroHom`
(#48), `Fork` (#37), `Cofork` (#54), `Set.Pairwise` (#60), `Set.InvOn` (#39),
`PullbackCone` (#49 partly). Cross-area members are constructions *into* a
generic API that already exists.

### `repeated_proof` (19) — inspected, not mechanical dedup
Largest are category-theory/topology constructions whose terms are big because
they bundle substantial carrier-specific proofs: `PullbackCone` (#49,
median 575 nodes), `RepresentableBy` (#106, 2385), `EqualizerCondition`
(#143, 9400), `IsTopologicalBasis` (#377, 26795), and induced-structure maps
`toOpens/toCloseds/toTopologicalSpace/toMeasurableSpace` (#97/#138/#366/#376).
Reading them: each constructs the head object inside a *different concrete
category/space*; there is no shared lemma that removes the carrier-specific
content. Big term size here reflects real work, not copy-paste.

### `mixed` (244) — includes the trivial-bundle families
The widest community, `Equivalence` (#10, 26 members / 10 areas), lands here
only because its suffixes vary (`equivalence / eqv / is_eqv / setoid`). Case
study D (`script/lean/22_equivalence_witness.lean`) shows it is in fact a
family of **trivial bundles**: every witness is `Equivalence.mk R.refl
R.symm R.trans` (or `where refl:=refl …`), and closure-generated relations use
the generic `Relation.ReflTransGen`/`EqvGen` constructors. `GaloisInsertion`
(#33) and `IsInitial` (#71) are analogous: many witnesses, one generic
constructor.

## Interpretation

Across all four sub-buckets, `shared_head_analogy` is overwhelmingly
**expected multiplicity of an existing abstraction**: either the head's own
API (85), trivial constructor bundles (Equivalence/GaloisInsertion/IsInitial),
or carrier-specific constructions with no factorable common argument
(repeated_proof). This is a structural contrast with script 19's
`structure_lifted_per_carrier` (Set/Filter pointwise), where a concrete
construction *is* duplicated and a shared binary-lift abstraction is genuinely
missing. The two-stage triage therefore de-prioritizes 348 communities with
evidence rather than intuition.

## Verification

`script/python/verify_shared_head.py` independently recomputes API/external
split, external suffix coverage, median term size, sub-status and ordering for
all 348 rows → **VERIFICATION OK**.

## Caveats

1. `valueNodes` measures elaborated term size, not proof duplication; the
   repeated_proof label is a *ranking hint*, every row still needs source
   reading (done for the top 19).
2. The `bundled_witness` automatable threshold is intentionally strict;
   trivial bundles with varied suffixes appear under `mixed` and are identified
   qualitatively (case D).
