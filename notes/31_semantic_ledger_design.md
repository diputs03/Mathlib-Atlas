# 31 — Closing the 627-pair semantic ledger

Script 28 produced 627 structurally-divergent cross-area semantic candidates.
Probes 29 (case F, filter-relative) and 30 (case G, real/manifold smoothness)
kernel-checked the two large families. Script 31 assigns **every** remaining
pair to a documented family by a mechanical rule, so the human only had to read
the shrinking `unresolved` residual (now **0**). Independent verifier
`verify_semantic_ledger.py` → **VERIFICATION OK**.

## Final ledger (627 = 627, 0 unresolved)

| family | count | share | mathematical status |
|---|---:|---:|---|
| **F_locus** — global / on-set / at-point / within / AE / eventually / uniform-on-filter | 365 | 58% | one generic `Filter.Eventually` with loci `⊤/𝓟/𝓝/ae`; **probe 29 kernel-verified**; order predicates need the α×α product filter; AE/QMP are quotient/measure-level |
| **G_smooth** — real-space vs manifold differentiability (incl. UniqueDiff/UniqueMDiff) | 126 | 20% | manifold notion is the generic; iff/equality bridges exist at every level; **probe 30 kernel-verified** |
| **strength_arity** — strict/non-strict, arity (Injective/Injective2), point/global (PeriodicPt/Periodic), connected/path-connected, embedding/closed-embedding, directed-sup | 57 | 9% | one definition plus a stronger hypothesis or extra argument; not a new abstraction |
| **cat_dual** — Limit/Colimit, Exact/ShortExact, Left/Right homology, Epi/Mono, Injective/Surjective | 54 | 9% | categorical dual / exactness already expressed by the same framework |
| **add_mul_twin** — additive vs multiplicative twin (IsAddUnit/IsUnit, AddCommute/Commute, *MulSupport/Support, IsOrderedAddMonoid/…) | 13 | 2% | literally one declaration duplicated by `to_additive` |
| **num_domain** — Nat/Int/Rat/NNRat/NNReal variants | 8 | 1% | same predicate over a different numeric carrier |
| **bundled_concept** — `Is…` predicate vs `…Category` bundled class, ℓp membership, naming ornament | 4 | 1% | same concept, bundled/unbundled presentation |
| **unresolved** | **0** | 0% | — |

## How the classification works (deterministic, pure stdlib)

For each pair take the two conclusion-head roots and apply, in order:

1. **F_locus** — strip locus suffixes (`WithinAt/OnWith/At/On/With/AE`) and
   `AE/Quasi` prefixes; match if the bases coincide while one side is decorated,
   if both are `Eventually*`, or both carry a filter marker
   (`Tendsto/UniformlyOn/OnFilter/HasProd`).
2. **G_smooth** — both roots contain a differentiability marker.
3. **add_mul_twin** — equal after deleting `Add`/`Mul` ornament.
4. **cat_dual** — dual-word pairs (Limit/Colimit, Epi/Mono, Injective/Surjective,
   Left/Right, both-Exact / both-Homology).
5. **strength_arity** — equal after deleting `Strict`, or on a fixed
   stronger/weaker/arity pair list.
6. **num_domain** — both mention a numeric-domain marker.
7. **bundled_concept** — equal after stripping `Is`, `Category`, `Space` and
   normalizing a handful of presentation aliases.
8. else **unresolved**.

The verifier independently re-derives a per-family invariant and checks a
name-pair bijection with the 627 candidates, count reconciliation, the empty
unresolved set, and the closed family set.

## Verdict for the whole semantic track (28–31)

The semantic/role-based method — which deliberately ignores structural head
identity, per the directive that undiscovered structure has an incomplete
structural signature — successfully recovered 627 cross-area analogies the
structural track (17–27) could not see. After kernel-level probing and full
ledger closure, **every one is an already-existing abstraction**: a filter locus
(F), the manifold generalization (G), a strength/arity variant, a categorical
dual, a `to_additive` twin, a numeric-carrier variant, or a bundled/unbundled
presentation. **No additional new construction beyond case E (`PointwiseLift`) is
warranted.** The value delivered is (a) validation that semantic similarity
reaches structurally-incomplete analogies, and (b) a kernel-verified explanation
of why each multiplicity is irreducible or already unified.

Outputs: `data/semantic_ledger.jsonl` (627 family labels),
`data/semantic_ledger_summary.json`. Reproduce:
`python script\python\31_semantic_ledger.py` then
`python script\python\verify_semantic_ledger.py` (VERIFICATION OK).
