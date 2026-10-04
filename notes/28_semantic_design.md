# 28 — Semantic (role/concept) analogy track

## Why this track exists

Scripts 17–27 built and triaged a **structural** analogy graph: two declarations
look alike because they share the same concrete conclusion head `H`, constraint
class `C`, or value head `V`. That sweep closed all 606 cross-area communities and
found exactly one positive new abstraction (case E, `PointwiseLift`).

Structural matching has a systematic blind spot that the user identified:

> Semantic similarity can be more valuable than structural similarity for
> finding genuinely *undiscovered* structure, because an abstraction that does
> not yet exist has an **incomplete structural signature**. Its instances do the
> same mathematical job while currently carrying **different concrete heads and
> different proof bodies** — so a head-equality method discards them as "different"
> precisely when they are most interesting.

Script 28 is the response. It deliberately **strips structural identity** and asks
only: *what mathematical ROLE is this declaration playing, and what is it ABOUT?*
Two theorems are paired when they play the same role and talk about the same
concept, even though their concrete predicate/lemma names differ.

## What is vectorized (and what is forbidden)

For each declaration in the script-17 population (human theorem/definition/opaque,
generated/instance/class and `Tactic`/`Lean`/`(root)`/`_private`/`.Meta.` removed),
plus an extra exclusion of auto-generated inductive API (`casesOn`/`recOn`/
`brecOn`/`inductionOn`/`rec`/`noConfusion*`):

| token | meaning | identity-free? |
|---|---|---|
| `k` | kind | yes |
| `P` | conclusion **predicate-role**: equality / iff / membership / order-comparison / instance-goal / exists / other-pred — never *which* predicate | yes |
| `V` | proof **strategy-role**: rfl / constructor / cases / recursor / rewrite / named-lemma / opaque / none | yes |
| `R` | prerequisite profile = the **areas** of its type-class constraints, not which classes | yes |
| `w` | **concept words** of the conclusion head (camelCase split, stopwords/len<3 removed): `Continuous`, `Mono`, `Measurable`, `Diff`, `Lipschitz` … | words, not full name |
| `vw` | concept words of the value head (proof vocabulary) | words, not full name |
| `s`,`S` | arity/binder/type-size/value-composition log-buckets + rfl/cases/rec/lam/let flags | yes |

**Deliberately NOT vectorized:** the full head/class/value identifiers, the
module, the namespace, the declaration name, and the *concrete prerequisite-class
words* (the latter only record a common setting — e.g. "normed space" — and were
found to dominate the cosine otherwise). Weighting is sublinear TF
`(1+ln tf, cap 4) × idf`, L2-normalized; cosine is an exact sparse dot product.

## Blocking: role signature + one shared result word

A naive "same role signature" block (kind,P,V + three size buckets) produced giant
blocks — e.g. `P:equality / V:named-lemma` had 24,541 members across 29 areas —
whose full cross-product was both expensive and low-precision. The final design
uses an **inverted index**: a declaration enters one block per conclusion concept
word, keyed by `(role signature, word)`. Any co-blocked pair therefore already
shares at least one result word, no block is ever giant, and coverage is complete
(**0 oversized blocks skipped** at full scale). A pair shared through several words
is de-duplicated, keeping its best cosine.

## The "hidden candidate" filter

A within-block pair is emitted only when ALL hold:

1. both are **theorems** with a non-empty conclusion (field projections and
   no-conclusion definitions are not discovery targets);
2. **cross-area**;
3. **structurally divergent**: different conclusion head AND different value head
   (the exact cases the structural track threw away);
4. shared result vocabulary: ≥1 shared conclusion word and ≥2 shared
   conclusion+value words (prerequisite setting words do not count);
5. cosine ≥ **0.80**;
6. closest 12 per block, global cap 40,000.

A second output, `semantic_role_shortlist.json`, lists every loose role signature
spanning ≥3 areas and ≥6 members — the "hunting grounds" even where no pair clears
the divergence gate.

## Full-run results (Lean v4.34.0-rc2 Mathlib, commit bbcd196)

- scanned 574,391; **embedded 285,823**; vocab 5,018; 33,341 word-anchored blocks;
  20,068,370 within-block pairs; **0 skipped**.
- **627 hidden candidates**, 776 declarations with a hidden neighbour;
  1,093 role-shortlist entries.
- Independent verifier (`verify_semantic.py`) rebuilds population, tokens, TF-IDF,
  blocking and filters from raw inputs: per-row invariants hold, regenerated pair
  set equals the emitted set **627 = 627 (missing 0 / extra 0)**, cosines agree,
  and the set is stable under sorted-block iteration → **VERIFICATION OK**.

## What the 627 pairs actually are — the family taxonomy

The candidates collapse into a small number of mathematically real "twin
predicate" families (conclusion-head-root pair counts):

| family | shape | pairs |
|---|---|---:|
| **locus-relative predicate** (global ↔ restricted / at-point / almost-everywhere / eventually) — **304 of 627 (48%)** | `Continuous↔ContinuousOn/At` 37+36, `StrictMono↔StrictMonoOn` 38, `Monotone↔MonotoneOn` 18, `Integrable↔IntegrableOn` 23, `Antitone↔AntitoneOn` 9, `LipschitzWith↔LipschitzOnWith` 10, `StronglyMeasurable↔AEStronglyMeasurable` 20, `MeasurePreserving↔QuasiMeasurePreserving` 29, `Eventually↔EventuallyEq` 60 | 304 |
| **real ↔ manifold differentiability** | `HasFDerivWithinAt↔HasMFDerivWithinAt` 21+13, `ContDiff(WithinAt)↔ContMDiff(WithinAt)` 12+, `Differentiable(On)↔MDifferentiable` 9+, `ContDiff↔ContDiffAt` 19 | 124 |
| categorical dual / exactness | `Exact↔ShortExact` 28, `PreservesLimitsOfShape↔PreservesColimitsOfShape` 12 | 40 |
| stricter/weaker variant | `HasDerivAt↔HasStrictDerivAt` 10, `Injective↔Injective2` 9 | ~25 |
| other (long tail, individually inspectable) | — | remainder |

Top area pairs are Analysis–Geometry (139), Analysis–Topology (81),
Analysis–MeasureTheory (65), MeasureTheory–Probability (46) — exactly the analysis
neighbourhood where the same notion is re-stated on a domain / at a point / on a
manifold / almost-everywhere.

## Reading the result: the method is validated, and a candidate case F emerges

**Methodological result.** The track recovers, with **zero head-equality signal**,
families the structural track could not surface: e.g. `Continuous` vs
`ContinuousOn` have different heads and different value lemmas, yet role + concept
words + shape place them at cosine ≈ 0.95. This confirms the user's point —
semantic/role similarity reaches structurally-incomplete analogies.

**These particular families are mostly already-known parallel APIs** (Mathlib
deliberately maintains `P` / `POn` / `PAt`, real vs manifold smoothness, limit vs
colimit). So, like cases C/D, they are *irreducible multiplicity of an existing
abstraction* rather than missing code — **not** new constructions.

**Candidate case F (to probe, not yet built): a filter-relative predicate.**
The 304-pair locus-relative superfamily has one mathematical shape:

```
P          = P relative to the whole carrier / top filter
POn s      = P relative to the principal filter 𝓟 s
PAt x      = P relative to the neighbourhood filter 𝓝 x
AE P       = P relative to the almost-everywhere filter ae μ
Eventually = P relative to an arbitrary filter (already filter-based)
```

Mathlib already unifies the *point/set* case through filters for continuity and
differentiability (`ContinuousAt = Continuous within 𝓝 …`, `WithinAt`), which is
why this is "partially abstracted". The open question for a case-F probe is whether
the residual `On`/`At`/`AE`/`Quasi`/`EventuallyEq` predicates across Order
(`Monotone`/`StrictMono`/`Antitone`), Measure (`Integrable`, `StronglyMeasurable`,
`MeasurePreserving`) and Analysis admit ONE generic `Filter.Relative P l` lifting
with the global/on/at/AE versions as instantiations — and where that lifting breaks
(e.g. `QuasiMeasurePreserving` is null-set-image, not a filter restriction, so it
may sit outside the abstraction exactly as `Group` sat outside the PointwiseLift
ladder in case E). No Lean construction is attempted here; that probe is the next
decision point.

## Reproduce

```
python script\python\28_semantic_analogy.py     # full, ~1 min
python script\python\verify_semantic.py         # VERIFICATION OK
# smoke:  $env:ATLAS_LIMIT="25000" before running (0 = full)
```

Outputs: `data/semantic_hidden_candidates.jsonl` (627),
`data/semantic_role_shortlist.json` (1,093), `data/semantic_summary.json`.
Pure stdlib, deterministic; population/exclusions match script 17 plus the
inductive-API exclusion. 07 full-proof-term persistence remains parked;
`external/mathlib4` untouched.
