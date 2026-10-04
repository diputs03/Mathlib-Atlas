# 19 — Community abstraction-status triage (design note)

## Purpose

Script 18 produced **8,216 analogy communities**, of which **606 span ≥2
top-level Mathlib areas**. Those 606 are the candidate "missing abstraction"
worklist, but they are not all the same kind of thing. Script 19 labels each
one by **abstraction status**, so downstream effort (and the Lean case studies)
goes to the communities that are genuinely repeated concrete code rather than
to families Mathlib has already abstracted.

## Inputs

- `data/analogy_clusters.jsonl` (8,216 communities, anchors, labels)
- `data/analogy_cluster_assignment.jsonl` (full membership + module/area)
- `data/atlas_features.jsonl` (`valueIsRfl`, `isInstance`, …)
- `data/atlas_classes.jsonl` (the 2,748-name typeclass table)

Only the 3,301 declarations that belong to cross-area communities need feature
lookups; the feature file is streamed once and filtered.

## Signals computed per community

- **suffix uniformity** — dominant declaration suffix and its coverage.
- **carriers** — distinct "namespace" prefixes (Set / Filter / Finset / …).
- **class anchors** — shared `C:` anchors that are real typeclasses.
- **head anchors** — shared conclusion heads `H:`.
- **built class** — a real class that is *both* a constraint anchor and the
  conclusion head, and whose name matches the declaration suffix
  (`Set.addCommMonoid` builds `AddCommMonoid`). This is the discriminator
  between "uses a helper class" and "constructs the same structure per
  carrier".
- **instance / rfl / infra fractions** — `isInstance`, `valueIsRfl`, and the
  share of members whose module is elaborator/pretty-printer infrastructure
  (`.Tactic. .Lean. .Util. .Meta. PrettyPrinter Parenthesizer Formatter
  Delaborator`).

## Status labels (priority order)

| status | rule | meaning |
|---|---|---|
| `infra` | ≥½ members in elaborator/PP modules | metaprogramming leakage, not math |
| `structure_lifted_per_carrier` | builds a named class, ≥2 carriers | same algebraic structure instantiated independently on several carriers (pointwise monoids, …) |
| `generic_api_exists` | shared real helper class, uniform suffix/instances | an abstraction already captures the family (case B's `Is*Apply`, InjSurj, category APIs) |
| `pointwise_repeated` | uniform suffix ≥0.6, ≥3 carriers, no class anchor | repeated concrete lemmas with no unifying class |
| `shared_head_analogy` | shared conclusion head, suffix <0.5 | same statement-shape across areas |
| `weak` | none of the above | low-signal |

Rows are ordered (candidate-first) and carry an `opportunityScore`
(size × areas × uniformity × (1 − ½·rflFraction)) for the two repeated buckets.

## Results (606 cross-area communities)

| status | count |
|---|---|
| shared_head_analogy | 348 |
| generic_api_exists | 144 |
| structure_lifted_per_carrier | 29 |
| weak | 66 |
| pointwise_repeated | 11 |
| infra | 8 |

### `generic_api_exists` (144) — external validation
The embeddings re-discovered families Mathlib already abstracted. Case B's
FunLike apply API is here (`#22 coe_smul`, `#23 smul_apply` anchored on
`IsSMulApply`, `#81/#83 neg/sub_apply`, `#113/#114 coe_neg/coe_sub`), as are
category-theory APIs (`forget_map`, `monoFactorisation`) and the InjSurj
transfer lemmas. These confirm the detector finds real abstractions; they are
not refactoring opportunities.

### `structure_lifted_per_carrier` (29) — the pointwise-algebra story
These are the pointwise operations/structures across `Set`, `Finset`,
`Filter`, `Ultrafilter`, `Equiv`, `Finsupp`, …:
`Add/Mul/Zero/One/Neg/Inv/Sub/Div` (#220/#222/#286/#289/#292/#293/#296/#298),
`Semigroup/AddSemigroup` (#392/#414), the full monoid ladder
(`#574–#602` Set↔Filter pairs), `MulAction` (#84, 9 members / 7 carriers, the
largest), `AddAction` (#140), `DistribMulAction` (#243/#185).

Source reading (see case study C, `script/lean/20_pointwise_lift.lean`) shows
these split into **three construction mechanisms** the name graph cannot see:
- `Set α` — primitive pointwise lift, laws from `Set.image2_assoc`;
- `Filter α` — primitive pointwise lift, laws from `Filter.map₂_assoc`;
- `Finset α` — **does not repeat the proof**: its whole hierarchy is
  `coe_injective.<class> … coe_mul`, i.e. it inherits from `Set` through the
  generic `Function.Injective.*` transfer API (which is itself a
  `generic_api_exists` family). The clustering therefore links two apparently
  separate communities through a real implementation relationship.

The residual duplication is Set-vs-Filter: both rebuild the hierarchy from
their own binary-lift primitive; a common "binary lift preserves algebra"
abstraction does not exist. A few topology transfer families
(`LocallyConnectedSpace`, `DiscreteTopology`) fall here too, correctly — they
are structure lifted across homeomorphism/chart carriers.

### `shared_head_analogy` (348) — candidate common lemmas
Largest genuine items: `H:Equivalence` (#10, 26 members / 10 areas),
`H:GaloisInsertion` (#33, 16/7), `H:AddHom` (#8, 26/4), `H:MulHom` (#14).
Caution: a handful of the top rows are elaborator/library-note families
(`#2 LibraryNote`, `#12 Unexpander`, `#3 TermElab`) whose members live in
non-Tactic *areas* and so escape the area filter; read the head anchor before
treating a row as mathematics.

## Verification

`script/python/verify_community_triage.py` independently re-derives every
metric and the status label for all 606 rows from the raw inputs, checks
suffix/instance/rfl fractions, built-class detection, coverage (every
cross-area community present exactly once), the by-status counts, and the
declared deterministic ordering → **VERIFICATION OK**.

## Caveats

1. "built class" detection is name/heuristic based; a class used only as a
   constraint with a coincidentally matching suffix could be mislabelled — the
   per-row evidence (`classAnchors`, `builtClass`, `members`) is emitted so any
   row is auditable.
2. The infra filter keys on module paths; meta lemmas that physically live in
   mathematical-area files can survive into `shared_head_analogy`.
3. Status describes *abstraction state*, not correctness: every declaration
   here already type-checks in Mathlib.
