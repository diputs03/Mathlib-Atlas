# 43 — Class-fact derivation detector (missing generic instance constructions)

## Question
Script 42 found that half of frontier repetition is *per-carrier class/prop-fact
derivation* and recommended a different detector (not the named-theorem lens).
Script 35 only checked missing cross-rung **instances** synthesizable by
projection. Here we ask: when the SAME class/prop fact is proved for many
concrete carriers by the SAME proof strategy (common value head) with no
polymorphic theorem, is a single generic derivation missing?

## Detector
* Universe: 47,342 Mathlib theorems whose conclusion head IS a class/prop.
* Group by (classFact, constraint tuple, nDefault); keep specialized-only groups
  (no sort-binder generic member), ≥4 specialized members, ≥3 distinct carriers.
* Require a DOMINANT shared proof-strategy head (valueHead used by ≥60% of
  members) — the signature "same derivation repeated".
* Funnel: 47,342 → 211 specialized-only groups → **39 shared-strategy candidates**
  (core 27 / frontier 11 / infra 1).

## Result — 0 genuine gaps; the detector inverts
Every one of the 39 falls into exactly two already-factored buckets:

| disposition | n | meaning |
|---|---|---|
| **ownConstructor** | 20 | shared strategy is the class's own `.mk`/`.mk'` — assembling the structure from per-carrier fields. There is no common mathematical content to factor; the fields differ per carrier, so this is irreducible. |
| **reusesGeneric** | 19 | shared strategy is a carrier-agnostic lemma/instance already being reused, e.g. `NeZero` via `NeZero.of_gt'`, `IsBoundedSMul` via `NormedSpace.toIsBoundedSMul` (stronger-class projection, the 35 mechanism), `AddSubgroup.Normal` via `normal_of_isAddCommutative`, `Precoherent` via `instPrecoherentOfFinitaryPreExtensiveOfPreregular`, `Nat.AtLeastTwo` via `Nat.instAtLeastTwoHAddOfNat` (152 carriers, share 1.0). |

### Why this is a structural proof, not an empirical coincidence
A valueHead is a single named constant. If the *same* constant closes the goal
for theorems over *distinct* carriers, that constant cannot mention any one
carrier — it is necessarily polymorphic, i.e. it IS the generic derivation, and
the per-carrier theorems are merely its applications. If the derivation were
genuinely carrier-specific, its head would differ from carrier to carrier and
could never produce a dominant shared valueHead. Hence "high shared-strategy
share across carriers" is evidence that a generic **already exists**, the
opposite of a gap. The only remaining case (own `.mk`) is record assembly with
no shared content. No Lean kernel probe is needed: the negative verdict follows
from what an identical cross-carrier constant can be.

## Relationship to prior results
* Complements 35 (which covered projection-synthesizable cross-rung instances):
  together, missing class-level derivations — whether by projection (35), by a
  reused generic lemma, or by the structure constructor (43) — are all closed.
* Reinforces 42: the frontier's class-fact repetition is concrete growth using
  existing generic machinery, not unfactored derivations. Frontier has 11 of 39
  candidates but 0 gaps, same as core.
* Across 16–43 the single positive new abstraction remains `PointwiseLift`
  (23–25).

## Verification & files
`verify_class_fact_derivations.py` independently rebuilds the generic set,
groups, strategy dominance and dispositions; asserts count bijection, the
20/19 split, deterministic sort and genuineGaps=0 → VERIFICATION OK.
* `script/python/43_class_fact_derivations.py`, `verify_class_fact_derivations.py`
* `data/class_fact_derivation_candidates.jsonl` (39 rows, each tagged disposition)
* `data/class_fact_summary.json`
