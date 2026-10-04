# 34/35 — Typeclass hierarchy topology and peer-relative instance gaps

Plan item 10. Uses the already-extracted `atlas_classes.jsonl` (2,300 Mathlib
classes; each carries `parents` with a `subobject` flag) and
`atlas_instances.jsonl` (33,215 Mathlib instances; each carries `className` and
`targetHead`). Script 34 builds the `extends` DAG and a conservative gap
detector; script 35 kernel-checks whether the flagged "missing" parents are
genuinely missing. Independent verifier `verify_typeclass_structure.py` →
**VERIFICATION OK**; Lean probe exits 0 with no warnings/`sorry`.

## (A) Hierarchy topology (authoritative)

- 2,300 Mathlib classes; **557** extend another class; **274** use multiple
  inheritance; **87** are true diamonds (two parents share an ancestor).
- Main-line depth (following `subobject=true`): 1,743 at depth 0, then
  257 / 126 / 71 / 34 / 29 / 23 / 10 / 5 / 2 across depths 1–9 — a wide, shallow
  hierarchy (max depth 9).
- Widest ancestor classes (number of descendants): `AddSemigroup` 75, `AddZero`
  73, `NSMul` 72, `AddZeroClass` 72, `AddMonoid` 71, `Semigroup` 64 — the
  additive/multiplicative algebraic magma spine dominates, exactly as expected
  from `to_additive`.
- Highest instance fan-in: `CategoryTheory.IsIso` 448, `IsScalarTower` 336,
  `Category` 300, `Module` 284, `SMulCommClass` 282, `PartialOrder` 276.
- Densest concrete carrier bundles (distinct classes concretely instantiated):
  `Prod` 352, `Subtype` 346, `OrderDual` 251, `MulOpposite` 173, `ULift` 156,
  `Opposite` 147 — the generic "wrapper" carriers carry the most class instances,
  which is the structural reason the analogy sweeps kept seeing wrapper twins.

## (B) Peer-relative gap detector — and why it is a NEGATIVE result

A concrete carrier T "has" class C when an instance with `targetHead = T`,
`className = C` exists (11,971 concrete pairs over 1,481 carriers). For a direct
**cross** parent P (`subobject=false`; main-line parents are auto-projected and
so never need restating), compare all carriers reaching C: if ≥3 peers and ≥66%
of them concretely provide P while some do not, flag the non-providers.

- 77 cross-parent rules examined; 20 rules show a peer-majority split;
  **54 candidate rows** (`data/typeclass_gap_candidates.jsonl`), e.g.
  `CommGroup → CommMonoid` (15 carriers), `AddGroupWithOne → AddGroup` (4),
  `NonUnitalNonAssocRing → NonUnitalNonAssocSemiring` (2).

### Kernel verdict (script 35): none are real gaps

For **all 20 rules**, assuming only `[C α]`, the parent `P α` is built by
`inferInstance` — i.e. the structure projection `C.toP` is itself a global
instance, so EVERY carrier of C automatically has P without a dedicated
declaration. `#synth CommMonoid ℤ` resolves concretely (`Int.instCommMonoid`).
Therefore:

> The 54 rows are **instance-economy / style differences**, not missing
> instances. Some carriers rely on the auto-projected cross parent; their peers
> restate it explicitly (a redundant instance). Lean synthesis succeeds either
> way, so there is nothing to add and no abstraction is missing.

This is itself a useful structural fact: Mathlib's algebraic hierarchy is
**closed under its cross-rungs by projection**, which is precisely why a purely
static "strong class present, parent absent" scan over-reports and must be
checked against the kernel before claiming a gap.

## Data-quality note

Three `parents` edges reference structures not enumerated as classes
(`IsLocalization' → Submonoid.IsLocalizationMap`,
`GroupFilterBasis/AddGroupFilterBasis → FilterBasis`): name-qualification /
structure-not-class coverage in the earlier class extraction. They are inert
here (guarded by `p in by`) and pinned as a fixed known set in the verifier.

Reproduce: `python script\python\34_typeclass_structure.py`,
`python script\python\verify_typeclass_structure.py` (VERIFICATION OK),
`lake env lean script\lean\35_instance_gap_check.lean` (exit 0, clean).
