# 74 — Equiv/transport scan frozen

Date: 2026-09-24

The Equiv/transport phenomenon is frozen. No further scans for missing
transport lemmas, generic transport abstractions, or Equiv-based API gaps
will be run on the mature stdlib.

## What was audited

- 1,135 plain-`Equiv` witnesses; 492 with two constructor carriers;
  276 constructor pairs; 253 pairs passing the footprint/gap floors.
- Every one of the 253 has a definite adjudication class; the nine
  coverage-gated pairs were source-adjudicated and Lean-falsified.
- Results: 124 representation_boundary, 122 false_positive,
  7 intentional_asymmetry, 0 missing_transport_lemma,
  0 missing_generic_abstraction.
- Independent verifier ALL CHECKS PASSED; Lean falsification EXIT=0 with a
  zero-byte log.

## Decision-gate outcome

The Equiv axis is **mostly null / existing machinery**. This is the second
well-audited null at the declaration/type/API level (the first being the
vertical-generalization axis, scripts 67/69). Per the two-positive/two-null
rule:

> Declaration/type/API-level discovery over the mature stdlib is provisionally
> saturated. The two positives (PointwiseLift; orphan Functors) and two nulls
> (vertical ladders; Equiv transport) close this representational level.

The next move per the roadmap is to climb the representation ladder, not open
another declaration-level scan:

- targeted **proof-strategy pilot** on one mature area (few thousand
  theorems; extract value Expr; normalize names; proof skeletons; cluster),
  with a known shared-strategy positive control recovered before any scaling;
- if the pilot works → strategy anomalies / cross-area strategy reuse;
- then within-theory anomaly ranking;
- then mathematical hypotheses → Lean verification.

Artifacts: `notes/70_74_equiv_transport_case_study.md`,
`script/python/70,71,73 + verifier`, `script/lean/72`,
`data/equiv_*`.
