# 80–85 — Within-theory anomaly ranking: case study and freeze

**Scientific question.** Does proof structure become informative when
"similarity" is replaced by *local abnormality within a mathematically
coherent neighborhood*? The target positive was a theorem whose statement
is ordinary in its area but whose proof/dependency structure is anomalous
and, on inspection, reveals a non-obvious connection.

## Method

- Scope: Order + Algebra, **62,003 real theorems** after the canonical
  helper filter (Order 17,189; Algebra 44,814).
- **80 — five competing neighborhoods**: same namespace (3,016 groups),
  same module (1,592), (area, conclusion head, nPi/2) family (3,206),
  shared rare-dependency targets with document frequency 2–12 (14,451
  theorems covered), and semantic nearest neighbors (7,165 covered).
- **81 — v3 percentile anomaly model** (two earlier iterations rejected:
  robust-z on heavy-tailed features in tiny modules produced 21k
  "anomalies"; a transform-consistency bug that queried raw values
  against log-built percentile maps was found and fixed). A dimension is
  a local anomaly only when the theorem's empirical percentile over the
  scoped corpus is ≥ 0.95 **and** its module peers' median percentile is
  ≤ 0.60; score = 10·(g−0.95)/0.05, capped at 10. Dimensions without data
  are NA, never forced.
- Result: **2,102 theorems with any local anomaly** (3.4%), 1,229
  single-dimension. Per-dimension high: proof 537, dependency 426,
  semantic 235, type 168, generality 105, namespace 0.
- **82 — calibration**: known-unusual cases are recovered —
  `Filter.map₂_assoc` (PointwiseLift family) proof anomaly 3.88; bridge
  declarations surface strongly (`MulMemClass.mul_mem` 9.89 semantic,
  `MonovaryOn.sum_smul_comp_perm…` 9.48 proof, `mul_lt_mul_of_pos_right`
  8.21, `Int.cast_mul` 8.15 proof, Subfield/Subring class instances
  8.62/8.02 dependency).
- **83 — adjudication**: a 70-candidate single-dimension shortlist
  (14/dimension) was checked against the Mathlib source. Every candidate
  received a definite class; zero candidates remain "other".

## Adjudication taxonomy (70 candidates)

| class | n | what it actually is |
|---|---:|---|
| category_api | 14 | limit/biprod/homology/short-exact lemmas; big terms are the category API itself |
| expected_generic | 14 | one-line positivity, atom, `isBot`/`isCoatom`, involutive delegations |
| bundled_equiv_api | 11 | `*_apply`/`*_symm_apply` lemmas; the type must mention both carriers and the Equiv |
| generated_fragment | 10 | residual `mk.inj`/`injEq`/`sizeOf_spec`/`congr`/`hcongr` — new helper patterns to record |
| instance_artifact | 6 | `inst*` and `lawfulMonad` field-proof declarations |
| legitimate_heavy_theorem | 6 | `MvPolynomial.dvd_X_mul_iff` (division algorithm), `fwdDiff_iter_choose_zero`, `Finpartition.atomise_empty`, Quaternion lemmas, `Fin.partialSum_contractNth` |
| family_cluster | 4 | floor family (`mul_lt_floor`, `div_two_lt_floor`, `ceil_lt/le_two_mul`): a self-contained sub-family sharing its own rare lemmas inside a generic module |
| ext_api | 2 | `Ring.ext`, `Unitization.algHom_ext` |
| class_field_api | 2 | `MulMemClass.mul_mem`, `StarMemClass.star_mem` field propagation |
| expected_induction_principle | 1 | `Algebra.adjoin_induction₂` — many binders are intrinsic |

**Null verdict.** No candidate is an ordinary statement hiding a
non-obvious cross-theory connection. The detector mechanically works —
it recovers planted/known controls — but what it sees at the
within-theory level is:

1. **theorem-weight peaks** — the central heavy proof of a file
   (division algorithm, finite-difference Kronecker identity);
2. **family density** — a self-contained theorem sub-family inside a
   larger generic module (floor lemmas);
3. **bundled API surface** — Equiv application lemmas, instance field
   proofs, category limit lemmas, class field lemmas;
4. **residual generated fragments** that name the next round of helper
   filters (`sizeOf_spec`, `mk.inj`, `hcongr`, `congr_simp`).

## What this establishes about the instrumentation

Together with 77–79, the proof representation now has two audited
results:

- **cross-area exact signatures**: too coarse globally (generic noise),
  too fine at full depth (the Fin positive control itself splits into
  41 keys);
- **within-theory local anomalies**: detectable and calibrated, but they
  measure theorem weight, family density, and bundled API surface — all
  expected structure — rather than hidden connections.

The missing instrument remains **approximate structural matching**
(tree-edit distance / name-family generalization) over proof terms. It
has not been built, deliberately. Per the pre-stated Phase 4
contingency, this null is the point at which building it has a strong
justification: exact representations failed both globally and locally.
That is a decision for the next campaign given the engineering cost.

## Freeze

Scripts 80–85 are frozen. `verify_within_theory_anomaly_campaign.py`
passes all checks. No further anomaly ranking with exact percentile
features; no revival of the 70+ GB full proof-term dump unless a new
campaign explicitly requires it.
