# 77–79 — Cross-area proof-strategy anomaly campaign: case study and freeze

Date: 2026-09-24. Toolchain: leanprover/lean4:v4.34.0-rc2. Windows, no WSL.
Downstream only; `external/mathlib4` untouched.

## 1. Question

After the Order pilot (75/76) showed that proof-strategy convergence is
detectable *within* a mathematical family (positive control: 41 Fin interval
lemmas co-group and all delegate to the generic `addNat`/`castAdd`/
`addNatEmb` interval lemmas), this campaign asked the cross-area question:

> Does a proof strategy common in one core area appear, anomalously, inside a
> different core area — i.e. can proof skeletons reveal cross-disciplinary
> strategy borrowing that the declaration/type/API layer missed?

## 2. Pipeline and counts

- **77** (`script/lean/77_proof_skeletons_core.lean`): one Mathlib load;
  `.thmInfo` values across all ten core areas; rows `{name, module, area,
  skeleton}` with the 75 tokenizer; resume support (append mode, existing
  names loaded into a HashSet, flush every 2000 rows).
  Result: **282,971 theorem skeletons; 3.59 GB; 14,324 oversized proofs
  truncated**. Per area: Algebra 76,830; Analysis 40,027; Data 35,274;
  Topology 38,161; RingTheory 28,702; Order 26,828 (exactly cross-validates
  script 75); LinearAlgebra 16,887; GroupTheory 13,261; FieldTheory 4,126;
  Logic 2,875.
  Accepted with EXIT=0 and zero warnings (a `String.trim` deprecation was
  fixed to `trimAscii.toString`; a resume rerun skipped all 282,971 rows and
  produced no new output).
- Helper census: of the 282,971 raw theorem rows, **116,023 are generated
  helpers** (`_private*`, `._proof_n`, `._simp_n`, `instX.eq_n`), leaving
  **166,948 real theorems**. The eq_n filter was added when the first
  anomaly pass was dominated by instance sub-proofs (`instX.eq_1`).
- **78** (`78_strategy_anomalies.py`, coarse level): group on the 76 coarse
  signature (K identity erased, variables/instances/projection indices
  erased). 130,381 coarse groups; groups with size ≥12 and one area ≥70%
  pure and spanning >1 area → **40 exported-strategy groups; 50 outlier
  theorems**. Rare-shape-weighted area overlap computed.
- **79** (`79_fine_strategy_groups.py`, fine level): full tree and all K
  tokens kept verbatim; only variables/instances/projection indices/literal
  values erased. **164,816 fine groups; only 108 span more than one area.**

## 3. Adjudication — coarse level

The 40 coarse exported groups were inspected against source. None is a
genuine exported strategy. They are generic-shape coincidences:

- multi-lambda constructor-application shapes shared by unrelated lemmas
  (e.g. pointwise set-subset lemmas grouped with interval membership lemmas;
  `UpperHalfPlane.coe_injective` grouped with `ENNReal.ofReal_mono` and
  `sigmoid_lt_iff`);
- residual OrderDual/type-synonym instance derivations
  (`instCompactSpaceMultiplicative`, `OrderDual.isDirected_le`).

The coarse signature erases exactly the information that distinguishes
strategies (which named lemmas are applied), so generic propositional shapes
("fun x y h1 h2 => exact ⟨…, …⟩") coincide across thousands of unrelated
theorems.

## 4. Adjudication — fine level

All 108 cross-area fine groups were manually adjudicated. Final class counts
(independent verifier, zero "other"):

| class | groups |
|---|---:|
| defeq_copy_or_expected_generic | 35 |
| bundled_hom_api_propagation | 27 |
| private_decidability_fragment | 17 |
| relation_class_propagation | 13 |
| instance_fragment | 7 |
| generated_equation_fragment | 5 |
| generic_shape_coincidence | 4 |
| **new exported strategy** | **0** |

Content of the classes:

- **bundled_hom_api_propagation** (script-64 class): `add_apply`,
  `smul_apply`, `coe_add/smul/neg/sub/sum`, `zero_apply`, `coe_zero`,
  `domRestrict(_apply)`, `intCast_apply`, `mul_apply_eq_comp`,
  `one_apply_eq_self`, `coeAddMonoidHom_apply`, `finsetSum_apply`,
  `forget_map` — the FunLike/BundledHom propagation lemmas across
  Seminorm/AddGroupNorm/CLM/ContinuousMultilinearMap/MultilinearMap/
  QuadraticMap/SchwartzMap/TestFunction and the concrete category forget
  functors.
- **relation_class_propagation** (script-64 class): `stdSymm`, `isTrans`,
  `refl`, `insert_of_symm`, `mapsTo_symm`, `symmGen`, the `Module.End`
  center family — generic relation-class API lemmas.
- **defeq_copy_or_expected_generic** (script-73 FP class plus expected
  generics): `some_injective/some_inj/map_id` across WithBot/WithTop/
  WithZero/WithOne/OnePoint/Sym2; `unop_op`; the three
  `Complex.equivRealProd*_apply` bundled views; CStarMatrix/Matrix
  (`instFinite`, `one_apply_ne` — defeq copies); `isCyclic.commutative` /
  `Surjective.mul_comm`; Free/Finite `shrink`; `of_ringEquiv`;
  `not_unit`; lcm/gcd/cast families; `finset_prod/sum` calculus and
  big-operator families.
- **instance_fragment**: instances whose value is a single projection or
  builds directly on another instance (`isTopologicalAddGroup`, Nonempty /
  IsEmpty derivations).
- **private_decidability_fragment**: `(L KInt (A PRIV V))` parity/decidable
  snippets (`Int.even_or_odd`, Nat/Int parity lemmas) sharing a private
  decidability lemma.
- **generated_equation_fragment** (new helper-name patterns):
  `*.sizeOf_spec`, `*.match_1.congr_eq_n`, `*._sparseCasesOn_1.else_eq` —
  equation-compiler-generated fragments.
- **generic_shape_coincidence**: size-2/3 unrelated one-liners (e.g.
  `Nat.choose_succ_le_two_pow` with `Polynomial.coeff_hermite_explicit`;
  `Subcomplex.ext` with `asIdeal_inj`).

## 5. Verdict: audited null

Cross-area proof-strategy sharing at exact-signature granularity surfaces
**nothing beyond already-classified phenomena** (bundled-hom and
relation-class API propagation, defeq copies) plus generated fragments.
The within-family positive control passed, but the cross-area anomaly claim
is not supported.

This is **one well-audited null at the cross-area exact-signature level** —
not two consecutive nulls across the whole proof representation, so the
proof-strategy level is not frozen.

## 6. Detectability boundary (the lasting instrumentation result)

- Exact coarse signatures: too coarse — generic lambda/application shapes
  dominate with false cross-area matches.
- Exact fine signatures: too strict — "same strategy, different lemma names"
  (the Fin interval family itself: 41 distinct fine sub-keys such as
  `image_addNat_Ico` vs `finsetImage_addNat_uIcc`) never co-groups.
- The missing instrumentation is **approximate matching**: tree-edit
  distance over skeletons, or name-family stemming (e.g. clustering K
  tokens through shared name stems like `addNat`). This risks inventing
  vocabulary and was deliberately not built here; it is the explicit
  boundary at which exact-signature strategy detection stops.
- Within-theory anomaly ranking (roadmap Phase 4: local outliers versus a
  theorem's mathematical neighborhood) is a different question and remains
  available without approximate matching.

## 7. Instrumentation cost

- 77: ~50 min per full compile (elaboration ~40 min + extraction ~10 min);
  three earlier full runs were killed mid-write (~168k/180k rows), and
  three machine wedges (~80–90 min each) occurred during the day; a clean
  run with no overlapping TaskOutput polls completed. Resume support makes
  killed runs recoverable.
- 78/79: ~10–15 min each (single streaming pass over 3.59 GB, stdlib-only
  Python).

## 8. Freeze

Cross-area exact-signature strategy-anomaly mining is frozen. Do not rerun
77–79 or add keyword buckets to force more groups. The campaign artifacts
stand: data files listed above, verifier ALL CHECKS PASSED, this note.
Next decision point: within-theory anomaly ranking (Phase 4) versus building
approximate skeleton matching — to be chosen deliberately, not by
auto-scanning.
