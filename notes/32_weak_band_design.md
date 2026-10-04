# 32/33 — Weak semantic band [0.70, 0.80) and candidate case H (independence)

Script 28 kept only cosine ≥ 0.80 (627 pairs, fully closed by 29–31). To make sure
the strict cutoff was not hiding a genuinely new abstraction, script 32
re-ran the full 285,823-theorem embedding at threshold **0.70** into separate
`_loose070` outputs and examined the weaker band **[0.70, 0.80)**.

## Counts (deterministic, pure stdlib; `verify_weak_band.py` → VERIFICATION OK)

- loose (≥0.70): **1,809**; tight (≥0.80): **627**; weak band: **1,182**.
- First stage = script 31's exact classifier: F_locus 404, strength_arity 139,
  cat_dual 69, G_smooth 68, add_mul_twin 53, bundled_concept 43, num_domain 24,
  unresolved 382.
- Second stage over the 382 (weak-band-specific broader normalizers):
  wb_strength_variant 144, wb_arrow_strength 49, wb_cat_limit 36, wb_measure 26,
  wb_naming 28, wb_finiteness 12, **wb_independence 11**, wb_notation_twin 5,
  **wb_noise 71**.

The 71 `wb_noise` rows were read by hand (listed in
`data/semantic_weak_band_residual.jsonl`, sorted by cosine). They are local/filter
reformulations (IsLocalExtrOn/IsExtrFilter), Archimedean strength variants,
Lp/integrability role coincidences, order duals, and a small set of genuine
role-only coincidences between unrelated concepts (e.g. `IsLinearMap`/`IsSymm`,
dynamics `MapsTo`/`Nonempty`). **None is a coherent cross-area analogy that
suggests a missing abstraction.**

## Candidate case H: the "independence" cluster (11 pairs)

The only cluster of real mathematical interest pairs four notions across areas:

| notion | carrier | definition (grounded in Mathlib source) |
|---|---|---|
| `LinearIndependent R v` | Module | `Injective (Finsupp.linearCombination R v)` — LinearIndependence/Basic.lean |
| `AlgebraicIndependent R x` | Algebra | `Injective (MvPolynomial.aeval x)` — AlgebraicIndependent/Defs.lean:54 |
| `ConvexIndependent 𝕜 p` | OrderedSemiring + Module | `p x ∈ convexHull 𝕜 (p '' s) → x ∈ s` — Convex/Independent.lean:57 |
| `sSupIndep` / `iSupIndep` | **CompleteLattice only** | `∀ a∈s, Disjoint a (sSup (s\{a}))` — Order/SupIndep.lean:279 |

### Verdict: NOT a new abstraction — kernel-checked in `33_independence_case.lean`

1. **Same definitional shape.** `LinearIndependent` and `AlgebraicIndependent`
   are both `rfl`-equal to `Function.Injective` of the canonical structure map
   (linear combination / polynomial evaluation). The common abstraction —
   "the canonical map out of a free object is injective" — is already what they
   say.
2. **Algebraic independence already reduces to linear independence of the free
   monomial basis** (`MvPolynomial.basisMonomials : Basis (σ→₀ℕ) R (MvPolynomial σ R)`,
   hence `.linearIndependent`; `AlgebraicIndependent.aevalEquiv`).
3. **Affine independence already reduces to linear independence of pairwise
   differences** (`affineIndependent_iff_linearIndependent_vsub`); convex
   independence is its hull form.
4. **The lattice generic already exists** for any `CompleteLattice`
   (`sSupIndep`/`iSupIndep`, only `Disjoint` + supremum) — Submodule/Subalgebra/
   Subgroup "independent" are its instances.
5. **The combinatorial generic already exists**: `Matroid α` with field
   `Indep` and `IndepAxioms.lean` (exchange axiom). Convex independence obeys the
   OPPOSITE anti-exchange law (a convex geometry, not a matroid), so collapsing
   all four into one class would be **mathematically false**.

## Bottom line

Lowering the threshold to 0.70 adds 1,182 weaker pairs but surfaces **no new
construction**. After two classification stages and a kernel probe of the one
interesting cluster, every pair is an existing abstraction, a strength/arity or
local/global variant, a notation/naming twin, or role-only noise. Across the
entire 16–33 sweep the single positive new abstraction remains **case E
`PointwiseLift`**. The weak-band result also bounds the semantic method: below
≈0.80 the role signal is dominated by surface proof-role coincidence, so 0.80 was
the right operating cutoff.

Reproduce:
`$env:ATLAS_SEM_THRESH="0.70"; $env:ATLAS_OUT_TAG="_loose070"; python script\python\28_semantic_analogy.py`
then `python script\python\32_weak_band_scan.py` and
`python script\python\verify_weak_band.py` (VERIFICATION OK); Lean probe
`lake env lean script\lean\33_independence_case.lean` (exit 0, no warnings).
