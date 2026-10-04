# 75–76 — Proof-strategy pilot (Order): instrumentation validated, positive control recovered

Date: 2026-09-24
Scripts:
- `script/lean/75_proof_skeletons_order.lean` — Lean extractor of normalized
  proof/value skeletons (EXIT=0; 26,828 theorems; 191 oversized proofs
  truncated; no sorry)
- `script/python/76_cluster_proof_skeletons.py` — two-level clustering
- `script/python/verify_proof_strategy_pilot.py` — ALL CHECKS PASSED
Data: `data/proof_skeletons_order.jsonl` (140 MB),
`data/proof_strategy_*_order.jsonl/json`.

## 1. Why this pilot exists

After the Equiv decision gate (§20) returned the second audited null at the
declaration/type/API level, declaration-level discovery was declared
provisionally saturated and the roadmap climbs to the next representation:
**proof structure**. The pilot question:

> Is "different theorem statements → same underlying proof strategy"
> detectable from Lean's elaborated proof terms, at all?

The user's requirement was explicit: recover a **known shared-strategy
positive control** before any scaling; if the instrumentation fails on it,
improve the instrumentation rather than scan.

## 2. Instrumentation

Script 75 loads Mathlib once and, for every theorem in `Mathlib.Order` with a
proof term under 50,000 nodes, emits a normalized skeleton. The vocabulary
comes from the actual terms, not invented beforehand:
- leaves: bvar `B`, fvar `F`, mvar `M`, sort `T`, literals `Ln/Ls`;
- constants classified by name:
  - `.rec/.brec/.recOn/.casesOn/.below` → `REC` (induction / match);
  - `toX` parent projections → `TOPROJ`;
  - `inst*` / `.inst*` → `INST`;
  - private names → `PRIV`;
  - other named constants → `K(short name)`;
- structure: app `(A …)`, lam `(L …)`, forall `(Q …)`, let `(E …)`,
  projection `(J idx …)`; metadata dropped.

Script 76 groups at two levels:
- **coarse signature**: erase lemma identity (`Kx → K`), variables
  (`B/F → V`), instances (`INST → I`), projection indices (`Jn → J`), literal
  values; keep the full tree. Identical coarse signatures = same proof
  *shape*;
- **sub-key within a group**: the ordered sequence of named lemmas actually
  applied — distinguishes shared derivations from shape coincidences.

## 3. The data-cleaning discovery: generated proof helpers

First clustering was dominated by 8,864 generated declarations: private
`_simp_1_n` helpers and `inst…_proof_n` sub-proofs that the elaborator stores
as theorem constants. They independently re-prove the same small facts
(Finset↔Set coe injection, propositional iff expansions), creating huge
illusory groups. They are now filtered downstream (raw data preserved):
`_private`, `._proof_`, `._simp_`. Corpus for analysis: **17,964 real
theorems**; 11,623 coarse groups; 3,285 multi-member groups.

## 4. Positive control — recovered (41 Fin interval lemmas)

The known family: Mathlib's Fin interval lemmas. Statements vary along five
axes at once —
- Set image (`Fin.image_*`), Finset image (`Fin.finsetImage_*`),
  Finset map (`Fin.map_*Emb`), preimage (`Fin.preimage_*`);
- intervals Icc/Ico/Ioc/Ioo/Ici/uIcc;
- maps `succ` / `castSucc` / `succEmb`;
- every one is proved by the same strategy: delegate to the generic
  `addNat`/`castAdd`/`addNatEmb` interval lemma (`image_addNat_Ico ..`,
  `finsetImage_addNat_uIcc ..`, `preimage_addNat_Ico_addNat ..`, …).

All 41 members land in one coarse group (41 distinct sub-keys — exactly
because the lemma *names* differ while the shape is identical). The coarse
level detects strategy, not lemma identity: the instrumentation works as
designed. Source-adjudicated against the read-only Mathlib files.

Secondary control also recovered: the 28 `dualEquiv_functor/_inverse`
lemmas across the bundled order categories (Preord, PartOrd, LinOrd, Lat,
DistLat, BddOrd, CompleteLat, …) — one proof shape for the order-duality
construction.

## 5. The strategy landscape of Order (descriptive)

- Most proofs are tiny: the largest real shape after filtering is the
  "extract a field of a hypothesis" family (95 members across 14 modules:
  `fun h => h.field`), and its two-hypothesis variant (69 members,
  25 modules).
- Induction/match (`REC`) is present but rare in Order — consistent with the
  area being mostly definitional/propositional; induction-heavy areas
  (Data/Algebra) are the place where skeleton structure should be richest.
- 8,338 singleton groups: nearly half of Order proofs have a unique shape —
  the level of proof-term diversity is high, the opposite extreme from the
  near-perfect factoring seen at declaration level.

## 6. What the pilot establishes

1. Proof-strategy convergence is real and **detectable without persisting all
   proof terms** (140 MB for the area vs the ~70+ GB step-07 corpus).
2. The required positive control passes; the instrumentation is accepted.
3. Scientifically, this crosses the roadmap's boundary: Atlas now has
   instruments on three representations — declaration structure, relation
   structure, and proof structure.

## 7. Next step (pre-authorized by the roadmap)

Scale skeleton extraction to all ten core areas in a **single Lean compile**
(tagging rows with area), then run cross-area strategy-anomaly ranking:
- groups whose members cluster in one area but a few members sit in another
  area (strategy exported across theories);
- pairs of areas with unusually high skeleton-shape overlap;
- within-area strategy outliers (a theorem using a shape common elsewhere and
  rare at home).
Then Phase 4: within-theory anomaly ranking feeding mathematical hypotheses.

## 8. Lean/API lessons recorded

- `Expr.fold` does not exist (again): node counts need explicit recursion.
- `List.get?` is absent in 4.34: use `(l.drop n).head?`.
- `String.get?` wants a byte `String.Pos`; for character indexing use
  `s.toList` + list indexing.
- `Literal.strVal` takes one argument.
- The `|>.method` named pipeline after certain parenthesized expressions
  (`get?`, quoted-string chains) produced parser errors; plain parenthesized
  method calls are reliable.
- Operational: a timed-out harness launch may leave the wrapper shell hung
  with no child process; stop the task and check processes rather than
  relaunching blindly.
