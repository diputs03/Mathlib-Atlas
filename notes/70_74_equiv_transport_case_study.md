# 70–74 — Equiv/transport experiment: case study and the decision-gate null result

Date: 2026-09-24

Scripts:



* `script/python/70_equiv_candidates.py` — witness scan + API footprints + gap

* `script/python/71_rank_equiv_candidates.py` — coverage-based ranking

* `script/lean/72_equiv_transport_falsification.lean` — Lean falsification

  (EXIT=0, zero-byte log, no sorry)

* `script/python/73_adjudicate_equiv.py` — every pair given a definite class

* `script/python/verify_equiv_experiment.py` — ALL CHECKS PASSED

  Data: `data/equiv_*.jsonl/json`.

## 1. The question

After horizontal analogies (PointwiseLift, §17), class-integration gaps

(orphan functors, §18), and the falsified vertical axis (§19), this

experiment tests the **equivalence/transport axis**:

> When Mathlib already knows an equivalence 
>
> `e : A ≃ B`
>
> , does it nevertheless
> fail to transport structure or lemmas across it — and is a generic transport
> abstraction genuinely missing?

The experiment was run as a **decision gate**, not an open-ended scan: after

adjudication the only question is whether a new kind of incompleteness was

found that Atlas's existing representations can explain.

## 2. Method (why the gap is measured the way it is)

A naïve scan over all theorem pairs would drown in coincidences, so the

corpus was built in stages:



1. From the conclusion-term layer (script 68), take declarations whose

   conclusion is exactly `(c Equiv α β)` — **plain&#x20;**`Equiv`**&#x20;only**; every other

   bundled iso (AddEquiv, RingEquiv, Homeomorph…) is an Equiv with extra

   fields and reduces to this case.

2. Keep witnesses where **both carriers are constructor-headed** (bare

   variables have no API footprint). 1,135 Equiv witnesses; 492 with two

   constructor carriers; **276 constructor pairs**.

3. Footprint of a constructor = declarations referencing it (reference edges,

   core Mathlib areas; 532,708 kept edge rows; 201,291 carrier-related

   sources).

4. **Transported counterpart test.** A canonical statement key is built per

   declaration by (a) holing instance-binder types (as in 69) and (b) replacing

   the two carrier constants with a fixed token. Keys present on both sides =

   transported API (`matchedKeys`); one-sided keys = the gap.

5. Instance footprint from `atlas_instances` (className sets per targetHead).

Floors: ≥20 declarations per footprint, ≥5 one-sided declarations.

**253 eligible pairs.**

## 3. The decisive statistic: transport coverage

Coverage = matched keys / min(keys on either side) — how much of the smaller

API is actually identified by the Equiv. Distribution over 253 pairs:



| coverage     | pairs |
| ------------ | ----- |
| 0.00–0.10    | 232   |
| 0.10–0.35    | 12    |
| 0.35–0.60    | 8     |
| 0.60–0.85    | 1     |
| 0.85–1.00    | 0     |
| exactly 1.00 | 0     |

The Equiv declarations Mathlib contains are overwhelmingly **one-off**

**encodings/unpackings**, not API identifications. The nine pairs above the

0.35 gate were all source-adjudicated.

## 4. The nine gated pairs, after Lean falsification



1. **CStarMatrix ↔ Matrix** — `def CStarMatrix m n A := Matrix m n A`;

   `ofMatrix = Equiv.refl`. The type copy exists solely to attach the operator

   norm and C\* instances (the file's implementation notes document the

   uniformity/bornology engineering). Verified in Lean: the defeq, the

   `Equiv.refl`, and that a "missing" Matrix lemma (`submatrix`) applies to

   CStarMatrix by conversion. Class: **representation\_boundary**.

2. **ConnectedComponents ↔ ZerothHomotopy** — clopen-component quotient vs

   path-component quotient; the Equiv exists only under

   `LocallyPathConnected`, built from proof that the two setoids are equal.

   The Homeomorph was not named upstream; it was **proved downstream in six**

   **lines** (`ccHomeomorphZh`, via `continuous_quot_map`). Derivable alias,

   not a missing mechanism. Class: **representation\_boundary**.

3. **MaximalSpectrum ↔ PrimeSpectrum** — Equiv conditional on

   `IsArtinianRing` (then every prime is maximal), with transport lemmas

   (`comp_asIdeal`) already present; the general relation is the subtype

   inclusion. Class: **representation\_boundary**.

4. **MaximalSpectrum ↔ Subtype** — literally the subtype of maximal ideals.

   Class: **representation\_boundary**.

5. **RegularWreathProduct ↔ Prod** — `equivProd` unpacks `D ≀ᵣ Q` into

   `(Q → D) × Q` for cardinality; the group law is a semidirect construction

   that cannot live on a generic product. Class: **false\_positive**.

   6–9. **BotHom/TopHom, OrderAddMonoidIso/OrderMonoidIso, sInfHom/sSupHom,**

   **InfTopHom/SupBotHom** — order-dual / to\_additive pairs with naturally

   side-specific lemmas. Class: **intentional\_asymmetry**.

Near-gated pairs examined and classified: **PSigma/Sigma** (generic

foundational encoding; instance transport demonstrated), **WithBot/WithTop**

(duals with `toDual/ofDual`), **InfHom/SupHom** (duals), **MonoidHom/ShelfHom**

(coarse match, false positive).

## 5. Adjudication of all 253 pairs



| class                             | count |
| --------------------------------- | ----- |
| representation\_boundary          | 124   |
| false\_positive                   | 122   |
| intentional\_asymmetry            | 7     |
| generic\_transport\_exists        | 0     |
| already\_symmetric                | 0     |
| **missing\_transport\_lemma**     | **0** |
| **missing\_generic\_abstraction** | **0** |

(The bulk rules: dual/to\_additive name pattern → intentional\_asymmetry;

footprint imbalance with ratio <0.10 → representation\_boundary; otherwise

false\_positive. Every rule is stated in script 73 and independently checked.)

## 6. The decision-gate answer

**No new kind of mathematical incompleteness was found.** Where an Equiv

exists, one of three things is true, each already represented:



* the types are defeq or a conditional coincidence and the Equiv is the

  identity/quotient map (representation boundary — the type difference is the

  point);

* the Equiv is an unpacking used for cardinality/encoding (false positive);

* the pair is an order/additive dual with intentionally side-specific lemmas.

A single generic "transport everything" theorem cannot exist: transporting a

structure always requires proving its preserved properties, so transport is

necessarily class-by-class; Mathlib supplies those lemmas wherever the

carrier relation genuinely identifies structures, and the only derivable

missing alias found (a Homeomorph for π₀ under local path-connectedness) is a

six-line convenience, not an abstraction.

## 7. False-positive taxonomy added to Atlas's ledger

New classes from this campaign:



* **defeq type copies with&#x20;**`Equiv.refl` (CStarMatrix): API gaps are

  illusory — kernel conversion crosses them;

* **conditional equivalences between distinct quotient relations**

  (ConnectedComponents/ZerothHomotopy): the witness exists exactly where the

  relations coincide;

* **unpacking Equivs** (wreath product, many encodings): cardinality/

  construction tools with no API-identification content;

* **head-constructor over-attribution**: carrier extraction on the head

  constant alone pairs a wrapper with every lemma of the ubiquitous inner

  constructor (Prod/Subtype/Option);

* **dual-side lemmas mistaken for asymmetries** (WithBot/WithTop, Inf/Sup).

## 8. Instrumentation-cost note

The experiment was built entirely on the standing conclusion-term layer

(225,535 rows, \~1.16 GB) plus the edge file; no proof-term persistence (step

07\) was needed. End-to-end Python cost: \~3 min for the witness scan, \~6 min

for the edge stream, seconds for ranking/adjudication. The only expensive

step was the single Lean falsification compile. Two operational wedges

occurred (machine-level, multi-hour; one required waiting out, one

self-recovered); lesson reinforced: **never run more than one Lean compile,**

**and launch compiles from a single tracked shell** (parallel/timed-out

relaunches are what wedge the machine).