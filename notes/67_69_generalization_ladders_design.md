# 67/68/69 — Vertical generalization ladders: a falsified phenomenon and the
# instrumentation map it produced

Date: 2026-09-23
Scripts:
- `script/python/67_generalization_ladders.py` (coarse first pass)
- `script/lean/68_conclusion_terms.lean` (new compact term layer)
- `script/python/69_precise_generalization_ladders.py` (term-precise pass)
- `script/python/verify_precise_ladders.py` (ALL CHECKS PASSED)
Data:
- `data/atlas_conclusion_terms.jsonl` (225,535 rows)
- `data/generalization_ladder_*` (coarse), `data/precise_ladder_*` (precise)

## 1. The phenomenon under test

Scripts 64/66 found structure along a *horizontal* axis (parallel analogies
across areas; integration gaps for an existing class). This campaign tests the
orthogonal, *vertical* axis predicted in the long-term plan ("generalization
opportunities: theorem families whose types exhibit a common pattern,
suggesting a more general theorem"):

> The same statement, proved at two or more typeclass-strength levels, with the
> stronger-hypothesis version a redundant special case of a weaker one.

A confirmed ladder would be a candidate missing most-general theorem; a
falsified ladder teaches Atlas another class of false positives.

## 2. Stage 67 — coarse detection and its detectability boundary

First pass used only the compact feature layer: blocks on
(conclusion head, explicit-binder counts, implicit/default counts, type depth,
type-node bucket), with weakening decided by matching constraint-class
multisets against the real class hierarchy (every stronger occurrence must be
a descendant of a weaker one), plus same-namespace and shared-name-token
guards.

Funnel: 296,268 eligible theorems; 129,860 blocks; 37,407 used;
**12,480 weakening pairs; 610 candidate ladders** after generated instance
proofs were filtered. Adjudication of the top candidates showed the pairs are
**shape coincidences between unrelated statements** (`Ideal.ofList_cons` vs
`Ideal.ramificationIdx_eq_one`; `Finset.offDiag_inter` vs
`Finset.image_sdiff_product`): node counts and a conclusion head cannot
distinguish "same statement, weaker hypotheses" from "different statements of
the same coarse shape". The honest output of stage 67 is a **detectability
boundary**: vertical subsumption requires term-level conclusion structure.

## 3. Stage 68 — the minimal instrumentation layer

Full proof persistence (step 07, ~70+ GB) is far more than the question needs.
The minimal layer is the **type only**, split into the outer forall prefix
(per binder: `BinderInfo` tag + binder-type term) and the conclusion term,
serialized as S-expressions (constants by name; sorts; de Bruijn indices;
literals; projections; metadata dropped).

Engineering outcomes (all recorded, none silent):
- A first unrestricted run died (~590 MB, 39k rows) on pathological
  CategoryTheory terms. Fixes: serialize only the ten core areas; per-term
  node budget 20,000 with a truncation flag; flush every 10,000 rows.
- Final run: scanned 777,251 constants; **225,535 rows; 1,231 truncated
  (0.55%)**; EXIT=0; ~34 min. Output ~1.16 GB — versus ~70+ GB for full proof
  persistence, a ~60x instrumentation reduction for this question.
- Lean notes: `prefix` is a reserved keyword; inline `match` in argument
  position needs parentheses; `Std.HashSet.ofList`; `privateToUserName?`
  application precedence; binders named in patterns must be used or prefixed
  `_` (acceptance bar includes zero warnings).

## 4. Stage 69 — term-precise ladders and the adjudicated null result

Canonical statement key: the full type with every **instance-binder type
replaced by a fixed hole** (positions and de Bruijn indices preserved —
deleting binders would shift indices), plus the conclusion. Same key ⇒ same
statement with only the exact class constraints differing. Constraint class
heads come from the instance terms; direction uses the hierarchy as before.

Restrictions found necessary during adjudication:
- definitions/classes with a sort conclusion (`Type u → [Mul α] → Type u`) all
  collapse to one key because a constructor's identity is its own name, absent
  from its type; the pass is restricted to **theorems whose conclusion contains
  a constant relation**.

Funnel: 170,579 canonical theorem statements; **3,158 groups with ≥2
members**; after removing same-strength restatements, **7 candidate ladders,
zero cross-area**. Every one was then checked against Mathlib source and
classified as an expected pattern:

1. `GroupWithZero.toNontrivial` → `Semifield.toNontrivial` (and the
   `toZPow/toZSMul` families): **parent projection constants** — the
   hierarchy edges themselves, not lemmas.
2. `exists_linearIndependent_algEquiv_apply` vs its `_private …_of_finite`
   counterpart, and the analogous Unramified pair: the **private
   implementation alias of the same declaration**.
3. `IsLeftCancelSMul.left_cancel` vs `IsCancelSMul.left_cancel` (and VAdd):
   `IsCancelSMul extends IsLeftCancelSMul`; the subclass lemma is proved
   directly from the parent's (`IsLeftCancelSMul.left_cancel'`) — a deliberate
   **dot-notation convenience on a subclass**, so users need not know the
   hierarchy.
4. `IsKrasner.of_completeSpace` vs `of_completeSpace_of_normal`: a same-file
   local `let` convenience, not a top-level duplicate.
5. `FiniteDimensional.mem_span_of_iInf_ker_le_ker` vs
   `mem_span_of_iInf_ker_le_ker`: genuinely different hypotheses
   (`FiniteDimensional E` vs `Finite ι`); distinct tools, not same-statement
   special cases.

**Result: the vertical generalization phenomenon is falsified over the mature
stdlib.** Same-statement theorems at redundant strength levels essentially do
not exist: 170,579 statements, 3,158 multi-member groups, zero unclassified
ladders. Mathlib's assumption-weakening culture has already closed this axis,
matching the earlier headline that the mature stdlib is "almost perfectly
factored".

## 5. The lasting output — an instrumentation map

The campaign's reusable artifact is a map from phenomenon class to the
instrumentation layer at which it becomes detectable, each row now with an
adjudicated result:

| Phenomenon axis | Layer needed | Result |
|---|---|---|
| Horizontal parallel analogies (cross-area) | coarse features + semantic TF-IDF (64) | PointwiseLift confirmed; 549 clusters mostly known patterns |
| Class-integration gaps | coarse structural features (66) | 6/6 orphan functors confirmed clean omissions |
| Vertical subsumption / weakening | conclusion terms (68/69) | **null**: 0 unclassified ladders |
| Proof-strategy convergence, automation genealogy | proof/value terms (step 07) | not yet testable at scale |
| Under-developed frontier structure | semantic-first matching (52) | semantic leads where structure is incomplete |

New false-positive classes taught to Atlas (added to the 66 ledger):
- coarse-shape coincidence of unrelated statements (need term comparison);
- sort-conclusion constructors grouped across distinct declarations;
- hierarchy parent projections mistaken for lemmas;
- private implementation aliases mistaken for separate theorems;
- subclass dot-notation convenience lemmas mistaken for redundancies;
- same statement name under genuinely different hypothesis regimes.

## 6. Disposition

- The conclusion-term layer (68) is retained as a standing layer: it is the
  natural substrate for future theorem-level questions (e.g., missing-lemma
  prediction, equivalence/transport gaps) at ~1/60 the cost of step 07.
- No PR material arises from this campaign (the 7 ladders are expected
  patterns); nothing is frozen beyond noting this axis is closed for the
  mature stdlib.
- Next discovery should move off the "same shape" family entirely — candidate
  phenomena: isomorphism/transport gaps (Equiv constants with un-transported
  instances), proof-strategy convergence on targeted slices (Lean-level
  extraction of proof skeletons, not full terms), or anomaly ranking within
  theory clusters.
