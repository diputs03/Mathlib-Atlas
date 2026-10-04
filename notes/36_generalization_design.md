# 36 — Theorem generalization / specialization links (plan item 12)

## Question
Distinct from the analogy sweeps (16–33, which looked for *shared shape across
different concepts*), item 12 asks the **generalization** question: where does
Mathlib prove the *same statement repeatedly over concrete carriers* while never
stating the polymorphic (generic) version? A cluster of per-carrier specializations
with no generic member is a candidate for a missing general theorem.

## Generic vs specialized (the key test)
Read directly from each theorem's `typeAst` forall spine:

* **GENERIC** — the prefix binds a universe-sorted type variable, i.e. a binder
  whose type is `Sort`/`Type` (`binderType.tag == "sort"`). Example `add_comm`:
  `{G : Type u_1} [AddCommMagma G] (a b : G)`. Validated: `add_comm`,
  `mul_comm`, `le_refl` are generic.
* **SPECIALIZED** — no sort binder; the objects have concrete carrier types.
  Example `Nat.one_mem_properDivisors_iff_one_lt`: `{n : Nat}`.

Theorems are grouped by a signature that is invariant under specializing the
carrier (the object-argument arity does not change):

    (conclusionHead, sorted constraint-class tuple, nDefault explicit args)

A group is **covered** when it has ≥1 generic member (the general theorem exists);
a **generalization opportunity** is a specialized-only group with ≥3 specialized
members over ≥2 distinct carriers (namespace roots).

## Funnel (330,601 theorems)
| stage | count |
|---|---|
| Mathlib theorems considered | 330,601 (generic 287,788 / specialized 42,813; 47,810 skipped: no skeleton/head/Ast) |
| shape groups | 80,747 |
| — pure-generic groups | 76,932 |
| — covered (generic + specialized) | 763 |
| — specialized-only groups | 3,052 |
| raw opportunities (≥3 spec, ≥2 carriers) | 348 |
| − conclusion head is itself a class/prop-fact (per-carrier fact derivations) | 152 |
| − bare logical head (Eq/Iff/Exists/order/mem…) or empty constraints, or namespace artifacts | 191 |
| **surviving opportunities** | **5** |

### Why the two filters are mandatory
* **Class/prop-fact heads** (`NeZero`, `Nontrivial`, `CharZero`, `Fact`,
  `CategoryTheory.*.PreservesLimits`, …) are *necessarily* per-carrier: a generic
  `NeZero α` for arbitrary `α` is not a theorem, it is a hypothesis. These are
  instance/fact derivations, not repeated lemmas.
* **Bare logical heads** (`Eq`, `Iff`, `Exists`, `LE.le`, …) cannot identify a
  common statement from head+constraints+arity: two equalities in the same
  algebraic setting with the same arg count are usually unrelated equalities.
  Gotcha: the head may be qualified (`LE.le`) whose **last segment** is `le`,
  while the bare form is `Eq`; comparison is case-insensitive on the last
  segment. A genuine missing generic lemma needs a *named operator* head and
  nonempty constraint hypotheses.

## The 5 survivors, triaged
1. `CategoryTheory.Limits.IsZero`, ndef 1, `[Subsingleton]`, 6 concrete
   categories (GrpCat/CommGrpCat/AddGrpCat/AddCommGrpCat/SemiNormedGrp/
   SemiNormedGrp₁): members are all `*.isZero_of_subsingleton` — the **only
   genuinely repeated statement**.
2. `Differentiable` (`[NeZero]`, DirichletCharacter/ZMod): heterogeneous
   L-function differentiability facts (different functions, same head).
3. `ContinuousOn` (`[NeZero]`, ArithmeticFunction/DirichletCharacter): same,
   one area (NumberTheory), different statements.
4. `IntervalIntegrable` (IsLocallyFiniteMeasure): carriers are namespace
   artifacts of the concept itself, one area (Analysis).
5. `IsQuotientCoveringMap` (`[NeZero]`, Circle/Complex): per-space npow/zpow
   covering facts.

2–5 are heterogeneous statements that share only a predicate head — noise.

## Lean boundary check (37) — the one repeated family is NOT a missing generic
`script/lean/37_generalization_boundary.lean` (exit 0, no warnings/sorry):

```
@IsZero X : Prop
IsZero.unique_to   : IsZero X → ∀ Y, Nonempty (Unique (X ⟶ Y))
IsZero.unique_from : IsZero X → ∀ Y, Nonempty (Unique (Y ⟶ X))
GrpCat.isZero_of_subsingleton     (G : GrpCat)     [Subsingleton ↑G] : IsZero G
CommGrpCat.isZero_of_subsingleton (G : CommGrpCat) [Subsingleton ↑G] : IsZero G
ModuleCat.isZero_of_subsingleton  (M : ModuleCat R) [Subsingleton ↑M] : IsZero M
```

`IsZero X` is a **categorical** condition (unique morphism in and out for every
Y). `[Subsingleton X]` is a **type-theoretic** condition (all *elements* of the
carrier are equal). In an arbitrary category the latter says nothing about the
hom-sets `X ⟶ Y`, so `Subsingleton X → IsZero X` is not provable in
`CategoryTheory.Limits` — and indeed no such generic lemma exists there. Each
concrete category bridges the two only through its **own** hom extensionality
(`ext x; Subsingleton.elim; map_one`). The "generic" statement that would suffice
is `IsZero` itself, so introducing it would be circular. The repetition is
irreducible, structurally the same lesson as case D (22): identical-looking
lemmas repeated because each needs the concrete carrier's extensionality.

## Verdict
**Negative result (0 missing generalizations).** Of 330,601 theorems, the
overwhelming majority of repeated per-carrier shapes already have a polymorphic
form (763 covered groups; 76,932 pure-generic). After removing the two large
classes of detector artifacts, only one family is a true repeated statement
(`isZero_of_subsingleton`), and the Lean kernel shows why it cannot be made
generic. This is complementary evidence to 34/35: Mathlib's algebraic hierarchy
is abstracted where the type theory permits, and the residual per-carrier
repetition sits exactly at boundaries where categorical structure cannot be
derived from carrier-level subsingleton/extensionality facts.

## Files
* `script/python/36_generalization_links.py` — streaming classifier + grouping + filters
* `script/python/verify_generalization_links.py` — independent rebuild; VERIFICATION OK
* `script/lean/37_generalization_boundary.lean` — kernel boundary check, exit 0
* `data/generalization_opportunities.jsonl` (5 rows), `data/generalization_summary.json`
