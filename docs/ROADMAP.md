# Mathlib Atlas — Status and Roadmap

Last updated: 2026-10-05. For the findings themselves see
[RESULTS.md](./RESULTS.md). This document says where the project stands,
why, and what the candidate next steps are — with a recommendation.

---

## 1. Where we are

### What is built and working

1. **A complete instrumentation layer over Mathlib.** One expensive Lean
   process loads `import Mathlib`; a single traversal of `env.constants`
   extracts, for all 574,391 declarations: kind, type and value Expr,
   module provenance (from `getModuleIdxFor?` → `header.moduleNames`,
   never from name prefixes), namespace, structural features, and
   separately labeled reference edges (16.3M). Raw Expr is preserved.
2. **A discovery pipeline with built-in adjudication.** Semantic
   (TF-IDF / embedding) and structural (type-shape blocking) detectors
   feed fixed ranking procedures; every candidate list is followed by
   downstream Lean falsification, an independent verifier, and a
   case-study/freeze note. False positives are first-class outputs.
3. **Two positive discoveries and five audited nulls** (see RESULTS.md),
   plus a frozen kernel-verified planar-combinatorics spine.

### What the last campaign decided

Scripts 86–90 were explicitly the **last attempt** to extract cross-theory
proof strategies from the current proof representation. They returned
**outcome C**: after normalization, rare-token features cannot see shared
strategy while common-token features flood with Lean idioms; the
idiom/strategy distinction is not structurally encodable at this layer.
The proof line is exhausted at four settings, and the declaration/type/API
level had already reached the two-positive/two-null saturation rule.

**Consequence:** mining the *mature* Mathlib corpus for hidden
cross-area relationships using declarations and proofs is provisionally
finished. This is not a dead end — it is a measured boundary that tells
us which experiments would be redundant.

## 2. The strategic principle behind what comes next

Every campaign so far has climbed a representation ladder:

```
declarations → relations → equivalences → proof strategies → anomalies
```

The mature library has answered thoroughly at every rung. The remaining
scientific question is no longer *"which representation of mature
mathematics should we try next"* but *"what data regime makes
undiscovered structure visible at all."* A standing project observation
points the way: **semantic methods have the most leverage where the
structure is incomplete** — exactly the opposite of the mature-stdlib
regime where structural methods dominated.

## 3. Candidate next steps

### Option A (recommended): underdeveloped / frontier corpora, semantic-first

Move from mature Mathlib to mathematics whose organization humans have
not finished: active research topics (in the project's defined sense —
Fields/Abel/Clay-level open problems with existing Lean code, e.g.
Navier–Stokes, Collatz, multi-color Ramsey, Erdős unit distance, the
Jacobian conjecture), plus in-progress Lean projects and Mathlib's own
less-mature areas.

The hypothesis: in a developing corpus, missing abstractions show up as
semantic clusters with *incomplete* shared structure — the precise
pattern structural detectors are blind to but semantic embeddings handle.

Shape of the campaign:
1. assemble a versioned frontier corpus (declarations + types +
   surrounding API, not full proof dumps);
2. semantic-first clustering with structural features used only for
   adjudication;
3. for each cluster, score *completion gaps* (which members have the
   expected lemmas/instances and which do not);
4. run the same falsification gate as script 66; record nulls.

Why this first: it is the pre-authorized consequence of outcome C, it
reuses nearly all existing instrumentation, and it is the regime where a
genuine new abstraction — rather than a recovered omission — is most
likely to appear.

### Option B: convert the two positives into upstream contributions

Turn PointwiseLift into a real Mathlib abstraction/PR and submit the six
orphan-functor instances (the PR-shaped material already exists in
`notes/66_pr_candidate.md`).

Value: immediate, concrete engineering credibility and citations into the
project. Cost: this is library maintenance, not discovery, and the user
has consistently asked to keep PR-shaped work separate from Atlas
science. Best done as a short, bounded workstream *after* the frontier
campaign shows the method's value, not instead of it.

### Option C: richer proof representation (role-aware or learned)

Build the machinery the 86–90 result says is missing: lemma-role
annotation (which referenced constant carries the argument versus
boilerplate), statement–proof joint features, or learned proof-tree
embeddings.

This is the most engineering-heavy option and it deliberately breaks the
outcome-C freeze. Learned embeddings in particular sacrifice the
auditable, traceable quality of every result so far. It should be
reconsidered only if Option A also comes back null — at which point the
justification ("both mature and frontier corpora resist semantic/
structural discovery") would be strong.

### Option D: paper-forming around the boundary result

Write up the instrumentation boundary itself — a large formal corpus
shown, with labeled precision ledgers and five adjudicated campaigns, to
be almost perfectly factored at declaration level — together with the two
positives. The venue analysis is already parked (arXiv; NeurIPS
Mathematical Reasoning & AI workshop; TMLR; CPP/ICLR following cycles).
The known acceptance risk: reviewers will want labeled precision/recall
and keyword/embedding/LLM baselines, which the frontier campaign would
directly supply. Recommended after Option A, not before.

## 4. Recommendation and sequencing

```
Option A  frontier/underdeveloped corpus, semantic-first   (now)
   │
   ├── strong positive(s) ──► case studies ──► Option B (PRs)
   │                              └──────────► Option D (paper)
   │
   └── audited null ──► Option C (richer proof representation),
                        then re-decide
```

Operating rules carried forward unchanged:

- **two-positive / two-null rule** — two consecutive well-audited nulls
  at a representational level closes that level;
- every new phenomenon is a **decision gate** with pre-registered
  controls, not an open-ended scan;
- everything "the hard way": real kernel verification, no `sorry`,
  Mathlib read-only;
- stop producing candidate lists once a level is saturated; climb the
  ladder or change the data regime.

## 5. Immediate work when Option A is approved

1. Define and version the frontier corpus (problem list → Lean code
   locations; include immature Mathlib areas and external Lean projects).
2. Port the semantic detector to the new corpus; pre-register the
   completion-gap score and positive controls.
3. Run, falsify, verify, freeze — same closed loop as scripts 64–90.
