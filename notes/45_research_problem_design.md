# 45 — Footprint of famous modern/open research problems in the Mathlib corpus

## Reframing "frontier"
The user means **research-level / famous open problems** (Fields/Abel-class and
Clay-millennium style), not Mathlib's internal area buckets. This script makes
that operational: for a curated problem list it measures, reproducibly from
`atlas_features.jsonl` at commit `bbcd1968`, the **formal footprint** —
`direct` = declarations whose name names the problem/object, `support` =
declarations in the adjacent-theory modules an attack would build on — and
records the actual named declarations. Fermat's Last Theorem is included as a
*positive control* of a famous theorem with real in-corpus Lean code.

## Footprint table (all counts corpus-grounded, verifier VERIFICATION OK)

| problem | status | direct | support | principal present scaffolding |
|---|---|---|---|---|
| **Erdős unit-distance (plane)** | **named object present** | **31** | 258 | `SimpleGraph.UnitDistEmbedding`; Turán 108, Erdős–Stone–Simonovits 41, Zarankiewicz 31 |
| **Jacobian conjecture** | machinery only | 0 | **2,513** | MvPolynomial; étale maps 960; `SubmersivePresentation.jacobian_isUnit`; change-of-variables Jacobian |
| **Multicolor Ramsey numbers** | machinery only | 0 | 837 | Clique 341, vertex coloring 147, edge labeling 73, Turán 108, Erdős–Stone 41 |
| **Collatz (3x+1)** | machinery only | 0 | 303 | PeriodicPts 184, OmegaLimit 66, FixedPoints 48 |
| **Navier–Stokes (Clay)** | machinery only (no PDE) | 0 | 208 | **ODE only**: Picard–Lindelöf 98, ExistUnique, Grönwall; **no PDE layer** |
| FLT (positive control) | **partly proved** | 305 | 280 | `FLT.Three` 191 (n=3, Eisenstein descent), `FLT.Four` 28 (`Fermat42`, n=4) |

## Per-problem assessment

### Erdős unit-distance — the most research-ready target
`Mathlib.Combinatorics.SimpleGraph.UnitDistance.Basic` (31 decls) already
defines `SimpleGraph.UnitDistEmbedding` — an embedding whose graph edges are
exactly the pairs at a fixed distance. The extremal-graph machinery needed to
*bound* how many such edges exist (Turán, Erdős–Stone–Simonovits, Zarankiewicz)
sits right beside it (258 decls). What is absent is the analytic/geometric side
of the Erdős bound (the actual `u(n)=O(n^{4/3})` estimate and the plane
incidence/crossing-number argument). **Object exists, extremal framework exists,
open estimate absent** — the smallest gap to a research statement.

### Jacobian conjecture — deepest scaffolding, no statement
2,513 support decls. The algebraic geometry of the hypothesis is heavily built:
multivariate polynomials (`MvPolynomial.Equiv/Eval`), étale morphisms
(`RingTheory.Etale.*`, Kähler differentials, quasi-finite/unramified), and
explicitly `Algebra.SubmersivePresentation.jacobian_isUnit` — a theorem whose
hypothesis is precisely "the Jacobian determinant is a unit." The
measure-theoretic Jacobian/change-of-variables (`MeasureTheory.Function.Jacobian`,
87) supplies the analytic determinant theory. What is missing is the
endomorphism statement (an étale/algebraically-`jacobian_isUnit` endomorphism of
affine n-space is an automorphism). Note the elliptic-curve `WeierstrassCurve.
Jacobian` decls are an unrelated name collision and were excluded.

### Multicolor Ramsey numbers — scaffolding without the theorem
No `Ramsey` module and no Ramsey theorem/number declaration at this commit, but
837 decls of exactly the right combinatorics: cliques (monochromatic target),
vertex/edge coloring and edge labeling (the coloring), and the extremal theory
(Turán/Erdős–Stone/Zarankiewicz) that supplies the complementary bounds. The
missing piece is the Ramsey theorem itself and a `RamseyNumber` API; specific
small numbers would then be finite decidability goals (the kind external
projects close by computation).

### Collatz — dynamical vocabulary, no map
No `Hailstone`/Collatz declaration at this commit. The dynamical-systems
language a proof needs is present (periodic points, omega-limit sets, fixed
points — 303 decls), but the Collatz iteration itself and any finite-range
verification are absent. A formalization would start by defining the map inside
this vocabulary.

### Navier–Stokes — the least ready: ODE yes, PDE no
Zero Navier/Stokes/PDE declarations. Mathlib has a solid **ordinary** DE layer
(Picard–Lindelöf existence/uniqueness, Grönwall, integral curves — 208 decls)
but no partial-differential-equation existence/evolution framework. The Clay
problem requires weak/Sobolev-space PDE machinery that is not present; this is
the largest gap of the five.

### Positive control — what "famous theorem with Lean code" looks like
`Mathlib.NumberTheory.FLT.*` proves the n=3 case (`FLT.Three`, full infinite
descent in Eisenstein integers, 191 decls) and the n=4 case (`FLT.Four`,
`Fermat42` descent, 28), with `FLT.Basic` giving the Nat/Int/Rat equivalence
formulations (`fermatLastTheoremFor_iff_rat`, TFAE). General FLT is not
formalized. This is the in-corpus template: a famous problem reduced to specific
cases with heavy dedicated scaffolding.

## Readiness ranking (named object + scaffolding density)
1. **Erdős unit-distance** — named object + adjacent extremal theory; needs the
   geometric incidence bound.
2. **Jacobian conjecture** — densest algebraic scaffolding incl. the exact
   determinant-unit hypothesis; needs the endomorphism/automorophism statement.
3. **Multicolor Ramsey** — broad combinatorial scaffolding; needs Ramsey's
   theorem + a number API.
4. **Collatz** — dynamics vocabulary present; needs the map defined.
5. **Navier–Stokes** — needs an entire PDE layer first.

## Scope note (external, NOT in this corpus)
`external/mathlib4` is read-only at the pinned commit; research-frontier Lean
formalizations of major results (e.g. the Liquid Tensor Experiment on condensed
mathematics, the sphere-eversion project) live in dedicated blueprint
repositories layered on Mathlib, which is where these open problems would be
attacked. Atlas's role is to map, from the corpus, exactly the dependency
frontier each such project would start from — a natural follow-up is to compute,
for the top-ranked target, the closure of existing scaffolding and the specific
missing lemmas between it and the open statement.

## Verification & files
`verify_research_problem_footprint.py` independently recomputes direct/support
counts, module lists, kind counts, derived status and summary cross-checks →
VERIFICATION OK.
* `script/python/45_research_problem_footprint.py`, `verify_research_problem_footprint.py`
* `data/research_problem_footprint.jsonl` (6 rows), `data/research_problem_summary.json`
