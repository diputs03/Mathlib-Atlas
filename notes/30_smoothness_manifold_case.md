# Case G — Real-space vs manifold differentiability

**Probe:** `script/lean/30_smoothness_manifold_bridge.lean` — kernel-checks,
exit 0, no warnings, no `sorry`.
**Trigger:** script 28’s second-largest hidden-candidate family (124 pairs):
`HasFDerivAt↔HasMFDerivAt`, `DifferentiableAt↔MDifferentiableAt`,
`fderiv=mfderiv`, `ContDiff↔ContMDiff`, across the Analysis/Geometry boundary.

## Question

Are the vector-space and manifold calculus APIs two independent duplications of
the same theory (a missing common abstraction), or one generic with a proven
special case?

## Grounded facts (commit bbcd196)

- The **manifold notion is defined first as the generic**, through charts:
  `MDifferentiableAt I I' f x := LiftPropAt (DifferentiableWithinAtProp I I') f x`,
  i.e. `ContinuousAt f x ∧ DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f)
  (range I) (extChartAt I x x)` — `Geometry/Manifold/MFDeriv/Defs.lean:248-256`.
  Its docstring states verbatim: *“This is a generalization of
  `DifferentiableAt` to manifolds.”*
- A normed space is a manifold over itself via the identity model-with-corners
  `𝓘(𝕜, E)`. The single file `Geometry/Manifold/MFDeriv/FDeriv.lean` already
  proves the coincidence at **every** level:

  | level | bridge | location |
  |---|---|---|
  | has-derivative filter | `hasMFDerivAt_iff_hasFDerivAt` | FDeriv.lean:64 |
  | differentiable at a point | `mdifferentiableAt_iff_differentiableAt` | FDeriv.lean:81 |
  | on a set / everywhere | `mdifferentiableOn_iff…`, `mdifferentiable_iff_differentiable` | :90/:99 |
  | derivative linear map | `mfderiv_eq_fderiv` | FDeriv.lean:118 |
  | C^n smoothness | `contMDiff_iff_contDiff` (+ `.contDiff`/`.contMDiff` aliases) | ContMDiff/NormedSpace.lean:67 |

## Kernel-checked content of the probe

With explicit identity models `𝓘(𝕜, E)`, `𝓘(𝕜, F)` the probe closes both
directions of each bridge by the existing aliases:

- `differentiableAt_of_mfd` / `mfd_of_differentiableAt`;
- `manifold_deriv_eq_vector_deriv : mfderiv 𝓘 𝓘 f x = fderiv 𝕜 f x`;
- `contMDiff_of_contDiff` / `contDiff_of_contMDiff`;
- `vector_diff_implies_continuity : DifferentiableAt 𝕜 f x → ContinuousAt f x`.

(The first compile failed only because the `𝓘(…)` notation is `scoped[Manifold]`;
`open scoped Manifold` fixed it — recorded as a toolchain note.)

## The one genuine asymmetry

The semantic pairs are not pure synonymy: **`MDifferentiableAt` carries
`ContinuousAt` as an explicit conjunct, whereas `DifferentiableAt` derives
continuity for free** (`DifferentiableAt.continuousAt`, FDeriv/Basic.lean:659).
The reason is mathematical, not an oversight: on a general manifold charts are
local, so points near `x` must first be guaranteed to stay in the chart domain;
on a vector space the chart is global (`writtenInExtChartAt` is essentially the
identity) and continuity follows from the derivative. The bridge proof in
Mathlib is exactly `⟨H.2, fun H => ⟨H.continuousAt, H⟩⟩` — drop the conjunct one
way, supply it the other. `#check mdifferentiableAt_iff` displays this.

## Verdict

**Already abstracted — no new construction warranted.** The manifold predicates
*are* the generic (chart-based); the real-space predicates are the identity-model
specialization, and the equivalence is already proved and aliased at every level.
Like cases D and F, script 28 rediscovered a real mathematical relationship that
Mathlib already formalizes; the residual is naming duplication
(`…` vs `M…`) and the one explained continuity asymmetry, not missing machinery.
This is a **negative/structural result with kernel-verified bridges**, and it
closes the 124-pair smoothness family.
