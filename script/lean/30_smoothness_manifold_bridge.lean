import Mathlib

/-!
# Case G probe: real-space vs manifold differentiability

Script 28’s second-largest family (124 pairs) pairs the real/vector-space calculus
predicates with their manifold twins:

  HasFDerivAt      ↔ HasMFDerivAt        DifferentiableAt   ↔ MDifferentiableAt
  fderiv           = mfderiv             ContDiff           ↔ ContMDiff

The discovery question is whether these are two independently-duplicated APIs
(a missing abstraction) or one generic with a proven special case.

## Answer: the manifold notion is already the generic; the vector-space notion is
its model-space specialization, and Mathlib already proves they coincide.

* `MDifferentiableAt I I' f x` is *defined* through charts as
  `ContinuousAt f x ∧ DifferentiableWithinAt 𝕜 (writtenInExtChartAt …) …`
  (`Geometry/Manifold/MFDeriv/Defs.lean:248-256`); its docstring: “This is a
  generalization of `DifferentiableAt` to manifolds.”
* For a normed space the model-with-corners is the identity `𝓘(𝕜, E)`, and one
  file (`Geometry/Manifold/MFDeriv/FDeriv.lean`) already supplies iff/equality
  bridges at EVERY level:
  - `hasMFDerivAt_iff_hasFDerivAt`                         (FDeriv.lean:64)
  - `mdifferentiableAt_iff_differentiableAt`              (FDeriv.lean:81)
  - `mdifferentiableOn_iff_differentiableOn` / …global    (FDeriv.lean:90/99)
  - `mfderiv_eq_fderiv`                                    (FDeriv.lean:118)
  - `contMDiff_iff_contDiff` (ContMDiff/NormedSpace.lean:67)

Everything below kernel-checks both directions of these bridges with the explicit
identity model `𝓘(𝕜, E)` / `𝓘(𝕜, F)` (no `sorry`).
-/

open Topology
open scoped Manifold

namespace Atlas

section Bridge
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (f : E → F) (x : E) (n : ℕ∞)

/-- Pointwise differentiability: both directions. -/
theorem differentiableAt_of_mfd (h : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, F) f x) :
    DifferentiableAt 𝕜 f x :=
  h.differentiableAt

theorem mfd_of_differentiableAt (h : DifferentiableAt 𝕜 f x) :
    MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, F) f x :=
  h.mdifferentiableAt

/-- The derivative LINEAR MAP is literally the same object on model spaces. -/
theorem manifold_deriv_eq_vector_deriv :
    mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F) f x = fderiv 𝕜 f x :=
  mfderiv_eq_fderiv

/-- C^n smoothness: both directions. -/
theorem contMDiff_of_contDiff (h : ContDiff 𝕜 n f) :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n f :=
  h.contMDiff

theorem contDiff_of_contMDiff (h : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n f) :
    ContDiff 𝕜 n f :=
  h.contDiff

/-- The ONE genuine asymmetry the semantic pairs reflect: on a vector space
continuity is DERIVED from differentiability, whereas on a general manifold
`MDifferentiableAt` requires `ContinuousAt` as an explicit conjunct (charts are
only local, so nearby points must stay in the chart domain). -/
theorem vector_diff_implies_continuity (h : DifferentiableAt 𝕜 f x) :
    ContinuousAt f x :=
  h.continuousAt

/- The manifold definition makes the same continuity a separate hypothesis;
`mdifferentiableAt_iff` displays the conjunction `ContinuousAt f x ∧ …`. -/
#check mdifferentiableAt_iff

end Bridge

end Atlas
