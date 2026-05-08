module

import Mathlib.Order.Filter.Basic

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.TangentCone.Defs
public import Mathlib.Analysis.Calculus.DiffContOnCl

public import SpherePacking.Basic.Domains.WedgeSet
public import SpherePacking.ForMathlib.ScalarOneForm

/-!
# Regularity lemmas on `wedgeSet` for contour arguments

The contour deformation step in the `perm_J12` development uses the Poincare lemma for curve
integrals on `wedgeSet`. For a scalar 1-form `scalarOneForm f`, the Poincare lemma requires:
- `DiffContOnCl` regularity on `wedgeSet`; and
- symmetry of `fderivWithin` on tangent directions (i.e. the form is closed).

This file provides small wrappers establishing these hypotheses from complex differentiability of
`f` on the upper half-plane.
-/

namespace SpherePacking.Contour

noncomputable section

/--
Upgrade complex differentiability on the upper half-plane to `DiffContOnCl` on `wedgeSet`.

The only boundary point that needs extra care is `z = 1`; we use the supplied `Tendsto` and value
assumptions there.
-/
public lemma diffContOnCl_wedgeSet_of
    {f : ℂ → ℂ}
    (hdiffC : DifferentiableOn ℂ f UpperHalfPlane.upperHalfPlaneSet)
    (htend : Filter.Tendsto f (nhdsWithin (1 : ℂ) (closure wedgeSet)) (nhds 0))
    (hval : f (1 : ℂ) = 0) :
    DiffContOnCl ℝ f wedgeSet := by
  refine ⟨(hdiffC.restrictScalars ℝ).mono wedgeSet_subset_upperHalfPlaneSet, fun z hzcl => ?_⟩
  by_cases h1 : z = (1 : ℂ)
  · subst h1; simpa [ContinuousWithinAt, hval] using htend
  · exact (hdiffC.continuousOn.continuousAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
        (mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one hzcl h1))).continuousWithinAt

end

end SpherePacking.Contour
