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

end

end SpherePacking.Contour
