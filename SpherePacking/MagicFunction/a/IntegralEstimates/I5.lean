/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

module
import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.Basic
import SpherePacking.MagicFunction.a.IntegralEstimates.BoundingAuxIci
import SpherePacking.MagicFunction.a.IntegralEstimates.I3
import SpherePacking.Integration.InvChangeOfVariables

/-!
# Bounds for `I₅'`

This file rewrites the auxiliary integral `I₅'` as an integral over `Ici 1` and proves the bound
used in Proposition 7.8 of the blueprint.

## Main definitions
* `g`

## Main statements
* `Complete_Change_of_Variables`
* `I₅'_bounding`
-/

namespace MagicFunction.a.IntegralEstimates.I₅

open scoped Function UpperHalfPlane Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open SpherePacking.Integration.InvChangeOfVariables

noncomputable section Change_of_Variables

variable (r : ℝ)

/-! We begin by performing changes of variables. We use `Ioc` intervals everywhere because of the
way `intervalIntegral` is defined. -/

section Setup

/-- The integrand on `Ici 1` obtained from `I₅'` after an inversion change of variables. -/
@[expose] public def g : ℝ → ℝ → ℂ := fun r s ↦ -I
  * φ₀'' (I * s)
  * (s ^ (-4 : ℤ))
  * cexp (-π * r / s)

end Setup

section Change

lemma Reconciling_Change_of_Variables (r : ℝ) :
    I₅' r = -2 * ∫ t in Ioc 0 1, |(-1 / t ^ 2)| • (g r (1 / t)) := by
  simp only [I₅'_eq_Ioc, g]
  congr 1
  apply setIntegral_congr_ae₀ nullMeasurableSet_Ioc
  apply ae_of_all
  intro t ht
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (MagicFunction.a.IntegralEstimates.I₃.inv_integrand_eq_integrand (t := t) ht.1 r (1 : ℂ))

/-- Rewrite `I₅' r` as an integral of `g r` over `Ici 1` (up to the factor `-2`). -/
public theorem Complete_Change_of_Variables (r : ℝ) :
    I₅' r = -2 * ∫ s in Ici (1 : ℝ), (g r s) := by
  refine (Reconciling_Change_of_Variables (r := r)).trans ?_
  simpa using
    congrArg (fun z : ℂ => (-2 : ℂ) * z)
      (integral_Ici_one_eq_integral_abs_deriv_smul (g := g r)).symm

end Change_of_Variables.Change
end I₅

end MagicFunction.a.IntegralEstimates
----------------------------------------------------------------
