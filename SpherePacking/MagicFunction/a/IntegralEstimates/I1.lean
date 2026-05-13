/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/
module

public import SpherePacking.MagicFunction.a.Basic
import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.MagicFunction.a.IntegralEstimates.I3
import SpherePacking.Integration.InvChangeOfVariables

/-!
# Bounds for `I₁'`

This file rewrites the auxiliary integral `I₁'` as an integral over `Ici 1` and proves the bound
used in Proposition 7.8 of the blueprint.

## Main definitions
* `g`

## Main statements
* `Complete_Change_of_Variables`
-/

namespace MagicFunction.a.IntegralEstimates.I₁

open scoped Function UpperHalfPlane Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral

noncomputable section

variable (r : ℝ)

/-- The integrand on `Ici 1` obtained from `I₁'` after an inversion change of variables. -/
@[expose] public def g : ℝ → ℝ → ℂ := fun r s ↦
  -I * φ₀'' (I * s) * (s ^ (-4 : ℤ)) * cexp (-π * I * r) * cexp (-π * r / s)

lemma Reconciling_Change_of_Variables (r : ℝ) :
    I₁' r = ∫ t in Ioc 0 1, |(-1 / t ^ 2)| • (g r (1 / t)) := by
  simp only [I₁'_eq_Ioc, g]
  refine setIntegral_congr_ae₀ nullMeasurableSet_Ioc (ae_of_all _ fun t ht => ?_)
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (MagicFunction.a.IntegralEstimates.I₃.inv_integrand_eq_integrand (t := t) ht.1 r
      (cexp (-π * I * r)))

/-- Rewrite `I₁' r` as an integral of `g r` over `Ici 1`. -/
public theorem Complete_Change_of_Variables (r : ℝ) :
    I₁' r = ∫ s in Ici (1 : ℝ), (g r s) :=
  (Reconciling_Change_of_Variables (r := r)).trans <| by
    simpa using
      (SpherePacking.Integration.InvChangeOfVariables.integral_Ici_one_eq_integral_abs_deriv_smul
        (g := g r)).symm

end

end MagicFunction.a.IntegralEstimates.I₁
