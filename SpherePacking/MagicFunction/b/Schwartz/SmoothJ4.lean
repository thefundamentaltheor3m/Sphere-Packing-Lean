module
public import SpherePacking.MagicFunction.b.Basic
public import SpherePacking.MagicFunction.b.PsiBounds

import SpherePacking.MagicFunction.b.Schwartz.SmoothJ24Common
import SpherePacking.MagicFunction.IntegralParametrisationsContinuity


/-!
# Smooth J4

This file proves smoothness/decay bounds for `RealIntegrals.J₄'` by differentiating under the
integral sign.

## Main statements
* `contDiff_J₄'`
* `decay_J₄'`
-/


namespace MagicFunction.b.Schwartz.J4Smooth

noncomputable section

open scoped Interval Manifold Topology UpperHalfPlane

open Complex Real Set MeasureTheory Filter intervalIntegral

open MagicFunction.Parametrisations
open MagicFunction.b.RealIntegrals
open MagicFunction.b.PsiBounds
open SpherePacking.ForMathlib

/-- Smoothness of `J₄'` (the primed radial profile).

The prime in `contDiff_J₄'` refers to the function `J₄'`. -/
public theorem contDiff_J₄' : ContDiff ℝ (⊤ : ℕ∞) J₄' := by
  refine
    (SmoothJ24Common.contDiff_of_eq_I0_mul (z := z₄') (c := (-1 : ℂ)) (f := J₄')
      (hfEq := ?_) continuous_z₄'
      (fun t => by simpa using (MagicFunction.Parametrisations.im_z₄'_pos_all t))
      (fun t => norm_z₄'_le_two t))
  intro x
  simp [SpherePacking.Integration.SmoothIntegralCommon.I, RealIntegrals.J₄', SmoothJ24Common.coeff,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g, mul_assoc, mul_left_comm, mul_comm]

/-- Schwartz-type decay bounds for `J₄'` and its iterated derivatives on `0 ≤ x`.

The prime in `decay_J₄'` refers to the function `J₄'`. -/
public theorem decay_J₄' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₄' x‖ ≤ C := by
  refine
    (SmoothJ24Common.decay_of_eq_I0_of_coeff_re_mul (z := z₄') (c := (-1 : ℂ)) (f := J₄')
      (hfEq := ?_) continuous_z₄'
      (fun t => by simpa using (MagicFunction.Parametrisations.im_z₄'_pos_all t))
      (fun t => norm_z₄'_le_two t) (fun t => im_z₄'_eq_one t))
  intro x
  simp [SpherePacking.Integration.SmoothIntegralCommon.I, RealIntegrals.J₄', SmoothJ24Common.coeff,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g, mul_assoc, mul_left_comm, mul_comm]

end

end MagicFunction.b.Schwartz.J4Smooth
