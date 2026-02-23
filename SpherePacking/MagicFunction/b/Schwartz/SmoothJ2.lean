module
public import SpherePacking.MagicFunction.b.Basic
public import SpherePacking.MagicFunction.b.PsiBounds

import SpherePacking.MagicFunction.b.Schwartz.SmoothJ24Common
import SpherePacking.MagicFunction.IntegralParametrisationsContinuity

/-!
# Smooth J2

This file proves smoothness/decay bounds for `RealIntegrals.J₂'` by differentiating under the
integral sign.
-/

namespace MagicFunction.b.Schwartz.J2Smooth

noncomputable section

open scoped Interval Manifold Topology UpperHalfPlane

open Complex Real Set MeasureTheory Filter intervalIntegral

open MagicFunction.Parametrisations
open MagicFunction.b.RealIntegrals
open MagicFunction.b.PsiBounds
open SpherePacking.ForMathlib

/-- Smoothness of `J₂'` (the primed radial profile used to define the Schwartz kernel `J₂`).

The prime in `contDiff_J₂'` refers to the function `J₂'`. -/
public theorem contDiff_J₂' : ContDiff ℝ (⊤ : ℕ∞) J₂' := by
  refine
    (SmoothJ24Common.contDiff_of_eq_I0_mul (z := z₂') (c := (1 : ℂ)) (f := J₂')
      (hfEq := ?_) continuous_z₂'
      (fun t => by simpa using (MagicFunction.Parametrisations.im_z₂'_pos_all t))
      (fun t => norm_z₂'_le_two t))
  intro x
  simp [SpherePacking.Integration.SmoothIntegralCommon.I, RealIntegrals.J₂', SmoothJ24Common.coeff,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g, mul_assoc, mul_left_comm, mul_comm]

/-- Schwartz-type decay bounds for `J₂'` and its iterated derivatives on `0 ≤ x`.

The prime in `decay_J₂'` refers to the function `J₂'`. -/
public theorem decay_J₂' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₂' x‖ ≤ C := by
  refine
    (SmoothJ24Common.decay_of_eq_I0_of_coeff_re_mul (z := z₂') (c := (1 : ℂ)) (f := J₂')
      (hfEq := ?_) continuous_z₂'
      (fun t => by simpa using (MagicFunction.Parametrisations.im_z₂'_pos_all t))
      (fun t => norm_z₂'_le_two t) (fun t => im_z₂'_eq_one t))
  intro x
  simp [SpherePacking.Integration.SmoothIntegralCommon.I, RealIntegrals.J₂', SmoothJ24Common.coeff,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g, mul_assoc, mul_left_comm, mul_comm]

end

end MagicFunction.b.Schwartz.J2Smooth
