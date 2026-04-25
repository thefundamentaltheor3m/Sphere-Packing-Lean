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
open MagicFunction.Parametrisations MagicFunction.b.RealIntegrals
  MagicFunction.b.PsiBounds SpherePacking.ForMathlib

private lemma hfEq_J₂' (x : ℝ) :
    J₂' x = SpherePacking.Integration.SmoothIntegralCommon.I
      (coeff := SmoothJ24Common.coeff z₂')
      (hf := fun t : ℝ ↦ (1 : ℂ) * ψT' (z₂' t)) 0 x := by
  simp [SpherePacking.Integration.SmoothIntegralCommon.I, RealIntegrals.J₂', SmoothJ24Common.coeff,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g, mul_assoc, mul_left_comm, mul_comm]

/-- Smoothness of `J₂'` (the primed radial profile used to define the Schwartz kernel `J₂`).

The prime in `contDiff_J₂'` refers to the function `J₂'`. -/
public theorem contDiff_J₂' : ContDiff ℝ (⊤ : ℕ∞) J₂' :=
  SmoothJ24Common.contDiff_of_eq_I0_mul (z := z₂') (c := (1 : ℂ)) hfEq_J₂'
    continuous_z₂' (fun t => by simpa using im_z₂'_pos_all t) norm_z₂'_le_two

/-- Schwartz-type decay bounds for `J₂'` and its iterated derivatives on `0 ≤ x`.

The prime in `decay_J₂'` refers to the function `J₂'`. -/
public theorem decay_J₂' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₂' x‖ ≤ C :=
  SmoothJ24Common.decay_of_eq_I0_of_coeff_re_mul (z := z₂') (c := (1 : ℂ)) hfEq_J₂'
    continuous_z₂' (fun t => by simpa using im_z₂'_pos_all t) norm_z₂'_le_two im_z₂'_eq_one

end

end MagicFunction.b.Schwartz.J2Smooth
