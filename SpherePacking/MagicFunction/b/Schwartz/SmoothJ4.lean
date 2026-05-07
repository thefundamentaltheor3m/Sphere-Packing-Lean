module
public import SpherePacking.MagicFunction.b.Basic
public import SpherePacking.MagicFunction.b.PsiBounds

import SpherePacking.MagicFunction.b.Schwartz.SmoothJ24Common
import SpherePacking.MagicFunction.IntegralParametrisationsContinuity

/-!
# Smooth J4

Smoothness/decay bounds for `RealIntegrals.J₄'` by differentiating under the integral sign.
-/

namespace MagicFunction.b.Schwartz.J4Smooth

noncomputable section

open scoped Interval Manifold Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter intervalIntegral MagicFunction.Parametrisations
  MagicFunction.b.RealIntegrals MagicFunction.b.PsiBounds SpherePacking.ForMathlib

private lemma hfEq_J₄' (x : ℝ) :
    J₄' x = SpherePacking.Integration.SmoothIntegralCommon.I
      (coeff := SmoothJ24Common.coeff z₄')
      (hf := fun t : ℝ ↦ (-1 : ℂ) * ψT' (z₄' t)) 0 x := by
  simp [SpherePacking.Integration.SmoothIntegralCommon.I, RealIntegrals.J₄', SmoothJ24Common.coeff,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g, mul_assoc, mul_left_comm, mul_comm]

/-- Smoothness of `J₄'` (the primed radial profile). -/
public theorem contDiff_J₄' : ContDiff ℝ (⊤ : ℕ∞) J₄' :=
  SmoothJ24Common.contDiff_of_eq_I0_mul (z := z₄') (c := (-1 : ℂ)) hfEq_J₄'
    continuous_z₄' (fun t => by simpa using im_z₄'_pos_all t) norm_z₄'_le_two

/-- Schwartz-type decay bounds for `J₄'` and its iterated derivatives on `0 ≤ x`. -/
public theorem decay_J₄' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₄' x‖ ≤ C :=
  SmoothJ24Common.decay_of_eq_I0_of_coeff_re_mul (z := z₄') (c := (-1 : ℂ)) hfEq_J₄'
    continuous_z₄' (fun t => by simpa using im_z₄'_pos_all t) norm_z₄'_le_two im_z₄'_eq_one

end

end MagicFunction.b.Schwartz.J4Smooth
