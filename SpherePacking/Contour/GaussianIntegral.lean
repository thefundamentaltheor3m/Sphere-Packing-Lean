module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Exp

import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.ForMathlib.GaussianRexpIntegral

/-!
Shared Gaussian integral wrappers used across the contour/Fourier developments.

This module consolidates two small "inner integral evaluation" lemmas that were previously split
across several tiny files.
-/

open scoped FourierTransform RealInnerProductSpace

namespace SpherePacking.Contour

noncomputable section

/--
Evaluate a Fourier-type Gaussian integral in even real dimension.

This is a thin wrapper around `SpherePacking.ForMathlib.integral_phase_gaussian_pi_mul_I_mul_even`,
pulling out the constant factor `c`.
-/
public lemma integral_const_mul_phase_gaussian_pi_mul_I_mul_even (k : ℕ)
    (w : EuclideanSpace ℝ (Fin (2 * k))) (z : ℂ) (hz : 0 < z.im) (c : ℂ) :
    (∫ x : EuclideanSpace ℝ (Fin (2 * k)),
        c *
          (Complex.exp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I) *
            Complex.exp ((Real.pi : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z))) =
      c * ((((Complex.I : ℂ) / z) ^ k) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * (‖w‖ ^ 2 : ℝ) * (-1 / z))) := by
  simpa [MeasureTheory.integral_const_mul] using congrArg (fun I : ℂ => c * I)
    (ForMathlib.integral_phase_gaussian_pi_mul_I_mul_even (k := k) (w := w) (z := z) hz)

/--
Evaluate the real Gaussian integral `∫ exp (-pi * t * ‖x‖^2)` in even dimension.

The result is the expected scaling law `(1 / t) ^ k`.
-/
public lemma integral_rexp_neg_pi_mul_sq_norm_even (k : ℕ) (t : ℝ) (ht : 0 < t) :
    (∫ x : EuclideanSpace ℝ (Fin (2 * k)),
        Real.exp (-Real.pi * t * (‖x‖ ^ 2))) = (1 / t) ^ k := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (ForMathlib.integral_gaussian_rexp_even (k := k) (s := (1 / t)) (one_div_pos.2 ht))

end

end SpherePacking.Contour
