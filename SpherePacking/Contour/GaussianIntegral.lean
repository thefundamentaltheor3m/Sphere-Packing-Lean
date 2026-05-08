module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import SpherePacking.ForMathlib.GaussianFourierCommon

/-! Shared Gaussian integral wrappers used across the contour/Fourier developments. -/

open scoped FourierTransform RealInnerProductSpace

namespace SpherePacking.Contour

noncomputable section

/-- Evaluate a Fourier-type Gaussian integral in even real dimension, pulling out a constant `c`. -/
public lemma integral_const_mul_phase_gaussian_pi_mul_I_mul_even (k : ℕ)
    (w : EuclideanSpace ℝ (Fin (2 * k))) (z : ℂ) (hz : 0 < z.im) (c : ℂ) :
    (∫ x : EuclideanSpace ℝ (Fin (2 * k)), c *
        (Complex.exp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I) *
          Complex.exp ((Real.pi : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z))) =
      c * ((((Complex.I : ℂ) / z) ^ k) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * (‖w‖ ^ 2 : ℝ) * (-1 / z))) := by
  simpa [MeasureTheory.integral_const_mul] using congrArg (fun I : ℂ => c * I)
    (ForMathlib.integral_phase_gaussian_pi_mul_I_mul_even (k := k) (w := w) (z := z) hz)

end

end SpherePacking.Contour
