module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Gaussian `rexp` integrals

This file evaluates `x ↦ exp (-π * ‖x‖^2 / s)` over `ℝ^(2k)`, and records the specialization to
`ℝ⁸` used in the dimension-8 development.
-/

namespace SpherePacking.ForMathlib

open Real MeasureTheory

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

/-- For `s > 0`, `∫ exp (-π ‖x‖² / s)` over `ℝ^(2k)` equals `s ^ k`. -/
public lemma integral_gaussian_rexp_even (k : ℕ) (s : ℝ) (hs : 0 < s) :
    (∫ x : EuclideanSpace ℝ (Fin (2 * k)), rexp (-π * (‖x‖ ^ 2) / s)) = s ^ k := by
  rw [integral_congr_ae (ae_of_all _ fun x => show rexp (-π * (‖x‖ ^ 2) / s) =
        rexp (-(π / s) * ‖x‖ ^ 2) by ring_nf),
    GaussianFourier.integral_rexp_neg_mul_sq_norm (div_pos Real.pi_pos hs)]
  simp [show (π / (π / s)) = s from by field_simp]

/-- Gaussian `rexp` integral over `ℝ⁸` with a scale parameter. -/
public lemma integral_gaussian_rexp (s : ℝ) (hs : 0 < s) :
    (∫ x : ℝ⁸, rexp (-π * (‖x‖ ^ 2) / s)) = s ^ 4 := by
  simpa using integral_gaussian_rexp_even (k := 4) s hs

/-- The real Gaussian `x ↦ exp (-π * ‖x‖^2 / s)` is integrable on `ℝ⁸` for `s > 0`. -/
public lemma integrable_gaussian_rexp (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : ℝ⁸ ↦ rexp (-π * (‖x‖ ^ 2) / s)) (volume : Measure ℝ⁸) := by
  simpa using
    (MeasureTheory.Integrable.of_integral_ne_zero (μ := volume) <| by
      rw [integral_gaussian_rexp_even (k := 4) (s := s) hs]; exact pow_ne_zero 4 hs.ne' :
      Integrable (fun x : EuclideanSpace ℝ (Fin (2 * 4)) ↦ rexp (-π * (‖x‖ ^ 2) / s))
        (volume : Measure (EuclideanSpace ℝ (Fin (2 * 4)))))

end SpherePacking.ForMathlib
