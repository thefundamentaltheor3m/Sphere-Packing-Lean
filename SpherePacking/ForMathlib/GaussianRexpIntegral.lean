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
  have hb : 0 < (π / s) := div_pos Real.pi_pos hs
  have hcong : (∫ x : EuclideanSpace ℝ (Fin (2 * k)), rexp (-π * (‖x‖ ^ 2) / s)) =
      ∫ x : EuclideanSpace ℝ (Fin (2 * k)), rexp (-(π / s) * ‖x‖ ^ 2) :=
    integral_congr_ae (ae_of_all _ fun x => by ring_nf)
  rw [hcong, GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
  simp [show (π / (π / s)) = s from by field_simp]

/-- Gaussian `rexp` integral over `ℝ⁸` with a scale parameter. -/
public lemma integral_gaussian_rexp (s : ℝ) (hs : 0 < s) :
    (∫ x : ℝ⁸, rexp (-π * (‖x‖ ^ 2) / s)) = s ^ 4 := by
  simpa using integral_gaussian_rexp_even (k := 4) s hs

end SpherePacking.ForMathlib
