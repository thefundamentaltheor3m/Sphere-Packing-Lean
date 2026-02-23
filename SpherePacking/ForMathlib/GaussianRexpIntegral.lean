module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Gaussian `rexp` integrals

This file evaluates the integral of the real Gaussian `x ↦ exp (-π * ‖x‖^2 / s)` over `ℝ^(2k)`,
and records the specialization to `ℝ⁸` used in the dimension-8 development.
-/

namespace SpherePacking.ForMathlib

open Real MeasureTheory

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

/-- Gaussian `rexp` integral with a scale parameter in even dimension.

For `s > 0`, the integral of `x ↦ exp (-π * ‖x‖^2 / s)` over `ℝ^(2k)` equals `s ^ k`.
-/
public lemma integral_gaussian_rexp_even (k : ℕ) (s : ℝ) (hs : 0 < s) :
    (∫ x : EuclideanSpace ℝ (Fin (2 * k)), rexp (-π * (‖x‖ ^ 2) / s)) = s ^ k := by
  have hb : 0 < (π / s) := div_pos Real.pi_pos hs
  calc
    (∫ x : EuclideanSpace ℝ (Fin (2 * k)), rexp (-π * (‖x‖ ^ 2) / s)) =
        ∫ x : EuclideanSpace ℝ (Fin (2 * k)), rexp (-(π / s) * ‖x‖ ^ 2) := by
          refine integral_congr_ae (ae_of_all _ fun x => by
            have : -π * (‖x‖ ^ 2) / s = -(π / s) * ‖x‖ ^ 2 := by ring_nf
            simpa [this])
    _ = (π / (π / s)) ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * k))) / 2 : ℝ) := by
        simpa using
          (GaussianFourier.integral_rexp_neg_mul_sq_norm
            (V := EuclideanSpace ℝ (Fin (2 * k))) (b := (π / s)) hb)
    _ = s ^ k := by
        have hbase : (π / (π / s)) = s := by
          field_simp [Real.pi_ne_zero, hs.ne']
        simp [hbase]

/-- Gaussian `rexp` integral over `ℝ⁸` with a scale parameter. -/
public lemma integral_gaussian_rexp (s : ℝ) (hs : 0 < s) :
    (∫ x : ℝ⁸, rexp (-π * (‖x‖ ^ 2) / s)) = s ^ 4 := by
  simpa using integral_gaussian_rexp_even (k := 4) s hs

end SpherePacking.ForMathlib
