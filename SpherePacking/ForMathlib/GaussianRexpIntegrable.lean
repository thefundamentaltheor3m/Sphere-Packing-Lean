module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import SpherePacking.ForMathlib.GaussianRexpIntegral

/-!
# Integrability of Gaussian `rexp`

This file proves integrability of the real Gaussian `x ↦ exp (-π * ‖x‖^2 / s)` on `ℝ^(2k)` for
`s > 0`, and records the specialization to `ℝ⁸` used in the dimension-8 development.
-/

namespace SpherePacking.ForMathlib

open Real MeasureTheory

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

/-- The real Gaussian `x ↦ exp (-π * ‖x‖^2 / s)` is integrable on `ℝ^(2k)` for `s > 0`. -/
public lemma integrable_gaussian_rexp_even (k : ℕ) (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : EuclideanSpace ℝ (Fin (2 * k)) ↦ rexp (-π * (‖x‖ ^ 2) / s))
      (volume : Measure (EuclideanSpace ℝ (Fin (2 * k)))) := by
  refine MeasureTheory.Integrable.of_integral_ne_zero (μ := volume) ?_
  rw [integral_gaussian_rexp_even (k := k) (s := s) hs]
  exact pow_ne_zero k hs.ne'

/-- The real Gaussian `x ↦ exp (-π * ‖x‖^2 / s)` is integrable on `ℝ⁸` for `s > 0`. -/
public lemma integrable_gaussian_rexp (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : ℝ⁸ ↦ rexp (-π * (‖x‖ ^ 2) / s)) (volume : Measure ℝ⁸) := by
  simpa using integrable_gaussian_rexp_even (k := 4) s hs

end SpherePacking.ForMathlib
