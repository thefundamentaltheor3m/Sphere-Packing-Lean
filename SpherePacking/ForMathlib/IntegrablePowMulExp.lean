module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral


/-!
# Integrability of `t ^ n * exp (-b * t)`

This file provides reusable integrability lemmas for functions of the form
`t ↦ t ^ n * exp (-b * t)` on `Ioi 0` and on `Ici 1`.
-/

namespace SpherePacking.ForMathlib

open MeasureTheory Set

/-- `t ↦ t ^ n * exp (-b * t)` is integrable on `(0, ∞)` when `0 < b`. -/
public lemma integrableOn_pow_mul_exp_neg_mul_Ioi (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ ↦ t ^ n * Real.exp (-b * t)) (Set.Ioi (0 : ℝ)) volume := by
  simpa [Real.rpow_one, Real.rpow_natCast, one_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (n : ℝ)) (b := b)
      (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)) (by simp) hb)

/-- `t ↦ t ^ n * exp (-b * t)` is integrable on `[1, ∞)` when `0 < b`. -/
public lemma integrableOn_pow_mul_exp_neg_mul_Ici (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ ↦ t ^ n * Real.exp (-b * t)) (Set.Ici (1 : ℝ)) volume := by
  refine (integrableOn_pow_mul_exp_neg_mul_Ioi (n := n) (b := b) hb).mono_set fun _ ht =>
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht

end SpherePacking.ForMathlib
