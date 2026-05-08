module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Integrability of `t ^ n * exp (-b * t)` on `Ioi 0` and `Ici 1`.
-/

namespace SpherePacking.ForMathlib

open MeasureTheory Set

/-- `t ↦ t ^ n * exp (-b * t)` is integrable on `[1, ∞)` when `0 < b`. -/
public lemma integrableOn_pow_mul_exp_neg_mul_Ici (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ ↦ t ^ n * Real.exp (-b * t)) (Set.Ici (1 : ℝ)) volume :=
  (show IntegrableOn (fun t : ℝ ↦ t ^ n * Real.exp (-b * t)) (Set.Ioi (0 : ℝ)) volume by
    simpa [Real.rpow_one, Real.rpow_natCast, one_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (n : ℝ)) (b := b)
        (Nat.cast_nonneg n |>.trans_lt' (by norm_num)) (by simp) hb).mono_set
    fun _ ht => lt_of_lt_of_le (zero_lt_one' ℝ) ht

end SpherePacking.ForMathlib
