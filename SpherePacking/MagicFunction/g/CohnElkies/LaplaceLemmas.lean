module
public import Mathlib.MeasureTheory.Integral.Gamma


/-!
# Laplace-type integrals

This file evaluates basic Laplace integrals over `Set.Ioi (0 : ℝ)` that occur in the
"another integral" representations for `a'` and `b'`.

## Main statements
* `MagicFunction.g.CohnElkies.integral_exp_neg_pi_mul_Ioi`
* `MagicFunction.g.CohnElkies.integral_mul_exp_neg_pi_mul_Ioi`
* `MagicFunction.g.CohnElkies.integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi`
-/

namespace MagicFunction.g.CohnElkies

open scoped BigOperators
open MeasureTheory Real

private lemma gamma_two : Real.Gamma (2 : ℝ) = 1 := by simp

lemma integral_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (-a * t)) = 1 / a := by
  simpa [Real.rpow_one, one_add_one_eq_two, gamma_two, Real.rpow_neg_one, one_div] using
    (integral_exp_neg_mul_rpow (p := (1 : ℝ)) (b := a) (hp := by norm_num) (hb := ha))

lemma integral_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    (∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-a * t)) = 1 / a ^ (2 : ℕ) := by
  simpa [Real.rpow_one, one_add_one_eq_two, gamma_two, Real.rpow_neg ha.le, one_div, div_one]
    using (integral_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (q := (1 : ℝ)) (b := a)
      (hp := by norm_num) (hq := by norm_num) (hb := ha))

/-- Evaluate `∫ exp(-π * u * t)` over `t ∈ (0, ∞)` (for `0 < u`). -/
public lemma integral_exp_neg_pi_mul_Ioi {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (-π * u * t)) = 1 / (π * u) := by
  simpa [mul_assoc] using (integral_exp_neg_mul_Ioi (a := π * u) (by positivity [Real.pi_pos, hu]))

/-- Evaluate `∫ t * exp(-π * u * t)` over `t ∈ (0, ∞)` (for `0 < u`). -/
public lemma integral_mul_exp_neg_pi_mul_Ioi {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-π * u * t)) = 1 / (π * u) ^ (2 : ℕ) := by
  simpa [mul_assoc] using
    (integral_mul_exp_neg_mul_Ioi (a := π * u) (by positivity [Real.pi_pos, hu]))

/-- Algebraic identity: `exp(2πt) · exp(-πut) = exp(-(π(u-2))t)`. -/
public lemma exp_two_pi_mul_mul_exp_neg_pi_mul (u t : ℝ) :
    Real.exp (2 * π * t) * Real.exp (-π * u * t) = Real.exp (-(π * (u - 2)) * t) := by
  rw [← Real.exp_add]; congr 1; ring

/-- Evaluate `∫ exp(2π t) * exp(-π u t)` over `t ∈ (0, ∞)` (for `2 < u`). -/
public lemma integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi {u : ℝ} (hu : 2 < u) :
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (2 * π * t) * Real.exp (-π * u * t)) =
      1 / (π * (u - 2)) := by
  have hpu : 0 < π * (u - 2) := by positivity [Real.pi_pos, sub_pos.2 hu]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (g := fun t => Real.exp (-(π * (u - 2)) * t))
    (fun t _ => by simpa using exp_two_pi_mul_mul_exp_neg_pi_mul u t)]
  simpa [mul_assoc] using (integral_exp_neg_mul_Ioi (a := π * (u - 2)) hpu)

end MagicFunction.g.CohnElkies
