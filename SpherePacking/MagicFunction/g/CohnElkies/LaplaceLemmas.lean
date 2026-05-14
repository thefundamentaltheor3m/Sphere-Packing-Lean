module
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Laplace-type integrals and trigonometric helpers

Basic Laplace integrals over `Set.Ioi (0 : ℝ)` used in the "another integral" representations
for `a'` and `b'`, plus trigonometric helpers used to factor out `sin(π u / 2)^2` from the
vertical-segment pieces of the defining integrals of `a'` and `b'`.
-/

namespace MagicFunction.g.CohnElkies

open scoped BigOperators
open MeasureTheory Real

private lemma gamma_two : Real.Gamma (2 : ℝ) = 1 := by simp

lemma integral_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (-a * t)) = 1 / a := by
  simpa [Real.rpow_one, one_add_one_eq_two, gamma_two, Real.rpow_neg_one, one_div] using
    (integral_exp_neg_mul_rpow (p := (1 : ℝ)) (b := a) (hp := by norm_num) (hb := ha))

/-- Evaluate `∫ exp(-π * u * t)` over `t ∈ (0, ∞)` (for `0 < u`). -/
public lemma integral_exp_neg_pi_mul_Ioi {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (-π * u * t)) = 1 / (π * u) := by
  simpa [mul_assoc] using (integral_exp_neg_mul_Ioi (a := π * u) (by positivity [Real.pi_pos, hu]))

/-- Evaluate `∫ t * exp(-π * u * t)` over `t ∈ (0, ∞)` (for `0 < u`). -/
public lemma integral_mul_exp_neg_pi_mul_Ioi {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-π * u * t)) = 1 / (π * u) ^ (2 : ℕ) := by
  have ha : 0 < π * u := by positivity [Real.pi_pos, hu]
  simpa [mul_assoc, Real.rpow_one, one_add_one_eq_two, gamma_two, Real.rpow_neg ha.le, div_one]
    using (integral_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (q := (1 : ℝ)) (b := π * u)
      (hp := by norm_num) (hq := by norm_num) (hb := ha))

/-- Algebraic identity: `exp(2πt) · exp(-πut) = exp(-(π(u-2))t)`. -/
public lemma exp_two_pi_mul_mul_exp_neg_pi_mul (u t : ℝ) :
    Real.exp (2 * π * t) * Real.exp (-π * u * t) = Real.exp (-(π * (u - 2)) * t) := by
  rw [← Real.exp_add]; congr 1; ring

/-- Evaluate `∫ exp(2π t) * exp(-π u t)` over `t ∈ (0, ∞)` (for `2 < u`). -/
public lemma integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi {u : ℝ} (hu : 2 < u) :
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (2 * π * t) * Real.exp (-π * u * t)) =
      1 / (π * (u - 2)) := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (g := fun t => Real.exp (-(π * (u - 2)) * t))
    (fun t _ => by simpa using exp_two_pi_mul_mul_exp_neg_pi_mul u t)]
  simpa [mul_assoc] using
    (integral_exp_neg_mul_Ioi (a := π * (u - 2)) (by positivity [Real.pi_pos, sub_pos.2 hu]))

namespace Trig

/-- Rewrite `2 - exp(π u i) - exp(-π u i)` as `2 - 2 cos(π u)`. -/
public lemma two_sub_exp_pi_mul_I_sub_exp_neg_pi_mul_I (u : ℝ) :
    (2 : ℂ) - Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) -
        Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) =
      ((2 - 2 * Real.cos (π * u) : ℝ) : ℂ) := by
  set z : ℂ := ((π * u : ℝ) : ℂ)
  have hcos : Complex.exp (z * Complex.I) + Complex.exp (-(z * Complex.I)) =
      (2 : ℂ) * Complex.cos z := by
    simpa [neg_mul] using (Complex.two_cos (x := z)).symm
  calc
    (2 : ℂ) - Complex.exp (z * Complex.I) - Complex.exp (-(z * Complex.I)) =
        (2 : ℂ) - (Complex.exp (z * Complex.I) + Complex.exp (-(z * Complex.I))) := by
          simpa using sub_sub (2 : ℂ) (Complex.exp (z * Complex.I)) (Complex.exp (-(z * Complex.I)))
    _ = (2 : ℂ) - (2 : ℂ) * Complex.cos z := by simp [hcos]
    _ = ((2 - 2 * Real.cos (π * u) : ℝ) : ℂ) := by simp [z, sub_eq_add_neg]

/-- Rewrite `2 - 2 cos(π u)` as `4 sin(π u / 2)^2`. -/
public lemma two_sub_two_cos_eq_four_sin_sq (u : ℝ) :
    (2 - 2 * Real.cos (π * u) : ℝ) = 4 * (Real.sin (π * u / 2)) ^ (2 : ℕ) := by
  have hsin : (Real.sin (π * u / 2)) ^ (2 : ℕ) = 1 / 2 - Real.cos (π * u) / 2 := by
    have : (2 : ℝ) * (π * u / 2) = π * u := by ring
    simpa [pow_two, this] using (Real.sin_sq_eq_half_sub (x := π * u / 2))
  calc
    (2 - 2 * Real.cos (π * u) : ℝ) = 4 * (1 / 2 - Real.cos (π * u) / 2) := by ring
    _ = 4 * (Real.sin (π * u / 2)) ^ (2 : ℕ) := by simp [hsin]

end Trig

end MagicFunction.g.CohnElkies
