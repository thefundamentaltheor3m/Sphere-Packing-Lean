module
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


/-!
# Derivative helpers

This file collects small `HasDerivAt` and norm/inequality lemmas that get duplicated across the
project.
-/

namespace SpherePacking.ForMathlib

open scoped Complex

/-- Derivative of `y ↦ (y : ℂ) * c` is the constant `c`. -/
public lemma hasDerivAt_ofReal_mul_const (c : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (y : ℂ) * c) c x := by
  simpa using (hasDerivAt_mul_const (x := (x : ℂ)) c).comp_ofReal

/-- Derivative of `y ↦ exp((y : ℂ) * c)` is `exp((x : ℂ) * c) * c`. -/
public lemma hasDerivAt_cexp_ofReal_mul_const (c : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Complex.exp ((y : ℂ) * c)) (Complex.exp ((x : ℂ) * c) * c) x := by
  simpa using (hasDerivAt_ofReal_mul_const c x).cexp

/-- Derivative of `y ↦ a * exp((y : ℂ) * c)`. -/
public lemma hasDerivAt_mul_cexp_ofReal_mul_const (a c : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ a * Complex.exp ((y : ℂ) * c))
      (c * (a * Complex.exp ((x : ℂ) * c))) x := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (hasDerivAt_cexp_ofReal_mul_const c x).const_mul a

/-- Derivative of `y ↦ (c ^ n) * (a * exp((y : ℂ) * c))`. -/
public lemma hasDerivAt_pow_mul_mul_cexp_ofReal_mul_const (a c : ℂ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (c ^ n) * (a * Complex.exp ((y : ℂ) * c)))
      ((c ^ (n + 1)) * (a * Complex.exp ((x : ℂ) * c)))
      x := by simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
        (hasDerivAt_mul_cexp_ofReal_mul_const a c x).const_mul (c ^ n)

/-- If `x ∈ ball x₀ ε`, then `|x| ≤ |x₀| + ε`. -/
public lemma abs_le_abs_add_of_mem_ball {x x₀ ε : ℝ} (hx : x ∈ Metric.ball x₀ ε) :
    |x| ≤ |x₀| + ε := by
  have hdist : |x - x₀| ≤ ε := le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hx)
  calc
    |x| ≤ |x₀| + |x - x₀| := by
      simpa [add_sub_cancel] using (abs_add_le x₀ (x - x₀))
    _ ≤ |x₀| + ε := add_le_add_right hdist |x₀|

/-- If `‖z‖ ≤ 2`, then `‖(π * I) * z‖ ≤ 2 * π`. -/
public lemma norm_mul_pi_I_le_two_pi {z : ℂ} (hz : ‖z‖ ≤ 2) :
    ‖((Real.pi : ℂ) * (Complex.I : ℂ)) * z‖ ≤ 2 * Real.pi := by
  simpa [mul_assoc, abs_of_nonneg Real.pi_pos.le, mul_comm] using
    (mul_le_mul_of_nonneg_left hz Real.pi_pos.le : (Real.pi : ℝ) * ‖z‖ ≤ Real.pi * 2)

/-- If `‖z‖ ≤ B`, then `‖(-2) * z‖ ≤ 2 * B`. -/
public lemma norm_neg_two_mul_le {z : ℂ} {B : ℝ} (hz : ‖z‖ ≤ B) :
    ‖(-2 : ℂ) * z‖ ≤ 2 * B := by
  simpa [norm_mul, mul_assoc] using (mul_le_mul_of_nonneg_left hz (by positivity : (0 : ℝ) ≤ 2))

/--
Bound `‖exp((x : ℂ) * c)‖` when `x ∈ ball x₀ 1` and `‖c‖ ≤ B`, by `exp((|x₀| + 1) * B)`.
-/
public lemma norm_cexp_ofReal_mul_le_exp_mul_of_norm_le {x x₀ : ℝ} {c : ℂ} {B : ℝ}
    (hc : ‖c‖ ≤ B) (hx : x ∈ Metric.ball x₀ (1 : ℝ)) :
    ‖cexp ((x : ℂ) * c)‖ ≤ Real.exp ((|x₀| + 1) * B) := by
  have hxabs : |x| ≤ |x₀| + 1 := abs_le_abs_add_of_mem_ball hx
  have hre : ((x : ℂ) * c).re ≤ (|x₀| + 1) * B := by
    refine (Complex.re_le_norm ((x : ℂ) * c)).trans ?_
    calc
      ‖(x : ℂ) * c‖ = |x| * ‖c‖ := by simp [Complex.norm_real]
      _ ≤ (|x₀| + 1) * B := by gcongr
  simpa [Complex.norm_exp] using (Real.exp_le_exp.2 hre)

/-- If `0 ≤ a ≤ C * b` with `0 < b`, then `0 ≤ C`. -/
public lemma nonneg_of_nonneg_le_mul {a b C : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (h : a ≤ C * b) :
    0 ≤ C :=
  nonneg_of_mul_nonneg_left (ha.trans h) hb

end SpherePacking.ForMathlib
