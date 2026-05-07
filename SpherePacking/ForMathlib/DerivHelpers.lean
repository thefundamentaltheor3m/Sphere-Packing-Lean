module
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Derivative helpers

Small `HasDerivAt` and norm/inequality lemmas duplicated across the project.
-/

namespace SpherePacking.ForMathlib

open scoped Complex

/-- Derivative of `y ↦ exp((y : ℂ) * c)` is `exp((x : ℂ) * c) * c`. -/
public lemma hasDerivAt_cexp_ofReal_mul_const (c : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ cexp ((y : ℂ) * c)) (cexp ((x : ℂ) * c) * c) x := by
  simpa using ((hasDerivAt_mul_const (x := (x : ℂ)) c).comp_ofReal).cexp

/-- Derivative of `y ↦ a * exp((y : ℂ) * c)`. -/
public lemma hasDerivAt_mul_cexp_ofReal_mul_const (a c : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ a * cexp ((y : ℂ) * c))
      (c * (a * cexp ((x : ℂ) * c))) x := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using (hasDerivAt_cexp_ofReal_mul_const c x).const_mul a

/-- Derivative of `y ↦ (c ^ n) * (a * exp((y : ℂ) * c))`. -/
public lemma hasDerivAt_pow_mul_mul_cexp_ofReal_mul_const (a c : ℂ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (c ^ n) * (a * cexp ((y : ℂ) * c)))
      ((c ^ (n + 1)) * (a * cexp ((x : ℂ) * c))) x := by
  simpa [pow_succ, mul_assoc] using
    (hasDerivAt_mul_cexp_ofReal_mul_const a c x).const_mul (c ^ n)

/-- If `x ∈ ball x₀ ε`, then `|x| ≤ |x₀| + ε`. -/
public lemma abs_le_abs_add_of_mem_ball {x x₀ ε : ℝ} (hx : x ∈ Metric.ball x₀ ε) :
    |x| ≤ |x₀| + ε := by
  have : |x - x₀| < ε := by simpa [Metric.mem_ball, Real.dist_eq] using hx
  linarith [abs_sub_abs_le_abs_sub x x₀]

/-- If `‖z‖ ≤ 2`, then `‖(π * I) * z‖ ≤ 2 * π`. -/
public lemma norm_mul_pi_I_le_two_pi {z : ℂ} (hz : ‖z‖ ≤ 2) :
    ‖((Real.pi : ℂ) * (Complex.I : ℂ)) * z‖ ≤ 2 * Real.pi := by
  simpa [mul_assoc, abs_of_nonneg Real.pi_pos.le, mul_comm] using
    mul_le_mul_of_nonneg_left hz Real.pi_pos.le

/-- Bound `‖exp((x : ℂ) * c)‖` when `x ∈ ball x₀ 1`, `‖c‖ ≤ B`, by `exp((|x₀| + 1) * B)`. -/
public lemma norm_cexp_ofReal_mul_le_exp_mul_of_norm_le {x x₀ : ℝ} {c : ℂ} {B : ℝ}
    (hc : ‖c‖ ≤ B) (hx : x ∈ Metric.ball x₀ (1 : ℝ)) :
    ‖cexp ((x : ℂ) * c)‖ ≤ Real.exp ((|x₀| + 1) * B) := by
  have hre : ((x : ℂ) * c).re ≤ (|x₀| + 1) * B := (Complex.re_le_norm _).trans <| by
    have : |x| * ‖c‖ ≤ (|x₀| + 1) * B := by gcongr; exact abs_le_abs_add_of_mem_ball hx
    simpa [norm_mul, Complex.norm_real, mul_assoc] using this
  simpa [Complex.norm_exp] using Real.exp_le_exp.2 hre

/-- If `0 ≤ a ≤ C * b` with `0 < b`, then `0 ≤ C`. -/
public lemma nonneg_of_nonneg_le_mul {a b C : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (h : a ≤ C * b) :
    0 ≤ C :=
  nonneg_of_mul_nonneg_left (ha.trans h) hb

end SpherePacking.ForMathlib
