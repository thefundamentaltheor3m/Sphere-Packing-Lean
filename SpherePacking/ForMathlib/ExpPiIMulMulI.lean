module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Imaginary-axis exponential weights

Elementary rewrite and norm lemmas for the standard exponential weights that appear when
restricting holomorphic functions to the imaginary axis.
-/

namespace SpherePacking.ForMathlib

open Complex
open scoped Complex

/-- Rewrite `exp (π i * u * (t i))` as a real exponential: `exp (-π * u * t)`. -/
public lemma exp_pi_I_mul_mul_I_eq_real_exp (u t : ℝ) :
    Complex.exp (Real.pi * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) =
      (Real.exp (-Real.pi * u * t) : ℂ) := by
  simp [show (Real.pi : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I) = (-Real.pi * u * t : ℂ)
    from by ring_nf; simp [Complex.I_sq]]

/-- If `δ ≤ Im z` then `‖exp (2π i * n * z)‖ ≤ (exp (-2π * δ)) ^ n` for all `n : ℕ`. -/
public lemma norm_cexp_two_pi_I_mul_nat_mul_le_pow_of_le_im (n : ℕ) {δ : ℝ} {z : ℂ}
    (hδ : δ ≤ z.im) :
    ‖cexp (2 * Real.pi * Complex.I * (n : ℂ) * z)‖ ≤ (Real.exp (-2 * Real.pi * δ)) ^ n := by
  have hbase : ‖cexp (2 * Real.pi * Complex.I * z)‖ ≤ Real.exp (-2 * Real.pi * δ) := by
    rw [show ‖cexp (2 * Real.pi * Complex.I * z)‖ = Real.exp (-2 * Real.pi * z.im) by
      simp [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im, mul_left_comm, mul_comm]]
    exact Real.exp_le_exp.2 (by nlinarith [hδ, Real.pi_pos])
  simpa [show 2 * Real.pi * Complex.I * (n : ℂ) * z = (n : ℂ) * (2 * Real.pi * Complex.I * z)
    from by ac_rfl, norm_pow, Complex.exp_nat_mul (2 * Real.pi * Complex.I * z) n] using
    pow_le_pow_left₀ (norm_nonneg _) hbase n

end SpherePacking.ForMathlib
