module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Imaginary-axis exponential weights

This file records elementary rewrite and norm lemmas for the standard exponential weights that
appear when restricting holomorphic functions to the imaginary axis.
-/

namespace SpherePacking.ForMathlib

open Complex
open scoped Complex

/-- Rewrite `exp (π i * u * (t i))` as a real exponential: `exp (-π * u * t)`. -/
public lemma exp_pi_I_mul_mul_I_eq_real_exp (u t : ℝ) :
    Complex.exp (Real.pi * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) =
      (Real.exp (-Real.pi * u * t) : ℂ) := by
  have harg :
      (Real.pi : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I) = (-Real.pi * u * t : ℂ) := by
    ring_nf
    simp [Complex.I_sq]
  simp [harg]

/--
The norm of `exp (2π i z)` is `exp (-2π * Im z)`.

Proof: `‖exp w‖ = exp (Re w)` and `Re (2π i z) = -2π * Im z`.
-/
public lemma norm_cexp_two_pi_I_mul (z : ℂ) :
    ‖cexp (2 * Real.pi * Complex.I * z)‖ = Real.exp (-2 * Real.pi * z.im) := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im, mul_left_comm, mul_comm]

/-- If `δ ≤ Im z` then `‖exp (2π i z)‖ ≤ exp (-2π * δ)`. -/
public lemma norm_cexp_two_pi_I_mul_le_of_le_im {δ : ℝ} {z : ℂ} (hδ : δ ≤ z.im) :
    ‖cexp (2 * Real.pi * Complex.I * z)‖ ≤ Real.exp (-2 * Real.pi * δ) := by
  simpa [norm_cexp_two_pi_I_mul] using Real.exp_le_exp.2 (by nlinarith [hδ, Real.pi_pos])

/-- If `δ ≤ Im z` then `‖exp (2π i * n * z)‖ ≤ (exp (-2π * δ)) ^ n` for all `n : ℕ`. -/
public lemma norm_cexp_two_pi_I_mul_nat_mul_le_pow_of_le_im (n : ℕ) {δ : ℝ} {z : ℂ}
    (hδ : δ ≤ z.im) :
    ‖cexp (2 * Real.pi * Complex.I * (n : ℂ) * z)‖ ≤ (Real.exp (-2 * Real.pi * δ)) ^ n := by
  have hmul :
      2 * Real.pi * Complex.I * (n : ℂ) * z = (n : ℂ) * (2 * Real.pi * Complex.I * z) := by
    ac_rfl
  simpa [hmul, norm_pow, Complex.exp_nat_mul (2 * Real.pi * Complex.I * z) n] using
    pow_le_pow_left₀ (norm_nonneg _)
      (norm_cexp_two_pi_I_mul_le_of_le_im (δ := δ) (z := z) hδ) n

end SpherePacking.ForMathlib
