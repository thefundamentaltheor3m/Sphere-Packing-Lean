module

public import SpherePacking.ForMathlib.SigmaBounds
public import SpherePacking.ForMathlib.SpecificLimits
public import Mathlib.Data.Complex.Basic

/-!
# Summability bounds for divisor sums

Wrappers turning polynomial bounds on divisor sums `σ k` into summability statements for
`q`-series coefficients of the form `‖σ k (n+s)‖ * exp(-2π n)` and
`‖(n+s) * σ k (n+s)‖ * exp(-2π n)`.
-/

namespace SpherePacking.ForMathlib

open scoped ArithmeticFunction.sigma

/-- Summability of `‖(n+s) * σ k (n+s)‖ * exp (-2π n)` from a polynomial bound on `σ k (n+s)`. -/
public lemma summable_norm_mul_sigma_shift_mul_exp {k m s : ℕ}
    (hsigma : ∀ n : ℕ, (σ k (n + s) : ℝ) ≤ (n + s : ℝ) ^ m) :
    Summable (fun n : ℕ =>
      ‖(((n + s : ℕ) : ℂ) * (σ k (n + s) : ℂ))‖ * Real.exp (-2 * Real.pi * n)) := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
    (by simpa using summable_pow_shift_mul_exp (m + 1) s)
  have hnorm : ‖(((n + s : ℕ) : ℂ) * (σ k (n + s) : ℂ))‖ ≤ (n + s : ℝ) ^ (m + 1) := calc
    ‖(((n + s : ℕ) : ℂ) * (σ k (n + s) : ℂ))‖
        = (n + s : ℝ) * (σ k (n + s) : ℝ) := by
          simp only [Complex.norm_mul, Complex.norm_natCast]; simp [Nat.cast_add]
    _ ≤ (n + s : ℝ) * (n + s : ℝ) ^ m := by gcongr; exact hsigma n
    _ = (n + s : ℝ) ^ (m + 1) := by simp [pow_succ, mul_comm]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (mul_le_mul_of_nonneg_right hnorm (by positivity : (0 : ℝ) ≤ Real.exp (-2 * Real.pi * n)))

end SpherePacking.ForMathlib
