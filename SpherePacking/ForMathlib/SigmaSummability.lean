module

public import SpherePacking.ForMathlib.SigmaBounds
public import SpherePacking.ForMathlib.SpecificLimits
public import Mathlib.Data.Complex.Basic

/-!
# Summability bounds for divisor sums

This file provides small wrappers turning polynomial bounds on divisor sums `σ k` into
summability statements for `q`-series coefficients of the form `‖σ k (n+s)‖ * exp(-2π n)` and
`‖(n+s) * σ k (n+s)‖ * exp(-2π n)`.
-/

namespace SpherePacking.ForMathlib

open scoped ArithmeticFunction.sigma

/-- Summability of `‖(n+s) * σ k (n+s)‖ * exp (-2π n)` from a polynomial bound on `σ k (n+s)`. -/
public lemma summable_norm_mul_sigma_shift_mul_exp {k m s : ℕ}
    (hsigma : ∀ n : ℕ, (σ k (n + s) : ℝ) ≤ (n + s : ℝ) ^ m) :
    Summable (fun n : ℕ =>
      ‖(((n + s : ℕ) : ℂ) * (σ k (n + s) : ℂ))‖ * Real.exp (-2 * Real.pi * n)) := by
  have hle :
      ∀ n : ℕ,
        ‖(((n + s : ℕ) : ℂ) * (σ k (n + s) : ℂ))‖ * Real.exp (-2 * Real.pi * n) ≤
          ((n + s : ℝ) ^ (m + 1)) * Real.exp (-2 * Real.pi * n) := by
    intro n
    set N : ℕ := n + s
    have hmul : (N : ℝ) * (σ k N : ℝ) ≤ (N : ℝ) * ((N : ℝ) ^ m) := by
      exact mul_le_mul_of_nonneg_left (by simpa [N] using hsigma n)
        (by positivity : (0 : ℝ) ≤ (N : ℝ))
    calc
      ‖(((n + s : ℕ) : ℂ) * (σ k (n + s) : ℂ))‖ * Real.exp (-2 * Real.pi * n) =
          ((N : ℝ) * (σ k N : ℝ)) * Real.exp (-2 * Real.pi * n) := by
            simp [N, -Nat.cast_add, mul_left_comm, mul_comm]
      _ ≤ ((N : ℝ) * ((N : ℝ) ^ m)) * Real.exp (-2 * Real.pi * n) := by
            exact mul_le_mul_of_nonneg_right hmul (by positivity)
      _ = ((N : ℝ) ^ (m + 1)) * Real.exp (-2 * Real.pi * n) := by
            simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
      _ = ((n + s : ℝ) ^ (m + 1)) * Real.exp (-2 * Real.pi * n) := by
            simp [N]
  have hs :
      Summable (fun n : ℕ => ((n + s : ℝ) ^ (m + 1)) * Real.exp (-2 * Real.pi * n)) := by
    simpa using (summable_pow_shift_mul_exp (m + 1) s)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => hle n) hs

end SpherePacking.ForMathlib
