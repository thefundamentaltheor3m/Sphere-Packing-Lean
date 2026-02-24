module
public import Mathlib.NumberTheory.ArithmeticFunction.Misc


/-!
# Divisor sum bounds

This file provides elementary bounds on divisor sums `σ k n` used in `q`-expansion estimates.
-/

namespace SpherePacking.ForMathlib

open scoped ArithmeticFunction.sigma

private lemma sigma_le_pow_succ (k n : ℕ) : σ k n ≤ n ^ (k + 1) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  calc
    σ k n = Finset.sum (Nat.divisors n) (fun d => d ^ k) := by
      simp [ArithmeticFunction.sigma_apply]
    _ ≤ Finset.sum (Nat.divisors n) (fun _d => n ^ k) := by
      refine Finset.sum_le_sum ?_
      intro d hd
      exact Nat.pow_le_pow_left
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.mem_divisors.mp hd).1) k
    _ = (Nat.divisors n).card * (n ^ k) := by simp
    _ ≤ n * (n ^ k) := by
      gcongr
      simpa using Nat.card_divisors_le_self n
    _ = n ^ (k + 1) := by
      simp [pow_succ, Nat.mul_comm]

/-- A crude bound `σ 3 n ≤ n ^ 4`. -/
public lemma sigma_three_le_pow_four (n : ℕ) : σ 3 n ≤ n ^ 4 := by
  simpa using (sigma_le_pow_succ 3 n)

end SpherePacking.ForMathlib
