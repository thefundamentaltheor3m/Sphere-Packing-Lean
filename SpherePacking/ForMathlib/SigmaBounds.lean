module
public import Mathlib.NumberTheory.ArithmeticFunction.Misc


/-!
# Divisor sum bounds

This file provides elementary bounds on divisor sums `σ k n` used in `q`-expansion estimates.
-/

namespace SpherePacking.ForMathlib

open scoped ArithmeticFunction.sigma

private lemma sigma_le_pow_succ (k n : ℕ) : σ k n ≤ n ^ (k + 1) := by
  by_cases hn : n = 0
  · simp [hn]
  calc
    σ k n ≤ (Nat.divisors n).card * n ^ k := by
      simpa [ArithmeticFunction.sigma_apply, nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul (Nat.divisors n) (fun d => d ^ k) (n ^ k) fun d hd =>
          Nat.pow_le_pow_left (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.mem_divisors.mp hd).1) k)
    _ ≤ n * n ^ k := by
      exact Nat.mul_le_mul_right _ (Nat.card_divisors_le_self n)
    _ = n ^ (k + 1) := by simp [pow_succ, Nat.mul_comm]

/-- A crude bound `σ 3 n ≤ n ^ 4`. -/
public lemma sigma_three_le_pow_four (n : ℕ) : σ 3 n ≤ n ^ 4 := by
  simpa using (sigma_le_pow_succ 3 n)

end SpherePacking.ForMathlib
