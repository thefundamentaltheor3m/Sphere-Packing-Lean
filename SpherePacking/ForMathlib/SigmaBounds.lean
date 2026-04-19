module
public import Mathlib.NumberTheory.ArithmeticFunction.Misc


/-!
# Divisor sum bounds

This file provides elementary bounds on divisor sums `σ k n` used in `q`-expansion estimates.
-/

namespace SpherePacking.ForMathlib

open scoped ArithmeticFunction.sigma

/-- A crude bound `σ 3 n ≤ n ^ 4`. -/
public lemma sigma_three_le_pow_four (n : ℕ) : σ 3 n ≤ n ^ 4 := by
  by_cases hn : n = 0
  · simp [hn]
  calc
    σ 3 n ≤ (Nat.divisors n).card * n ^ 3 := by
      simpa [ArithmeticFunction.sigma_apply, nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul (Nat.divisors n) (fun d => d ^ 3) (n ^ 3) fun d hd =>
          Nat.pow_le_pow_left (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.mem_divisors.mp hd).1) 3)
    _ ≤ n * n ^ 3 := Nat.mul_le_mul_right _ (Nat.card_divisors_le_self n)
    _ = n ^ 4 := by ring

end SpherePacking.ForMathlib
