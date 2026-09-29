/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Bounds on the complex exponential
-/

@[expose] public section

namespace Real

theorem exp_neg_mul_decay (k : ℕ) {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k * exp (-r * x) ≤ (k / r * exp (-1)) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, one_mul, Nat.cast_zero]
    exact exp_le_one_iff.2 (by nlinarith)
  calc
    _ = ((r * x / k) * rexp (- (r * x / k)) * (k / r)) ^ k := by
      rw [mul_right_comm, mul_pow, ← Real.exp_nat_mul]
      field_simp
    _ ≤ (k / r * exp (-1)) ^ k := by
      grw [Real.mul_exp_neg_le_exp_neg_one]
      grind

theorem exp_decay (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : x ^ k * rexp (-k * x) ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, one_mul, Nat.cast_zero]
    exact exp_le_one_iff.2 (by nlinarith)
  grw [exp_neg_mul_decay _ (by positivity) hx, div_self (by positivity),
    exp_le_one_iff.2 (by simp), one_mul, one_pow]

end Real
