/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

-/

module
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real


/-!
# Specific limits

This file collects auxiliary limit results not available in Mathlib.
It proves results such as `summable_real_norm_mul_geometric_of_norm_lt_one`.
-/

open Filter

/-- If `‖r‖ < 1` and `u n` grows at most polynomially, then `‖u n * r ^ n‖` is summable. -/
public theorem summable_real_norm_mul_geometric_of_norm_lt_one {k : ℕ} {r : ℂ}
    (hr : ‖r‖ < 1) {u : ℕ → ℂ} (hu : u =O[atTop] (fun n ↦ (↑(n ^ k) : ℝ))) :
    Summable fun n : ℕ ↦ ‖u n * r ^ n‖ := by
  refine summable_of_isBigO_nat (g := fun n ↦ ‖(↑(n ^ k) : ℂ) * r ^ n‖) ?_ ?_
  · simpa [Nat.cast_pow] using summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℂ) k (r := r) hr
  · simp_rw [norm_mul]
    simpa [Real.norm_eq_abs, Complex.norm_real, Nat.cast_pow] using
      (hu.norm_left.mul (Asymptotics.isBigO_refl (fun n : ℕ ↦ ‖r ^ n‖) atTop))

/-- Summability of `(n+s)^k * exp(-2π n)` on `ℕ`, used to justify `q`-series limits. -/
public theorem summable_pow_shift_mul_exp (k s : ℕ) :
    Summable (fun n : ℕ => ((n + s : ℝ) ^ k) * Real.exp (-2 * Real.pi * n)) := by
  have hs_base :
      Summable (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-2 * Real.pi * n)) := by
    simpa [Nat.cast_pow, mul_assoc] using
      Real.summable_pow_mul_exp_neg_nat_mul k (r := 2 * Real.pi) (by positivity)
  have hs_shift :
      Summable (fun n : ℕ => ((n + s : ℝ) ^ k) * Real.exp (-2 * Real.pi * (n + s))) := by
    simpa [Nat.cast_add, add_mul, mul_add, mul_assoc] using (summable_nat_add_iff s).2 hs_base
  refine (hs_shift.mul_left (Real.exp (2 * Real.pi * s))).congr ?_
  intro n
  have hexp :
      Real.exp (2 * Real.pi * s) * Real.exp (-2 * Real.pi * (n + s : ℝ)) =
        Real.exp (-2 * Real.pi * (n : ℝ)) := by
    have h : (2 * Real.pi * s) + (-2 * Real.pi * (n + s : ℝ)) = -2 * Real.pi * (n : ℝ) := by
      ring
    calc
      Real.exp (2 * Real.pi * s) * Real.exp (-2 * Real.pi * (n + s : ℝ)) =
          Real.exp ((2 * Real.pi * s) + (-2 * Real.pi * (n + s : ℝ))) := by
            simpa using (Real.exp_add (2 * Real.pi * s) (-2 * Real.pi * (n + s : ℝ))).symm
      _ = Real.exp (-2 * Real.pi * (n : ℝ)) := by
          exact congrArg Real.exp h
  calc
    Real.exp (2 * Real.pi * s) * (((n + s : ℝ) ^ k) * Real.exp (-2 * Real.pi * (n + s : ℝ))) =
        (n + s : ℝ) ^ k * (Real.exp (2 * Real.pi * s) * Real.exp (-2 * Real.pi * (n + s : ℝ))) := by
          ac_rfl
    _ = ((n + s : ℝ) ^ k) * Real.exp (-2 * Real.pi * (n : ℝ)) := by
          rw [hexp]
