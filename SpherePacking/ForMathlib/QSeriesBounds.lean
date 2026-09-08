/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Pointwise bounds for q-series

Absolute summability at a reference height `c` gives uniform bounds above that height.
For shifted coefficients, the decay factor is `exp (-2π n₀ im z)`. For unshifted
coefficients vanishing below `n₀`, it is `exp (-2π n₀ (im z - c))`: keeping the
reference-height correction is essential when using the unshifted coefficient norm sum.
-/

@[expose] public section

open Real

namespace Complex

/-- Bound a shifted q-series above its reference height of absolute summability. -/
lemma norm_qseries_shift_le {a : ℕ → ℂ} (n₀ : ℕ) {c : ℝ}
    (ha : Summable fun m : ℕ ↦ ‖a m‖ * Real.exp (-(2 * π * c) * m))
    (z : ℂ) (hz : c ≤ z.im) :
    ‖∑' m : ℕ, a m * exp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * z)‖ ≤
      (∑' m : ℕ, ‖a m‖ * Real.exp (-(2 * π * c) * m)) *
        Real.exp (-(2 * π) * n₀ * z.im) := by
  have key (m : ℕ) : ‖a m * exp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * z)‖ ≤
      ‖a m‖ * Real.exp (-(2 * π * c) * m) * Real.exp (-(2 * π) * n₀ * z.im) := by
    rw [norm_mul, norm_exp, mul_assoc ‖a m‖]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [← Real.exp_add, Real.exp_le_exp]
    simp only [show (2 * π * I * ((m + n₀ : ℕ) : ℂ) * z).re =
      -(2 * π) * (m + n₀) * z.im by simp [mul_re, mul_im]]
    nlinarith [mul_le_mul_of_nonneg_left hz
      (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * π) m.cast_nonneg)]
  have hs := Summable.of_nonneg_of_le (fun m ↦ norm_nonneg _) key (ha.mul_right _)
  exact (norm_tsum_le_tsum_norm hs).trans
    ((Summable.tsum_le_tsum key hs (ha.mul_right _)).trans_eq tsum_mul_right)

/-- Bound a q-series whose coefficients vanish below `n₀`, retaining the reference-height
correction in the decay factor. Unlike a shifted series, the coefficient norm sum is unshifted. -/
lemma norm_qseries_le_of_coeff_vanish {b : ℕ → ℂ} (n₀ : ℕ) {c : ℝ}
    (hb : ∀ m < n₀, b m = 0)
    (hs : Summable fun m : ℕ ↦ ‖b m‖ * Real.exp (-(2 * π * c) * m))
    (z : ℂ) (hz : c ≤ z.im) :
    ‖∑' m : ℕ, b m * exp (2 * π * I * m * z)‖ ≤
      (∑' m : ℕ, ‖b m‖ * Real.exp (-(2 * π * c) * m)) *
        Real.exp (-(2 * π) * n₀ * (z.im - c)) := by
  have key (m : ℕ) : ‖b m * exp (2 * π * I * m * z)‖ ≤
      ‖b m‖ * Real.exp (-(2 * π * c) * m) * Real.exp (-(2 * π) * n₀ * (z.im - c)) := by
    by_cases hm : m < n₀
    · simp [hb m hm]
    rw [norm_mul, norm_exp, mul_assoc ‖b m‖]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [← Real.exp_add, Real.exp_le_exp]
    simp only [show (2 * π * I * (m : ℂ) * z).re = -(2 * π) * m * z.im by
      simp [mul_re, mul_im]]
    have hm' : (n₀ : ℝ) ≤ m := by exact_mod_cast Nat.le_of_not_gt hm
    nlinarith [mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hm' (sub_nonneg.mpr hz))
      (by positivity : (0 : ℝ) ≤ 2 * π)]
  have hsum := Summable.of_nonneg_of_le (fun m ↦ norm_nonneg _) key (hs.mul_right _)
  exact (norm_tsum_le_tsum_norm hsum).trans
    ((Summable.tsum_le_tsum key hsum (hs.mul_right _)).trans_eq tsum_mul_right)

end Complex
