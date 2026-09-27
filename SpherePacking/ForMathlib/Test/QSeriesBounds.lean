/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

import SpherePacking.ForMathlib.QSeriesBounds
import Mathlib.Tactic.Linarith

/-!
# Regression tests for pointwise q-series bounds

Check zero starting indices, equality at the reference height (without a positivity assumption
on that height), and the reference-height correction using a single nonzero coefficient.
-/

open Complex Real

-- A zero shift contributes no exponential prefactor.
example {a : ℕ → ℂ} {c : ℝ}
    (ha : Summable fun m : ℕ ↦ ‖a m‖ * Real.exp (-(2 * π * c) * m))
    (z : ℂ) (hz : c ≤ z.im) :
    ‖∑' m : ℕ, a m * Complex.exp (2 * π * I * m * z)‖ ≤
      ∑' m : ℕ, ‖a m‖ * Real.exp (-(2 * π * c) * m) := by
  simpa using Complex.norm_qseries_shift_le 0 ha z hz

-- The vanishing hypothesis is vacuous when the starting index is zero.
example {b : ℕ → ℂ} {c : ℝ}
    (hs : Summable fun m : ℕ ↦ ‖b m‖ * Real.exp (-(2 * π * c) * m))
    (z : ℂ) (hz : c ≤ z.im) :
    ‖∑' m : ℕ, b m * Complex.exp (2 * π * I * m * z)‖ ≤
      ∑' m : ℕ, ‖b m‖ * Real.exp (-(2 * π * c) * m) := by
  simpa using Complex.norm_qseries_le_of_coeff_vanish 0 (by simp) hs z hz

-- At the reference height, the unshifted coefficient norm sum needs no extra factor.
example {b : ℕ → ℂ} (n₀ : ℕ) {c : ℝ}
    (hb : ∀ m < n₀, b m = 0)
    (hs : Summable fun m : ℕ ↦ ‖b m‖ * Real.exp (-(2 * π * c) * m))
    (z : ℂ) (hz : z.im = c) :
    ‖∑' m : ℕ, b m * Complex.exp (2 * π * I * m * z)‖ ≤
      ∑' m : ℕ, ‖b m‖ * Real.exp (-(2 * π * c) * m) := by
  simpa [hz] using Complex.norm_qseries_le_of_coeff_vanish n₀ hb hs z hz.ge

-- A series with only its index-one coefficient nonzero attains this boundary bound.
example (c : ℝ) :
    ‖∑' m : ℕ, (if m = 1 then (1 : ℂ) else 0) *
      Complex.exp (2 * π * I * m * (c * I))‖ = Real.exp (-(2 * π) * c) := by
  simp [ite_mul, Complex.norm_exp, Complex.mul_re, Complex.mul_im, mul_assoc]

-- Dropping the reference-height correction gives a false bound when c > 0.
example (c : ℝ) (hc : 0 < c) :
    ¬ (‖∑' m : ℕ, (if m = 1 then (1 : ℂ) else 0) *
      Complex.exp (2 * π * I * m * (c * I))‖ ≤
      (∑' m : ℕ, ‖if m = 1 then (1 : ℂ) else 0‖ *
        Real.exp (-(2 * π * c) * m)) * Real.exp (-(2 * π) * c)) := by
  have hexp : Real.exp (-(2 * π) * c) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos Real.pi_pos hc])
  simpa [ite_mul, apply_ite, Complex.norm_exp, Complex.mul_re, Complex.mul_im, mul_assoc] using
    (mul_lt_of_lt_one_right (Real.exp_pos (-(2 * π) * c)) hexp).not_ge
