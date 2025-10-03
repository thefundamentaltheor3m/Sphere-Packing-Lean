/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import Mathlib.Analysis.Real.Pi.Bounds

import SpherePacking.MagicFunction.a.Eigenfunction
import SpherePacking.MagicFunction.a.SpecialValues
import SpherePacking.MagicFunction.b.Eigenfunction
import SpherePacking.MagicFunction.b.SpecialValues
import SpherePacking.Tactic.NormNumI

/-! # Viazovska's Magic Function

In this file, we define Viazovska's magic funtction `g`.
-/

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open SchwartzMap Complex Real MagicFunction.FourierEigenfunctions MagicFunction.a.Fourier
  MagicFunction.b.Fourier MagicFunction.a.SpecialValues MagicFunction.b.SpecialValues

/-- The Magic Function, `g`. -/
noncomputable def g : 𝓢(ℝ⁸, ℂ) := ((π * I) / 8640) • a + (I / (240 * π)) • b

-- Note that in the proof, we need `g` to be Real-valued. We need to decide how we want to state
-- this: either `g ∘ Complex.im = 0` or we actually construct an element of `𝓢(ℝ⁸, ℝ)`...

section Zero

theorem g_zero : g 0 = 1 := by
  simp only [g, add_apply, smul_apply, a_zero, neg_mul, smul_eq_mul, b_zero, mul_zero, add_zero]
  ring_nf
  simp only [I_sq, mul_neg, mul_one, neg_mul, neg_neg]
  apply Complex.mul_inv_cancel
  norm_cast
  exact pi_ne_zero

theorem fourier_g_zero : fourierTransformCLE ℂ g 0 = 1 := by
  simp only [g, map_add, map_smul, eig_a, eig_b, add_apply, smul_apply, a_zero, smul_eq_mul]
  have : (-b) 0 = -(b 0) := rfl
  ring_nf
  simp only [I_sq, mul_neg, mul_one, neg_mul, neg_neg, this, b_zero, neg_zero, mul_zero, one_div,
    zero_mul, add_zero]
  apply Complex.mul_inv_cancel
  norm_cast
  exact pi_ne_zero

theorem g_zero_eq_fourier_g_zero : g 0 = fourierTransformCLE ℂ g 0 := by rw [g_zero, fourier_g_zero]

end Zero
