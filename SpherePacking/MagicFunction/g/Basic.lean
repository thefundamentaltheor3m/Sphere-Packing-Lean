/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds

public import SpherePacking.MagicFunction.a.Eigenfunction
public import SpherePacking.MagicFunction.a.SpecialValues
public import SpherePacking.MagicFunction.b.Eigenfunction
public import SpherePacking.MagicFunction.b.SpecialValues
public import SpherePacking.Tactic.NormNumI

/-! # Viazovska's Magic Function

In this file, we define Viazovska's magic funtction `g`.
-/

@[expose] public section
local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open scoped FourierTransform

open SchwartzMap Complex Real MagicFunction.FourierEigenfunctions MagicFunction.a.Fourier
  MagicFunction.b.Fourier MagicFunction.a.SpecialValues MagicFunction.b.SpecialValues

/-- The Magic Function, `g`. -/
noncomputable def g : RadialSchwartzMap ℂ ℝ⁸ ℂ := ((π * I) / 8640) • a + (I / (240 * π)) • b

-- Note that in the proof, we need `g` to be Real-valued. We need to decide how we want to state
-- this: either `Complex.im ∘ g = 0` or we actually construct an element of
-- `RadialSchwartzMap ℝ ℝ⁸ ℝ` or something...

section Zero

@[simp]
theorem g_apply (x : ℝ⁸) : g x = (π * I) / 8640 * a x + I / (240 * π) * b x := rfl

theorem fourier_g_eq : 𝓕 g = ((π * I) / 8640) • a + (I / (240 * π)) • (-b) := by
  have hg : g = ((π * I) / 8640) • a + (I / (240 * π)) • b := rfl
  rw [hg, FourierTransform.fourier_add, FourierTransform.fourier_smul,
    FourierTransform.fourier_smul, eig_a, eig_b]

@[simp]
theorem fourier_g_apply (x : ℝ⁸) : 𝓕 g x = (π * I) / 8640 * a x - I / (240 * π) * b x := by
  rw [fourier_g_eq]
  simp only [RadialSchwartzMap.add_apply, RadialSchwartzMap.smul_apply,
    RadialSchwartzMap.neg_apply, smul_eq_mul, mul_neg, ← sub_eq_add_neg]

theorem g_zero : g 0 = 1 := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  rw [g_apply, a_zero, b_zero, mul_zero, add_zero]
  field_simp
  simp [I_sq]

theorem fourier_g_zero : 𝓕 g 0 = 1 := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  rw [fourier_g_apply, a_zero, b_zero, mul_zero, sub_zero]
  field_simp
  simp [I_sq]

theorem g_zero_eq_fourier_g_zero : g 0 = 𝓕 g 0 := by
  rw [g_zero, fourier_g_zero]

end Zero
