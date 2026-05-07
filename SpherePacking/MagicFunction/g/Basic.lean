/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.a.Schwartz.Basic
public import SpherePacking.MagicFunction.b.Schwartz.Basic
import SpherePacking.MagicFunction.a.Eigenfunction.FourierPermutations
import SpherePacking.MagicFunction.a.SpecialValues
import SpherePacking.MagicFunction.b.Eigenfunction.FourierPermutations
import SpherePacking.MagicFunction.b.SpecialValues
import SpherePacking.Tactic.NormNumI

/-! # Viazovska's Magic Function `g` and its normalization at `0`. -/

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open SchwartzMap Complex Real MagicFunction.FourierEigenfunctions MagicFunction.a.SpecialValues
  MagicFunction.b.SpecialValues

noncomputable section

/-- The Magic Function, `g`. -/
@[expose] public def g : 𝓢(ℝ⁸, ℂ) := ((π * I) / 8640) • a - (I / (240 * π)) • b

/-- Normalization of `g` at the origin. -/
public theorem g_zero : g 0 = 1 := by
  simp [g, a_zero, b_zero, sub_eq_add_neg, smul_eq_mul, div_eq_mul_inv]
  field_simp [show (π : ℂ) ≠ 0 by exact_mod_cast pi_ne_zero]; ring_nf; norm_num1

/-- Normalization of the Fourier transform of `g` at the origin. -/
public theorem fourier_g_zero : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) g 0 = 1 := by
  simp only [g, map_sub, map_smul, MagicFunction.a.Fourier.eig_a, MagicFunction.b.Fourier.eig_b,
    sub_apply, smul_apply, smul_eq_mul]
  simp [a_zero, b_zero, sub_eq_add_neg, div_eq_mul_inv]
  field_simp [show (π : ℂ) ≠ 0 by exact_mod_cast pi_ne_zero]; ring_nf; norm_num1

end
