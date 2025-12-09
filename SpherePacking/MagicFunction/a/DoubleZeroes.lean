/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: (Add your names here)
-/

import SpherePacking.ModularForms.Eisenstein
import SpherePacking.MagicFunction.a.Basic
import SpherePacking.MagicFunction.IntegralParametrisations
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic


noncomputable section
set_option linter.style.longLine false
set_option linter.style.commandStart false

open Set Complex Real MeasureTheory MagicFunction.Parametrisations MagicFunction.a.RealIntegrals

lemma corollary_7_5 : ∃ C₀ > 0, ∀ z : ℂ, ‖φ₀'' z‖ ≤
C₀ * Real.exp (-2 * Real.pi * (Complex.im z)) := by sorry
lemma corollary_7_6 : ∃ C₂ > 0, ∀ z : ℂ, ‖φ₂'' z‖ ≤ C₂ := by sorry
lemma corollary_7_7 : ∃ C₄ > 0, ∀ z : ℂ, ‖φ₄'' z‖ ≤ C₄ * Real.exp (2 * Real.pi * (Complex.im z)) := by sorry


def d (r : Ici (1 : ℝ)) := -4 * (Complex.sin (Real.pi * r / 2) ^ 2) *  ∫ t in Ici (0 : ℝ),
 φ₀'' (-1 / (I * t)) * (I * t)^2 *
 cexp (I * π * r * (I * t))

variable (r : ℝ) (hr : r > 2)

lemma r_gt_1 : r ∈ Ici 1 := by sorry

lemma sin_eq_exp : -4 * (Complex.sin (Real.pi * r / 2))^2 =
  Complex.exp (I * Real.pi * r) - 2 + Complex.exp (-I * Real.pi * r) := by sorry

def φ₀_int_1 := ∫ t in Ici (0 : ℝ),
 φ₀'' (-1 / ((-1 + I * t) + 1)) * ((-1 + I * t) + 1) ^ 2 *
 cexp (I * π * r * ((-1 + I * t) + 1))

def φ₀_int_2 := ∫ t in Ici (0 : ℝ),
 φ₀'' (-1 / (I * t - 1)) * (I * t - 1) ^ 2 *
 cexp (I * π * r * (I * t))

def φ₀_int_3 := ∫ t in Ici (0 : ℝ),
 φ₀'' (-1 / ((1 + I * t) - 1)) * ((1 + I * t) - 1) ^ 2 *
 cexp (I * π * r * ((1 + I * t) - 1))

lemma φ₀_int_1_eq : φ₀_int_1 r = ∫ t in Ici (0 : ℝ),
 φ₀'' (-1 / (I * t)) * (I * t)^2 *
 cexp (I * π * r * (I * t - 1)) := by sorry

lemma φ₀_int_3_eq : φ₀_int_3 r = ∫ t in Ici (0 : ℝ),
 φ₀'' (-1 / (I * t)) * (I * t)^2 *
 cexp (I * π * r * (I * t + 1)) := by sorry

lemma d_eq_2 : d ⟨r, r_gt_1 r⟩ = φ₀_int_1 r + φ₀_int_2 r + φ₀_int_3 r := by
  calc
      _ =  -4 * (Complex.sin (Real.pi * r / 2) ^ 2) *
              ∫ t in Ici (0 : ℝ), φ₀'' (-1 / (I * t)) *
              (I * t)^2 * cexp (I * π * r * (I * t)) := rfl
      _ = φ₀_int_1 r + φ₀_int_2 r + φ₀_int_3 r := ?_
  · rw [sin_eq_exp]
    rw [<- integral_const_mul_of_integrable]
    simp [add_mul, sub_mul]
    rw [integral_add, integral_sub]

    have : (∫ (a : ℝ) in Ici 0, cexp (I * ↑π * ↑r) * (φ₀'' (-1 / (I * ↑a)) * (I * ↑a) ^ 2 * cexp (↑I * π * ↑r * (I * ↑a)))) = φ₀_int_3 r := by
      conv_lhs =>
        pattern (cexp _ * _)
        rw [mul_comm, mul_assoc, ← Complex.exp_add]
      conv_lhs =>
        pattern cexp (_ + _)
        rw [add_comm, ← mul_one_add, add_comm]
      simp [φ₀_int_3_eq r]
    rw [this]

    have : (∫ (a : ℝ) in Ici 0, cexp (-(I * ↑π * ↑r)) * (φ₀'' (-1 / (I * ↑a)) * (I * ↑a) ^ 2 * cexp (↑I * π * ↑r * (I * ↑a)))) = φ₀_int_1 r := by
      conv_lhs =>
        pattern (cexp _ * _)
        rw [mul_comm, mul_assoc, ← Complex.exp_add]
      conv_lhs =>
        pattern cexp (_ + _)
        rw [add_comm, ← neg_one_mul]
      have : forall a, (-1 * (I * ↑π * ↑r) + I * ↑π * ↑r * (I * ↑a)) = I * ↑π * ↑r * (I * ↑a - 1) := by grind
      conv_lhs =>
        pattern cexp _
        rw [this]
      simp [φ₀_int_1_eq r]
    rw [this]

    rw [sub_eq_add_neg]
    have : - ∫ (a : ℝ) in Ici 0, 2 * (φ₀'' (-1 / (I * ↑a)) * (I * ↑a) ^ 2 * cexp (I * ↑π * ↑r * (I * ↑a))) = φ₀_int_2 r := by
      sorry

    simp [this]
    grind

    -- All remaining goals are about Integrability of some functions.
    -- We will probably need to adapt the proofs from IntegralEstimates/*.lean
    all_goals sorry


def φ₀_int_4 := -2 * ∫ t in Ici (0 : ℝ),
 φ₀'' (-1 / (I * t)) * (I * t)^2 *
 cexp (I * π * r * (I * t))

def φ₀_int_5 := -2 * ∫ t in Ici (1 : ℝ),
 φ₀'' (-1 / (I * t)) * (I * t)^2 *
 cexp (I * π * r * (I * t))


lemma I₅'_eq : I₅' r = φ₀_int_4 r - φ₀_int_5 r := by sorry

lemma from_4_4_1_int_1 : ∫ t in Ici (0 : ℝ),
 φ₀'' (-1 / ((-1 + I * t) + 1)) * ((-1 + I * t) + 1) ^ 2 *
 cexp (I * π * r * ((-1 + I * t) + 1)) = I₁' r + I₂' r + ∫ t in Ici (1 : ℝ),
 φ₀'' (-1 / (I * t + 1)) * (I * t + 1)^2 *
 cexp (I * π * r * (I * t)) := by sorry

lemma from_4_4_1_int_3 : ∫ t in Ici (0 : ℝ),
 φ₀'' (-1 / ((1 + I * t) - 1)) * ((1 + I * t) - 1) ^ 2 *
 cexp (I * π * r * ((1 + I * t) - 1)) = I₃' r + I₄' r +  ∫ t in Ici (1 : ℝ),
 φ₀'' (-1 / (I * t - 1)) * (I * t - 1)^2 *
 cexp (I * π * r * (I * t)) := by sorry

lemma d_eq_1 : d ⟨r, r_gt_1 r⟩ = I₁' r + I₂' r + I₃' r + I₄' r + I₅' r +
  ∫ t in Ici (1 : ℝ),
 (φ₀'' (-1 / (I * t + 1)) * (I * t + 1)^2 *
 cexp (I * π * r * (I * t)) +
 φ₀'' (-1 / (I * t - 1)) * (I * t - 1)^2 *
 cexp (I * π * r * (I * t)) +
 -2 * φ₀'' (-1 / (I * t)) * (I * t)^2 *
 cexp (I * π * r * (I * t))) := by sorry

lemma integrand_eq_2φ₀ : ∀ z : ℂ, φ₀'' (-1 / (z + 1)) * (z + 1)^2 +
 φ₀'' (-1 / (z - 1)) * (z - 1)^2 +
 φ₀'' (-1 / z) * (z)^2 = 2 * φ₀'' z := by sorry

theorem d_eq_a : d ⟨r, r_gt_1 r⟩ = a' r := by sorry
