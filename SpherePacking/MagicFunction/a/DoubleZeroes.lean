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


noncomputable section
set_option linter.style.longLine false
set_option linter.style.commandStart false

open Set Complex Real MagicFunction.Parametrisations MagicFunction.a.RealIntegrals

lemma corollary_7_5 : ∃ C₀ > 0, ∀ z : ℂ, ‖φ₀'' z‖ ≤
C₀ * Real.exp (-2 * Real.pi * (Complex.im z)) := by sorry
lemma corollary_7_6 : ∃ C₂ > 0, ∀ z : ℂ, ‖φ₂'' z‖ ≤ C₂ := by sorry
lemma corollary_7_7 : ∃ C₄ > 0, ∀ z : ℂ, ‖φ₄'' z‖ ≤ C₄ * Real.exp (2 * Real.pi * (Complex.im z)) := by sorry


def d (r : Ici (1 : ℝ)) := -4 * (Complex.sin (Real.pi * r / 2) ^ 2) *  ∫ t in Ici (0 : ℝ), I *
 φ₀'' (-1 / (I * t)) * (I * t)^2 *
 cexp (π * I * r * (I * t))

variable (r : ℝ) (hr : r > 2)

lemma r_gt_1 : r ∈ Ici 1 := by sorry

def φ₀_int_1 := ∫ t in Ici (0 : ℝ),
 φ₀'' (-1 / (I * t)) * (I * t)^2 *
 cexp (π * I * r * (I * t - 1))

def φ₀_int_2 := ∫ t in Ici (0 : ℝ),
 φ₀'' (-1 / (I * t - 1)) * (I * t - 1)^2 *
 cexp (π * I * r * (I * t))

def φ₀_int_3 := ∫ t in Ici (0 : ℝ),
 φ₀'' (-1 / (I * t)) * (I * t)^2 *
 cexp (π * I * r * (I * t + 1))

def φ₀_int_4 := -2 * ∫ t in Ici (0 : ℝ),
 φ₀'' (-1 / (I * t)) * (I * t)^2 *
 cexp (π * I * r * (I * t))

def φ₀_int_5 := -2 * ∫ t in Ici (1 : ℝ),
 φ₀'' (-1 / (I * t)) * (I * t)^2 *
 cexp (π * I * r * (I * t))


lemma φ₀_int_1_eq : φ₀_int_1 r = ∫ t in Ici (0 : ℝ),
 φ₀'' (-1 / ((-1 + I * t) + 1)) * ((-1 + I * t) + 1) ^ 2 *
 cexp (π * I * r * ((-1 + I * t) + 1)) := by sorry

lemma φ₀_int_3_eq : φ₀_int_3 r =  ∫ t in Ici (0 : ℝ),
 φ₀'' (-1 / ((1 + I * t) - 1)) * ((1 + I * t) - 1) ^ 2 *
 cexp (π * I * r * ((1 + I * t) - 1)) := by sorry

lemma I₅'_eq : I₅' r = φ₀_int_4 r - φ₀_int_5 r := by sorry

lemma from_4_4_1_int_1 : ∫ t in Ici (0 : ℝ),
 φ₀'' (-1 / ((-1 + I * t) + 1)) * ((-1 + I * t) + 1) ^ 2 *
 cexp (π * I * r * ((-1 + I * t) + 1)) = I₁' r + I₂' r + ∫ t in Ici (1 : ℝ),
 φ₀'' (-1 / (I * t + 1)) * (I * t + 1)^2 *
 cexp (π * I * r * (I * t)) := by sorry

lemma from_4_4_1_int_3 : ∫ t in Ici (0 : ℝ),
 φ₀'' (-1 / ((1 + I * t) - 1)) * ((1 + I * t) - 1) ^ 2 *
 cexp (π * I * r * ((1 + I * t) - 1)) = I₃' r + I₄' r +  ∫ t in Ici (1 : ℝ),
 φ₀'' (-1 / (I * t - 1)) * (I * t - 1)^2 *
 cexp (π * I * r * (I * t)) := by sorry

lemma d_eq_1 : d ⟨r, r_gt_1 r⟩ = I₁' r + I₂' r + I₃' r + I₄' r + I₅' r +
  ∫ t in Ici (1 : ℝ),
 (φ₀'' (-1 / (I * t + 1)) * (I * t + 1)^2 *
 cexp (π * I * r * (I * t)) +
 φ₀'' (-1 / (I * t - 1)) * (I * t - 1)^2 *
 cexp (π * I * r * (I * t)) +
 -2 * φ₀'' (-1 / (I * t)) * (I * t)^2 *
 cexp (π * I * r * (I * t))) := by sorry

lemma integrand_eq_2φ₀ : ∀ z : ℂ, φ₀'' (-1 / (z + 1)) * (z + 1)^2 +
 φ₀'' (-1 / (z - 1)) * (z - 1)^2 +
 φ₀'' (-1 / z) * (z)^2 = 2 * φ₀'' z := by sorry

theorem d_eq_a : d ⟨r, r_gt_1 r⟩ = a' r := by sorry
