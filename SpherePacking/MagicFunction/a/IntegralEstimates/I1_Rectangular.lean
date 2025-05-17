/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

import Mathlib

import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.MagicFunction.a.Basic_Rectangular

/-! # Constructing Upper-Bounds for I₁

The purpose of this file is to construct bounds on the integral `I₁` that is part of the definition
of the function `a`. We follow the proof of Proposition 7.8 in the blueprint.
-/

open MagicFunction.a.Parametrisations MagicFunction.a.RealIntegrals
  MagicFunction.a.RadialFunctions
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter
open scoped Function

namespace MagicFunction.a.IntegralEstimates.I1

noncomputable section Change_of_Variables

variable (r : ℝ)

/-! We begin by performing changes of variables. -/
-- #check intervalIntegral.integral_comp_smul_deriv
-- #check MeasureTheory.integral_image_eq_integral_abs_deriv_smul

def f : ℝ → ℝ := fun t ↦ 1 / t

def f' : ℝ → ℝ := fun t ↦ -1 / t ^ 2

def g : ℝ → ℝ → ℂ := fun r s ↦
  φ₀'' (I * s)
  * (s ^ (-4 : ℤ))
  * cexp (-π * I * r)
  * cexp (I * π * r / s)

lemma aux_measurable : MeasurableSet ((Ioo 0 1) : Set ℝ) := measurableSet_Ioo

lemma aux_hasDeriv (x : ℝ) (hx : x ∈ Ioo 0 1) : HasDerivWithinAt f (f' x) (Ioo 0 1) x := by
  have hf : f = fun t ↦ (t ^ (-1 : ℤ)) := by
    ext t
    rw [f, div_eq_mul_inv, zpow_neg, zpow_one, one_mul]
  have hf' : f' = fun t ↦ -(t ^ (-2 : ℤ)) := by
    ext t
    rw [f', div_eq_mul_inv, zpow_neg, neg_mul, one_mul]
    rfl
  simp only [hf, hf']
  have : -x ^ (-2 : ℤ) = (-1 : ℤ) * x ^ ((-1 : ℤ) - 1) := by simp
  rw [this]
  exact hasDerivWithinAt_zpow (-1 : ℤ) x (Or.inl (ne_of_gt hx.1)) (Ioo 0 1)

lemma aux_injOn : InjOn f (Ioo 0 1) := by
  intro _ _ _ _ hf
  simp only [f, div_eq_mul_inv, neg_mul, one_mul, neg_inj, inv_inj] at hf
  exact hf

lemma Changing_Domain_of_Integration (r : ℝ) :
    ∫ s in Ioi (1 : ℝ), (g r s) = ∫ (s : ℝ) in f '' (Ioo (0 : ℝ) (1 : ℝ)), (g r s) := by
  congr
  ext x
  constructor <;> intro hx
  · use x⁻¹
    simp only [mem_Ioi, mem_Ioo] at hx ⊢
    constructor
    · refine ⟨by positivity, ?_⟩
      rw [← mul_one x⁻¹, inv_mul_lt_one₀ (by positivity)]
      exact hx
    · rw [f, div_inv_eq_mul, one_mul]
  · obtain ⟨y, hy₁, hy₂⟩ := hx
    rw [← hy₂, f]
    simp only [one_div, mul_inv_rev, mem_Ioi, inv_pos, Nat.ofNat_pos, lt_mul_iff_one_lt_left]
    exact one_lt_inv_iff₀.mpr hy₁

lemma Changing_Variables (r : ℝ) : ∫ (s : ℝ) in f '' (Ioo (0 : ℝ) (1 : ℝ)), (g r s) =
    ∫ (t : ℝ) in Ioo 0 1, |f' t| • (g r (f t)) :=
  integral_image_eq_integral_abs_deriv_smul aux_measurable aux_hasDeriv aux_injOn (g r)

end Change_of_Variables
