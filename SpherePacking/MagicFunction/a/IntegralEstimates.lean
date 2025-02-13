/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

import Mathlib

import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.MagicFunction.a.Basic

/-! # Constructing Upper-Bounds for I₁, I₂, I₃ and I₄

The purpose of this file is to construct bounds on the integrals `I₁`, `I₂`, `I₃` and `I₄` that
make up the function `a`. We follow the proof of Proposition 7.8 in the blueprint.
-/

open MagicFunction Complex Real Set MeasureTheory MeasureTheory.Measure
open scoped Function

-- namespace MagicFunction

noncomputable section I₁

variable (r : ℝ)

/-! We begin by performing changes of variables. -/
-- #check intervalIntegral.integral_comp_smul_deriv
#check MeasureTheory.integral_image_eq_integral_abs_deriv_smul

/- 1. (z + 1) ↦ -1 / (z + 1) -/
private def f : ℝ → ℝ := fun t ↦ 1 / (2 * t)

private def f' : ℝ → ℝ := fun t ↦ -1 / (2 * t ^ 2)

private def g : ℝ → ℝ → ℂ := fun r s ↦
    φ₀'' ((I + 1) * s) * ((I + 1) / (2 * s)) ^ 2 * (-1 / (2 * s)) ^ 2
      * cexp (I * π * r ^ 2 * (1 / (2 * s)) * (I - 1))

private lemma aux_measurable : MeasurableSet ((Ioo 0 1) : Set ℝ) := measurableSet_Ioo

private lemma aux_hasDeriv (x : ℝ) (hx : x ∈ Ioo 0 1) : HasDerivWithinAt f (f' x) (Ioo 0 1) x := by
  sorry

private lemma aux_injOn : InjOn f (Ioo 0 1) := by
  sorry

private lemma calc_aux_1 (r : ℝ) :
    ∫ (s : ℝ) in Ioi ((1 / 2) : ℝ), (g r s) = ∫ (s : ℝ) in f '' (Ioo (0 : ℝ) (1 : ℝ)), (g r s) := by
  congr
  ext x
  constructor <;> intro hx
  · use 1 / (2 * x)
    simp only [mem_Ioi, mem_Ioo] at hx ⊢
    constructor
    · refine ⟨by positivity, ?_⟩
      rw [one_div, mul_inv_rev, inv_mul_lt_one₀ (by positivity), ← one_div]
      exact hx
    field_simp [f]
  · obtain ⟨y, hy₁, hy₂⟩ := hx
    rw [← hy₂, f]
    simp
    exact one_lt_inv_iff₀.mpr hy₁

private lemma calc_aux_2 (r : ℝ) : ∫ (s : ℝ) in f '' (Ioo (0 : ℝ) (1 : ℝ)), (g r s) =
    ∫ (t : ℝ) in Ioo 0 1, |f' t| • (g r (f t)) :=
  integral_image_eq_integral_abs_deriv_smul aux_measurable aux_hasDeriv aux_injOn (g r)

private lemma calc_aux_3 (r : ℝ) : ∫ (t : ℝ) in Ioo 0 1, |f' t| • (g r (f t)) = I₁' r := by
  congr
  ext t
  sorry

end I₁
