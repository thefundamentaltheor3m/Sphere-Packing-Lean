/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

import Mathlib

import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.MagicFunction.a.Basic
import SpherePacking.Tactic.NormNumI

/-! # Constructing Upper-Bounds for I₄

The purpose of this file is to construct bounds on the integral `I₄` that is part of the definition
of the function `a`. We follow the proof of Proposition 7.8 in the blueprint.

## TODO:
- Integrability of `g` and `C₀ * rexp (-2 * π * s) * rexp (-π * r / s)`
-/

open MagicFunction.a.Parametrisations MagicFunction.a.RealIntegrals
  MagicFunction.a.RadialFunctions MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open scoped Function UpperHalfPlane

namespace MagicFunction.a.IntegralEstimates.I₄

variable (r : ℝ)

section Setup

noncomputable def g : ℝ → ℝ → ℂ := fun r t ↦ φ₀'' (-1 / (-t + I))
    * (-t + I) ^ 2
    * cexp (π * I * r)
    * cexp (-π * I * r * t)
    * cexp (-π * r)

lemma I₄'_eq_integral_g_Ioo (r : ℝ) : I₄' r = ∫ t in Ioo (0 : ℝ) 1, g r t := by
  simp only [I₄'_eq, neg_mul, intervalIntegral_eq_integral_uIoc, zero_le_one, ↓reduceIte,
    uIoc_of_le, one_smul, g, integral_Ioc_eq_integral_Ioo]

end Setup

-- #exit

-- The rest of this file needs fixing.

----------------------------------------------------------------

section Bounding

section Bounding_Integrand

lemma I₄'_bounding_aux_1 (r : ℝ) : ∀ t ∈ Ioo (0 : ℝ) 1, ‖g r t‖ ≤
    ‖φ₀'' (-1 / (-t + I))‖ * 2 * rexp (-π * r) := by
  intro t ht
  obtain ⟨ht₀, ht₁⟩ := ht
  rw [g, norm_mul, norm_mul, norm_mul, mul_assoc, mul_assoc, norm_mul]
  gcongr
  · rw [norm_pow, ← normSq_eq_norm_sq, normSq_apply, add_re, neg_re, ofReal_re, I_re,
      add_zero, mul_neg, neg_mul, neg_neg, add_im, neg_im, ofReal_im, neg_zero, I_im, zero_add,
      mul_one]
    nlinarith
  · conv_rhs => rw [← one_mul (rexp _), ← one_mul (rexp _)]
    gcongr <;> apply le_of_eq
    · calc
      _ = ‖cexp (((π * r : ℝ) : ℂ) * I)‖ := by congr 2; push_cast; ac_rfl
      _ = 1 := norm_exp_ofReal_mul_I (π * r)
    · calc
      _ = ‖cexp (((-π * r * t : ℝ) : ℂ) * I)‖ := by congr 2; push_cast; ac_rfl
      _ = 1 := norm_exp_ofReal_mul_I (-π * r * t)
    · rw [norm_exp]
      simp

lemma parametrisation_eq : ∀ t ∈ Ioo (0 : ℝ) 1,
    (-1 / (-↑t + I)) = t / (t ^ 2 + 1) + (1 / (t ^ 2 + 1) * I) := by
  intro t ht
  obtain ⟨ht₀, ht₁⟩ := ht
  calc
  _ = (-1 / (-t + I)) * ((-t - I) / (-t - I)) := by
      conv_lhs => rw [← mul_one (-1 / (-t + I))]
      congr; symm
      apply div_self
      intro h
      conv at h => rw [sub_eq_add_neg, add_comm, ← sub_eq_add_neg, sub_eq_zero]
      -- This has to be the most ridiculous proof ever. It should never have to go down to 0 ≠ 1 :(
      have h₁ : (ofReal t).im = 0 := ofReal_im t
      have h₂ : (ofReal t).im = -1 := by rw [← h]; norm_num1 -- `simp` works too
      rw [h₁] at h₂
      norm_num1 at h₂
  _ = _ := by
      conv_lhs => rw [div_mul_div_comm (-1) (-t + I)]
      simp only [neg_mul, one_mul, neg_sub, div_mul_eq_mul_div, div_add_div_same]
      congr
      · ring
      · ring_nf
        rw [I_sq]
        ring

lemma im_parametrisation_eq : ∀ t ∈ Ioo (0 : ℝ) 1, (-1 / (-↑t + I)).im = 1 / (t ^ 2 + 1) := by
  intro t ht
  conv_lhs => rw [parametrisation_eq t ht, add_im]
  norm_cast
  rw [zero_add, mul_I_im, ofReal_re]

lemma im_parametrisation_lower : ∀ t ∈ Ioo (0 : ℝ) 1, 1 / 2 < (-1 / (-↑t + I)).im := by
  intro t ht
  have hpos : 0 < t ^ 2 + 1 := by positivity
  rw [im_parametrisation_eq t ht, one_div, one_div, inv_lt_inv₀ two_pos hpos]
  obtain ⟨ht₀, ht₁⟩ := ht
  nlinarith

lemma im_parametrisation_upper : ∀ t ∈ Ioo (0 : ℝ) 1, (-1 / (-↑t + I)).im < 1 := by
  intro t ht
  rw [im_parametrisation_eq t ht, one_div, ← inv_one, inv_lt_inv₀]
  obtain ⟨ht₀, ht₁⟩ := ht
  · simp_all only [inv_one, lt_add_iff_pos_left, pow_pos]
  · positivity
  · exact one_pos

lemma I₄'_bounding_aux_2 (r : ℝ) : ∃ C₀ > 0, ∀ t ∈ Ioo (0 : ℝ) 1,
    ‖g r t‖ ≤ C₀ * rexp (-2 * π * (-1 / (-t + I)).im) * 2 * rexp (-π * r) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀_le -- The `PolyFourierCoeffBound` of `φ₀`
  use C₀, hC₀_pos
  intro t ht
  apply (I₄'_bounding_aux_1 r t ht).trans
  gcongr
  have him : 1 / 2 < (-1 / (-↑t + I)).im := im_parametrisation_lower t ht
  have hpos : 0 < (-1 / (-↑t + I)).im := one_half_pos.trans him
  let z : ℍ := ⟨-1 / (-t + I), hpos⟩
  specialize hC₀ z him
  simp only [φ₀'', hpos, ↓reduceDIte]
  exact hC₀

lemma I₄'_bounding_aux_3 (r : ℝ) :  ∃ C₀ > 0, ∀ t ∈ Ioo (0 : ℝ) 1,
    ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := I₄'_bounding_aux_2 r -- The `PolyFourierCoeffBound` of `φ₀`
  use C₀, hC₀_pos
  intro t ht
  apply (hC₀ t ht).trans
  gcongr
  simp only [neg_mul, neg_le_neg_iff]
  conv_rhs => rw [mul_comm 2 π]
  have hcalc : π = π * 2 * (1 / 2) := by simp
  conv_lhs => rw [hcalc]
  gcongr
  exact le_of_lt <| im_parametrisation_lower t ht

end Bounding_Integrand

section Integrability

lemma Bound_integrableOn (r C₀ : ℝ) :
    IntegrableOn (fun _ ↦ C₀ * rexp (-π) * 2 * rexp (-π * r)) (Ioo (0 : ℝ) 1) volume := by
  rw [integrableOn_const_iff]
  right
  exact measure_Ioo_lt_top

end Integrability

section Bounding_Integral

lemma I₄'_bounding_aux_4 (r : ℝ) :  ∃ C₀ > 0,
    ∫ t in Ioo (0 : ℝ) 1, ‖g r t‖ ≤ ∫ _ in Ioo (0 : ℝ) 1, C₀ * rexp (-π) * 2 * rexp (-π * r) := by
  wlog hint : IntegrableOn (fun t ↦ ‖g r t‖) (Ioo (0 : ℝ) 1) volume
  · refine ⟨1, by positivity, ?_⟩
    haveI h₁ : CompleteSpace ℝ := inferInstance
    have h₂ : ¬ (Integrable (fun t ↦ ‖g r t‖) (volume.restrict (Ioo (0 : ℝ) 1))) := hint
    conv_lhs => simp only [integral, h₁, h₂, ↓reduceDIte]
    positivity
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := I₄'_bounding_aux_3 r
  use C₀, hC₀_pos
  exact setIntegral_mono_on hint (Bound_integrableOn r C₀) measurableSet_Ioo hC₀

theorem I₄'_bounding (r : ℝ) : ∃ C₁ > 0, ‖I₄' r‖ ≤ C₁ * rexp (-π * r) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := I₄'_bounding_aux_4 r
  refine ⟨C₀ * rexp (-π) * 2, by positivity, ?_⟩
  calc
  _ = ‖∫ t in Ioo (0 : ℝ) 1, g r t‖ := by rw [I₄'_eq_integral_g_Ioo]
  _ ≤ ∫ t in Ioo (0 : ℝ) 1, ‖g r t‖ := norm_integral_le_integral_norm (g r)
  _ ≤ ∫ _ in Ioo (0 : ℝ) 1, C₀ * rexp (-π) * 2 * rexp (-π * r) := hC₀
  _ = _ := by simp

-- The following may be useful:
-- #check MeasureTheory.integral_mono_of_nonneg -- integrability can't be avoided...
-- #check MeasureTheory.setLIntegral_mono
-- #check MeasureTheory.setIntegral_mono_on

end Bounding_Integral

end Bounding

----------------------------------------------------------------

section Higher_iteratedFDerivs



end Higher_iteratedFDerivs

----------------------------------------------------------------

noncomputable section Schwartz_Decay

open SchwartzMap

section Zeroth_Derivative

theorem decay'₀ : ∀ (k : ℕ), ∃ C, ∀ (x : ℝ), ‖x‖ ^ k * ‖I₄' x‖ ≤ C := by

  sorry

end Zeroth_Derivative

section Higher_iteratedFDerivs

theorem decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₄' x‖ ≤ C := by

  sorry

end Higher_iteratedFDerivs

-- def I₄'_Schwartz : 𝓢(ℝ, ℂ) where
--   toFun := I₄'
--   smooth' := sorry
--   decay' := by extract_goal; sorry

end Schwartz_Decay
