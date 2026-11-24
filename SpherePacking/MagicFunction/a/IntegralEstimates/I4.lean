/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.a.Basic

import SpherePacking.ForMathlib.SetIntegralMono
import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.Tactic.ComplexGrind

/-!
# Constructing Upper-Bounds for I₄

The purpose of this file is to construct bounds on the integral `I₄` that is part of the definition
of the function `a`. We follow the proof of Proposition 7.8 in the blueprint.

## TODO:
- Integrability of `g` and `C₀ * rexp (-2 * π * s) * rexp (-π * r / s)`
-/

@[expose] public section

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals
  MagicFunction.a.RadialFunctions MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open scoped Function UpperHalfPlane ComplexGrind

namespace MagicFunction.a.IntegralEstimates.I₄

variable (r : ℝ)

section Setup

noncomputable def g : ℝ → ℝ → ℂ := fun r t ↦ -1
    * φ₀'' (-1 / (-t + I))
    * (-t + I) ^ 2
    * cexp (π * I * r)
    * cexp (-π * I * r * t)
    * cexp (-π * r)

lemma I₄'_eq_integral_g_Ioo (r : ℝ) : I₄' r = ∫ t in Ioo (0 : ℝ) 1, g r t := by
  simp only [I₄'_eq, g, integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

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
  have h : ‖-(t : ℂ) + I‖ ^ 2 ≤ 2 := by
    rw [← normSq_eq_norm_sq, normSq_apply]
    simp only [add_re, neg_re, ofReal_re, I_re, add_im, neg_im, ofReal_im, I_im]
    nlinarith
  calc ‖g r t‖ = ‖φ₀'' (-1 / (-t + I))‖ * ‖-(t : ℂ) + I‖ ^ 2 * rexp (-π * r) := by
        simp [g, norm_exp]
    _ ≤ _ := by gcongr

lemma parametrisation_eq : ∀ t ∈ Ioo (0 : ℝ) 1,
    (-1 / (-↑t + I)) = t / (t ^ 2 + 1) + (1 / (t ^ 2 + 1) * I) := by
  intro t _
  have h₁ : -(t : ℂ) + I ≠ 0 := by grind
  have h₂ : (t : ℂ) ^ 2 + 1 ≠ 0 := by norm_cast; positivity
  field_simp
  grind

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
  · obtain ⟨ht₀, ht₁⟩ := ht
    simp_all [inv_one, lt_add_iff_pos_left]
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

lemma I₄'_bounding_aux_3 (r : ℝ) : ∃ C₀ > 0, ∀ t ∈ Ioo (0 : ℝ) 1,
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

lemma I₄'_bounding_aux_4 (r : ℝ) : ∃ C₀ > 0,
    ∫ t in Ioo (0 : ℝ) 1, ‖g r t‖ ≤ ∫ _ in Ioo (0 : ℝ) 1, C₀ * rexp (-π) * 2 * rexp (-π * r) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := I₄'_bounding_aux_3 r
  exact ⟨C₀, hC₀_pos, setIntegral_mono_on_of_nonneg measurableSet_Ioo (fun _ _ ↦ norm_nonneg _)
    (Bound_integrableOn r C₀) hC₀⟩

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
-- toFun := I₄'
-- smooth' := sorry
-- decay' := by extract_goal; sorry

end Schwartz_Decay
end MagicFunction.a.IntegralEstimates.I₄
