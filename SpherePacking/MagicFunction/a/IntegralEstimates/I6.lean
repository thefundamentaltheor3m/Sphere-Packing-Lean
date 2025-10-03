/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.MagicFunction.a.Basic

/-! # Constructing Upper-Bounds for I₆

The purpose of this file is to construct bounds on the integral `I₆` that is part of the definition
of the function `a`. We follow the proof of Proposition 7.8 in the blueprint.

## TODO:
- Integrability of `g` and `C₀ * rexp (-2 * π * s) * rexp (-π * r / s)`
-/

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals
  MagicFunction.a.RadialFunctions MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open scoped Function UpperHalfPlane

namespace MagicFunction.a.IntegralEstimates.I₆

variable (r : ℝ)

section Setup

noncomputable def g : ℝ → ℝ → ℂ := fun r t ↦ I
  * φ₀'' (I * t)
  * cexp (-π * r * t)

lemma I₆'_eq_integral_g_Ioo (r : ℝ) : I₆' r = 2 * ∫ t in Ici (1 : ℝ), g r t := by simp [I₆'_eq, g]

end Setup

----------------------------------------------------------------

section Bounding

section Bounding_Integrand

lemma I₆'_bounding_aux_1 (r : ℝ) : ∀ t ∈ Ici 1, ‖g r t‖ = ‖φ₀'' (I * t)‖ * rexp (-π * r * t) := by
  simp [g, neg_mul, norm_I, one_mul, norm_exp]

lemma I₆'_bounding_aux_2 (r : ℝ) : ∃ C₀ > 0, ∀ t ∈ Ici (1 : ℝ),
    ‖g r t‖ ≤ C₀ * rexp (-2 * π * t) * rexp (-π * r * t) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀_le -- The `PolyFourierCoeffBound` of `φ₀`
  use C₀, hC₀_pos
  intro t ht
  rw [I₆'_bounding_aux_1 r t ht]
  rw [mem_Ici] at ht
  gcongr
  have him : (I * t).im = t := by simp
  have hpos : 0 < (I * t).im := by rw [him]; linarith
  have h_half_lt_one : 1 / 2 < (I * t).im := by rw [him]; linarith
  let z : ℍ := ⟨I * t, hpos⟩
  have him' : z.im = t := him
  specialize hC₀ z h_half_lt_one
  simp only [φ₀'', hpos, ↓reduceDIte]
  simp only [him'] at hC₀
  exact hC₀

end Bounding_Integrand

section Integrability

lemma Bound_integrableOn (r C₀ : ℝ) (hC₀_pos : C₀ > 0)
  (hC₀ : ∀ t ∈ Ici 1, ‖g r t‖ ≤ C₀ * rexp (-2 * π * t) * rexp (-π * r * t)) :
  IntegrableOn (fun t ↦ C₀ * rexp (-2 * π * t) * rexp (-π * r * t)) (Ici (1 : ℝ)) volume := sorry

end Integrability

section Bounding_Integral

lemma I₆'_bounding_aux_3 (r : ℝ) : ∃ C₀ > 0,
    ∫ t in Ici (1 : ℝ), ‖g r t‖ ≤
    ∫ t in Ici (1 : ℝ), C₀ * rexp (-2 * π * t) * rexp (-π * r * t) := by
  wlog hint : IntegrableOn (fun t ↦ ‖g r t‖) (Ici (1 : ℝ)) volume
  · refine ⟨1, by positivity, ?_⟩
    haveI h₁ : CompleteSpace ℝ := inferInstance
    have h₂ : ¬ (Integrable (fun t ↦ ‖g r t‖) (volume.restrict (Ici 1))) := hint
    conv_lhs => simp only [integral, h₁, h₂, ↓reduceDIte]
    positivity
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := I₆'_bounding_aux_2 r
  use C₀, hC₀_pos
  exact setIntegral_mono_on hint (Bound_integrableOn r C₀ hC₀_pos hC₀) measurableSet_Ici hC₀

theorem I₆'_bounding (r : ℝ) : ∃ C₁ > 0,
    ‖I₆' r‖ ≤ ∫ t in Ici (1 : ℝ), C₁ * rexp (-2 * π * t) * rexp (-π * r * t) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := I₆'_bounding_aux_3 r
  refine ⟨2 * C₀, by positivity, ?_⟩
  calc
  _ = ‖2 * ∫ t in Ici (1 : ℝ), g r t‖ := by simp only [I₆'_eq_integral_g_Ioo, g]
  _ ≤ 2 * ∫ t in Ici (1 : ℝ), ‖g r t‖ := by
      simp only [norm_mul, Complex.norm_ofNat, Nat.ofNat_pos, mul_le_mul_iff_right₀]
      exact norm_integral_le_integral_norm (g r)
  _ ≤ 2 * ∫ t in Ici (1 : ℝ), C₀ * rexp (-2 * π * t) * rexp (-π * r * t) := by gcongr
  _ = _ := by
      rw [← smul_eq_mul, ← MeasureTheory.integral_smul (2 : ℝ)]
      congr; ext t
      rw [smul_eq_mul]
      ac_rfl

theorem I₆'_bounding_eq (r : ℝ) : ∃ C₂ > 0,
    ‖I₆' r‖ ≤ C₂ * rexp (-π * (r ^ 2 + 2)) / (r ^ 2 + 2) := by
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := I₆'_bounding r
  use C₁, hC₁_pos
  apply le_of_le_of_eq hC₁
  calc
  _ = ∫ t in Ici (1 : ℝ), C₁ * rexp ((-2 * π - π * r) * t) := by
      congr; ext t
      rw [mul_assoc, sub_mul, sub_eq_add_neg, Real.exp_add]
      simp
  _ = _ := sorry

end Bounding_Integral

end Bounding

----------------------------------------------------------------

section Higher_iteratedFDerivs



end Higher_iteratedFDerivs

----------------------------------------------------------------

noncomputable section Schwartz_Decay

open SchwartzMap

section Zeroth_Derivative

theorem decay'₀ : ∀ (k : ℕ), ∃ C, ∀ (x : ℝ), ‖x‖ ^ k * ‖I₆' x‖ ≤ C := by

  sorry

end Zeroth_Derivative

section Higher_iteratedFDerivs

theorem decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₆' x‖ ≤ C := by

  sorry

end Higher_iteratedFDerivs

-- def I₆'_Schwartz : 𝓢(ℝ, ℂ) where
-- toFun := I₆'
-- smooth' := sorry
-- decay' := by extract_goal; sorry

end Schwartz_Decay

end I₆

end IntegralEstimates

end a

end MagicFunction
