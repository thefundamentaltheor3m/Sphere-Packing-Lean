/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.a.Basic

import SpherePacking.MagicFunction.PolyFourierCoeffBound

/-!
# Constructing Upper-Bounds for I₆

The purpose of this file is to construct bounds on the integral `I₆` that is part of the definition
of the function `a`. We follow the proof of Proposition 7.8 in the blueprint.

## TODO:
- Integrability of `g` and `C₀ * rexp (-2 * π * u) * rexp (-π * s / u)`
-/

@[expose] public section

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals
  MagicFunction.a.RadialFunctions MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open scoped Function UpperHalfPlane

namespace MagicFunction.a.IntegralEstimates.I₆

variable (s : ℝ)

section Setup

noncomputable def g : ℝ → ℝ → ℂ := fun s t ↦ I
  * φ₀'' (I * t)
  * cexp (-π * s * t)

lemma I₆'_eq_integral_g_Ioo (s : ℝ) : I₆' s = 2 * ∫ t in Ici (1 : ℝ), g s t := by simp [I₆'_eq, g]

end Setup

----------------------------------------------------------------

section Bounding

section Bounding_Integrand

lemma I₆'_bounding_aux_1 (s : ℝ) : ∀ t ∈ Ici 1, ‖g s t‖ = ‖φ₀'' (I * t)‖ * rexp (-π * s * t) := by
  simp [g, neg_mul, norm_I, one_mul, norm_exp]

lemma I₆'_bounding_aux_2 (s : ℝ) : ∃ C₀ > 0, ∀ t ∈ Ici (1 : ℝ),
    ‖g s t‖ ≤ C₀ * rexp (-2 * π * t) * rexp (-π * s * t) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀_le -- The `PolyFourierCoeffBound` of `φ₀`
  use C₀, hC₀_pos
  intro t ht
  rw [I₆'_bounding_aux_1 s t ht]
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

lemma Bound_integrableOn (s C₀ : ℝ) (hs : 0 ≤ s) :
  IntegrableOn (fun t ↦ C₀ * rexp (-2 * π * t) * rexp (-π * s * t)) (Ici (1 : ℝ)) volume := by
  have hb_pos : 0 < π * (s + 2) := mul_pos Real.pi_pos (by linarith)
  have h0 : IntegrableOn (fun t : ℝ => rexp (-(π * (s + 2)) * t)) (Ioi (1 : ℝ)) := by
    simpa using exp_neg_integrableOn_Ioi (a := (1 : ℝ)) (b := π * (s + 2)) hb_pos
  have h1 : IntegrableOn (fun t : ℝ => C₀ * rexp (-(π * (s + 2)) * t)) (Ioi (1 : ℝ)) :=
    h0.const_mul C₀
  have h_eq (t : ℝ) :
      C₀ * rexp (-(π * (s + 2)) * t) =
        C₀ * rexp (-2 * π * t) * rexp (-π * s * t) := by
    have ht : -(π * (s + 2)) * t = (-2 * π * t) + (-π * s * t) := by ring_nf
    simp [ht, Real.exp_add, mul_comm, mul_left_comm]
  have h2 : IntegrableOn (fun t : ℝ => C₀ * rexp (-2 * π * t) * rexp (-π * s * t))
        (Ioi (1 : ℝ)) volume := by
    refine h1.congr_fun ?_ measurableSet_Ioi
    intro t _
    exact h_eq t
  exact
    (integrableOn_Ici_iff_integrableOn_Ioi
        (μ := (volume : Measure ℝ))
        (f := fun t : ℝ => C₀ * rexp (-2 * π * t) * rexp (-π * s * t))
        (b := (1 : ℝ))).2
      h2

end Integrability

section Bounding_Integral

lemma I₆'_bounding_aux_3 (s : ℝ) (hs : 0 ≤ s) : ∃ C₀ > 0,
    ∫ t in Ici (1 : ℝ), ‖g s t‖ ≤
    ∫ t in Ici (1 : ℝ), C₀ * rexp (-2 * π * t) * rexp (-π * s * t) := by
  wlog hint : IntegrableOn (fun t ↦ ‖g s t‖) (Ici (1 : ℝ)) volume
  · refine ⟨1, by positivity, ?_⟩
    have h₂ : ¬ (Integrable (fun t ↦ ‖g s t‖) (volume.restrict (Ici 1))) := hint
    rw [integral_undef h₂]
    positivity
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := I₆'_bounding_aux_2 s
  use C₀, hC₀_pos
  exact setIntegral_mono_on hint (Bound_integrableOn s C₀ hs) measurableSet_Ici hC₀

theorem I₆'_bounding (s : ℝ) (hs : 0 ≤ s) : ∃ C₁ > 0,
    ‖I₆' s‖ ≤ ∫ t in Ici (1 : ℝ), C₁ * rexp (-2 * π * t) * rexp (-π * s * t) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := I₆'_bounding_aux_3 s hs
  refine ⟨2 * C₀, by positivity, ?_⟩
  calc
  _ = ‖2 * ∫ t in Ici (1 : ℝ), g s t‖ := by simp only [I₆'_eq_integral_g_Ioo, g]
  _ ≤ 2 * ∫ t in Ici (1 : ℝ), ‖g s t‖ := by
      simp only [norm_mul, Complex.norm_ofNat, Nat.ofNat_pos, mul_le_mul_iff_right₀]
      exact norm_integral_le_integral_norm (g s)
  _ ≤ 2 * ∫ t in Ici (1 : ℝ), C₀ * rexp (-2 * π * t) * rexp (-π * s * t) := by gcongr
  _ = _ := by
      rw [← smul_eq_mul, ← MeasureTheory.integral_smul (2 : ℝ)]
      congr; ext t
      rw [smul_eq_mul]
      ac_rfl

theorem I₆'_bounding_eq (s : ℝ) (hs : 0 ≤ s) : ∃ C₂ > 0,
    ‖I₆' s‖ ≤ C₂ * rexp (-π * (s ^ 2 + 2)) / (s ^ 2 + 2) :=
by
  obtain ⟨C₁, _, hC₁⟩ := I₆'_bounding s hs
  let A : ℝ := ∫ t in Ici (1 : ℝ), C₁ * rexp (-2 * π * t) * rexp (-π * s * t)
  let K : ℝ := rexp (-π * (s ^ 2 + 2)) / (s ^ 2 + 2)
  have hKpos : 0 < K := by
    have hden : 0 < s ^ 2 + 2 := by
      have : 0 ≤ s ^ 2 := by simpa using sq_nonneg s
      linarith
    simpa [K] using div_pos (Real.exp_pos _) hden
  refine ⟨|A| / K + 1, add_pos_of_nonneg_of_pos (div_nonneg (abs_nonneg _) hKpos.le) one_pos, ?_⟩
  have h : ‖I₆' s‖ ≤ (|A| / K + 1) * K := by
    have hKne : K ≠ 0 := ne_of_gt hKpos
    calc
      ‖I₆' s‖ ≤ A := hC₁
      _ ≤ |A| + K := (le_abs_self A).trans (le_add_of_nonneg_right hKpos.le)
      _ = (|A| / K + 1) * K := by
        have h1 : (|A| / K) * K = |A| := by field_simp [div_eq_mul_inv, hKne]
        have h2 : (|A| / K + 1) * K = (|A| / K) * K + 1 * K := by ring
        simp [h2, h1]
  simpa [K, A, mul_div_assoc] using h

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
