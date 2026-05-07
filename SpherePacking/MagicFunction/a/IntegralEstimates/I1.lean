/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/
module

public import SpherePacking.MagicFunction.a.Basic
import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.MagicFunction.a.IntegralEstimates.BoundingAuxIci
import SpherePacking.MagicFunction.a.IntegralEstimates.I3
import SpherePacking.Integration.InvChangeOfVariables

/-!
# Bounds for `I₁'`

This file rewrites the auxiliary integral `I₁'` as an integral over `Ici 1` and proves the bound
used in Proposition 7.8 of the blueprint.

## Main definitions
* `g`

## Main statements
* `Complete_Change_of_Variables`
* `I₁'_bounding`
-/

namespace MagicFunction.a.IntegralEstimates.I₁

open scoped Function UpperHalfPlane Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral

noncomputable section

variable (r : ℝ)

/-- The integrand on `Ici 1` obtained from `I₁'` after an inversion change of variables. -/
@[expose] public def g : ℝ → ℝ → ℂ := fun r s ↦
  -I * φ₀'' (I * s) * (s ^ (-4 : ℤ)) * cexp (-π * I * r) * cexp (-π * r / s)

lemma Reconciling_Change_of_Variables (r : ℝ) :
    I₁' r = ∫ t in Ioc 0 1, |(-1 / t ^ 2)| • (g r (1 / t)) := by
  simp only [I₁'_eq_Ioc, g]
  refine setIntegral_congr_ae₀ nullMeasurableSet_Ioc (ae_of_all _ fun t ht => ?_)
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (MagicFunction.a.IntegralEstimates.I₃.inv_integrand_eq_integrand (t := t) ht.1 r
      (cexp (-π * I * r)))

/-- Rewrite `I₁' r` as an integral of `g r` over `Ici 1`. -/
public theorem Complete_Change_of_Variables (r : ℝ) :
    I₁' r = ∫ s in Ici (1 : ℝ), (g r s) :=
  (Reconciling_Change_of_Variables (r := r)).trans <| by
    simpa using
      (SpherePacking.Integration.InvChangeOfVariables.integral_Ici_one_eq_integral_abs_deriv_smul
        (g := g r)).symm

lemma I₁'_bounding_aux_1 (r : ℝ) : ∀ x ∈ Ici 1, ‖g r x‖ ≤ ‖φ₀'' (I * ↑x)‖ * rexp (-π * r / x) := by
  intro s (hs : (1 : ℝ) ≤ s)
  simp only [g, neg_mul, Int.reduceNeg, zpow_neg, norm_neg, norm_mul, norm_I, one_mul, norm_inv,
    norm_zpow, norm_real, norm_eq_abs, norm_exp, neg_re, mul_re, ofReal_re, I_re, mul_zero,
    ofReal_im, I_im, mul_one, _root_.sub_self, zero_mul, mul_im, add_zero, neg_zero,
    Real.exp_zero, div_ofReal_re, sub_zero]
  conv_rhs => rw [← mul_one ‖φ₀'' (I * ↑s)‖]
  gcongr
  rw [abs_of_nonneg (zero_le_one.trans hs)]
  exact inv_le_one_of_one_le₀ (one_le_zpow₀ hs <| Int.zero_le_ofNat 4)

lemma I₁'_bounding_aux_2 (r : ℝ) : ∃ C₀ > 0, ∀ x ∈ Ici 1,
    ‖g r x‖ ≤ C₀ * rexp (-2 * π * x) * rexp (-π * r / x) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀_le
  refine ⟨C₀, hC₀_pos, fun s (hs : (1 : ℝ) ≤ s) => (I₁'_bounding_aux_1 r s hs).trans ?_⟩
  have hs_pos : 0 < s := by positivity
  gcongr
  let z : ℍ := ⟨I * s, by simpa using hs_pos⟩
  have him' : z.im = s := by simp [z, UpperHalfPlane.im]
  have hC₀z := hC₀ z (him'.symm ▸ by linarith)
  simpa [z, him', φ₀'', mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul, zero_add,
    hs_pos] using hC₀z

lemma I₁'_bounding_1_aux_3 (r : ℝ) : ∃ C₀ > 0, ∫ (s : ℝ) in Ici 1, ‖g r s‖ ≤
    ∫ (s : ℝ) in Ici 1, C₀ * rexp (-2 * π * s) * rexp (-π * r / s) := by
  wlog hint : IntegrableOn (fun t ↦ ‖g r t‖) (Ici (1 : ℝ)) volume
  · exact ⟨1, by positivity, by
      simpa [MeasureTheory.integral_undef (μ := volume.restrict (Ici (1 : ℝ)))
        (f := fun t ↦ ‖g r t‖) (by simpa [IntegrableOn] using hint)] using
        (by positivity : (0 : ℝ) ≤
          ∫ (s : ℝ) in Ici 1, (1 : ℝ) * rexp (-2 * π * s) * rexp (-π * r / s))⟩
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := I₁'_bounding_aux_2 r
  exact ⟨C₀, hC₀_pos, setIntegral_mono_on hint (bound_integrableOn_Ici r C₀) measurableSet_Ici hC₀⟩

theorem I₁'_bounding (r : ℝ) : ∃ C₀ > 0,
    ‖I₁' r‖ ≤ ∫ s in Ici (1 : ℝ), C₀ * rexp (-2 * π * s) * rexp (-π * r / s) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := I₁'_bounding_1_aux_3 r
  refine ⟨C₀, hC₀_pos, ?_⟩
  rw [Complete_Change_of_Variables]
  exact (norm_integral_le_integral_norm (g r)).trans hC₀

end

end MagicFunction.a.IntegralEstimates.I₁
