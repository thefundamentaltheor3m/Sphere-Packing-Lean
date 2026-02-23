/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/
module

import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.Basic
import SpherePacking.MagicFunction.a.IntegralEstimates.BoundingAuxIci
import SpherePacking.Integration.InvChangeOfVariables

/-!
# Bounds for `I₃'`

This file rewrites the auxiliary integral `I₃'` as an integral over `Ici 1` and proves the
exponential bound used in Proposition 7.8 of the blueprint.

## Main definitions
* `g`

## Main statements
* `inv_integrand_eq_integrand`
* `I₃'_bounding`
-/

namespace MagicFunction.a.IntegralEstimates.I₃

open scoped Function UpperHalfPlane Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral

noncomputable section Change_of_Variables

variable (r : ℝ)

/-! We begin by performing changes of variables. We use `Ioc` intervals everywhere because of the
way `intervalIntegral` is defined. -/

section Setup

/-- The integrand on `Ici 1` obtained from `I₃'` after an inversion change of variables. -/
@[expose] public def g : ℝ → ℝ → ℂ := fun r s ↦ -I
  * φ₀'' (I * s)
  * (s ^ (-4 : ℤ))
  * cexp (π * I * r)
  * cexp (-π * r / s)

end Setup

section Change

lemma Changing_Domain_of_Integration (r : ℝ) :
    ∫ s in Ici (1 : ℝ), (g r s) = ∫ (s : ℝ) in f '' (Ioc (0 : ℝ) (1 : ℝ)), (g r s) := by
  congr
  ext x
  constructor <;> intro hx
  · use x⁻¹
    simp only [mem_Ici] at hx ⊢
    constructor
    · refine ⟨by positivity, ?_⟩
      rw [← mul_one x⁻¹, inv_mul_le_one₀ (by positivity)]
      exact hx
    · rw [f, div_inv_eq_mul, one_mul]
  · obtain ⟨y, hy₁, hy₂⟩ := hx
    rw [← hy₂, f]
    simp only [one_div, mem_Ici]
    exact one_le_inv_iff₀.mpr hy₁

lemma Changing_Variables (r : ℝ) : ∫ (s : ℝ) in f '' (Ioc (0 : ℝ) (1 : ℝ)), (g r s) =
    ∫ (t : ℝ) in Ioc 0 1, |f' t| • (g r (f t)) :=
  integral_image_eq_integral_abs_deriv_smul aux_measurable aux_hasDeriv aux_injOn (g r)

lemma Writing_as_intervalIntegral (r : ℝ) :
    ∫ (t : ℝ) in Ioc 0 1, |f' t| • (g r (f t)) = ∫ t in (0 : ℝ)..1, |f' t| • (g r (f t)) := by
  rw [integral_of_le zero_le_one]

lemma Reconciling_Change_of_Variables (r : ℝ) :
    I₃' r = ∫ t in Ioc 0 1, |f' t| • (g r (f t)) := by
  simp only [I₃'_eq_Ioc, f, f', g]
  apply setIntegral_congr_ae₀ nullMeasurableSet_Ioc
  apply ae_of_all
  intro t ht
  obtain ⟨ht₀, ht₁⟩ := ht
  simp only [Int.reduceNeg, zpow_neg, real_smul]
  have h₃ : -1 / (I * t) = I / t := by
    rw [div_mul_eq_div_div_swap, div_I, neg_div, neg_mul, neg_neg, mul_comm, mul_div, mul_one]
  have h₁ : |-1 / t ^ 2| = 1 / t ^ 2 := by simp [neg_div]
  rw [h₁, h₃]
  simp only [neg_mul, ofReal_div, ofReal_one, ofReal_pow, mul_div_assoc', mul_one, div_zpow,
    one_zpow, inv_div, div_one, div_div_eq_mul_div, mul_neg, div_mul_eq_mul_div, one_mul, neg_div']
  rw [eq_div_iff (pow_ne_zero 2 (by exact_mod_cast (ne_of_gt ht₀))), neg_mul, neg_inj]
  ring_nf; ac_rfl

end Change_of_Variables.Change
----------------------------------------------------------------

section Bounding

section Bounding_Integrand

/-- Pointwise bound on `‖g r s‖` on `Ici 1` in terms of `‖φ₀'' (I * s)‖`. -/
public lemma I₃'_bounding_aux_1 (r : ℝ) :
    ∀ x ∈ Ici 1, ‖g r x‖ ≤ ‖φ₀'' (I * ↑x)‖ * rexp (-π * r / x) := by
  intro s hs
  simp only [
    g, neg_mul, Int.reduceNeg, zpow_neg, norm_neg, norm_mul, norm_I, one_mul, norm_inv, norm_zpow,
    norm_real, norm_eq_abs, norm_exp, neg_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, zero_mul, mul_im, add_zero, Real.exp_zero, div_ofReal_re, sub_zero
  ]
  conv_rhs => rw [← mul_one ‖φ₀'' (I * ↑s)‖]
  gcongr
  have hs1 : (1 : ℝ) ≤ s := by simpa [mem_Ici] using hs
  simpa [abs_of_nonneg (zero_le_one.trans hs1)] using
    (inv_le_one_of_one_le₀ (one_le_zpow₀ hs1 <| Int.zero_le_ofNat 4))

end Bounding_Integrand

section Integrability

/-- The model bound integrand is integrable on `Ici 1`. -/
public lemma Bound_integrableOn (r C₀ : ℝ) :
    IntegrableOn (fun s ↦ C₀ * rexp (-2 * π * s) * rexp (-π * r / s)) (Ici 1) volume := by
  set f := fun s : ℝ ↦ C₀ * rexp (-2 * π * s) * rexp (-π * r / s)
  have hcont : ContinuousOn f (Ici 1) := by
    have h1 : ContinuousOn (fun s : ℝ ↦ rexp ((-2 * π) * s)) (Ici 1) :=
      Real.continuous_exp.comp_continuousOn (continuousOn_const.mul continuousOn_id)
    have h2 : ContinuousOn (fun s : ℝ ↦ rexp ((-π * r) * s⁻¹)) (Ici 1) :=
      Real.continuous_exp.comp_continuousOn
        (continuousOn_const.mul (continuousOn_id.inv₀ fun _ hx ↦ (zero_lt_one.trans_le hx).ne'))
    exact (continuousOn_const.mul (h1.mul h2)).congr fun s _ => by
      simp [f, div_eq_mul_inv]
      ring
  have hO : f =O[atTop] fun s ↦ rexp (-(2 * π) * s) := .of_bound (c := |C₀| * rexp (π * |r|)) <| by
    filter_upwards [Filter.Ici_mem_atTop 1] with s hs
    have heb : rexp (-π * r / s) ≤ rexp (π * |r|) :=
      Real.exp_le_exp.mpr <| (le_abs_self _).trans <| by
        simp [abs_div, abs_mul, abs_of_nonneg Real.pi_pos.le]
        exact div_le_self (by positivity) (by rwa [abs_of_nonneg (zero_lt_one.trans_le hs).le])
    simp only [f, Real.norm_eq_abs, Real.abs_exp, abs_mul, mul_comm, mul_left_comm,
      mul_assoc, div_eq_mul_inv]
    calc |C₀| * (rexp (r * (s⁻¹ * -π)) * rexp (s * (π * -2)))
        = |C₀| * rexp ((-2 * π) * s) * rexp (-π * r / s) := by ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left heb (by positivity)
      _ = _ := by ring_nf
  simpa [f, div_eq_mul_inv, neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc] using
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrable_of_isBigO_exp_neg (by positivity) hcont hO)

end Integrability
end Bounding
end I₃

end MagicFunction.a.IntegralEstimates
----------------------------------------------------------------
