/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/
module


public import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.Basic

@[expose] public section

/-! # Constructing Upper-Bounds for I₅

The purpose of this file is to construct bounds on the integral `I₅` that is part of the definition
of the function `a`. We follow the proof of Proposition 7.8 in the blueprint.

## TODO:
- Integrability of `g` and `C₀ * rexp (-2 * π * s) * rexp (-π * r / s)`
-/

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals
  MagicFunction.a.RadialFunctions MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open scoped Function UpperHalfPlane

namespace MagicFunction.a.IntegralEstimates.I₅

noncomputable section Change_of_Variables

variable (r : ℝ)

/-! We begin by performing changes of variables. We use `Ioc` intervals everywhere because of the
way `intervalIntegral` is defined. -/

-- Change of variable result is based on
-- #check intervalIntegral.integral_comp_smul_deriv

-- Interval integrals can be reconciled with `Ioc` integrals using
-- #check intervalIntegral_eq_integral_uIoc
-- taking advantage of the fact that we have the following:
-- example : uIoc 0 1 = Ioc 0 1 := rfl

section Setup

def f : ℝ → ℝ := fun t ↦ 1 / t

def f' : ℝ → ℝ := fun t ↦ -1 / t ^ 2

def g : ℝ → ℝ → ℂ := fun r s ↦ -I
  * φ₀'' (I * s)
  * (s ^ (-4 : ℤ))
  * cexp (-π * r / s)

lemma aux_measurable : MeasurableSet ((Ioc 0 1) : Set ℝ) := measurableSet_Ioc

lemma aux_hasDeriv (x : ℝ) (hx : x ∈ Ioc 0 1) : HasDerivWithinAt f (f' x) (Ioc 0 1) x := by
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
  exact hasDerivWithinAt_zpow (-1 : ℤ) x (Or.inl (ne_of_gt hx.1)) (Ioc 0 1)

lemma aux_injOn : InjOn f (Ioc 0 1) := by
  intro _ _ _ _ hf
  simp only [f, div_eq_mul_inv, one_mul, inv_inj] at hf
  exact hf

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
  simp [intervalIntegral_eq_integral_uIoc]

lemma Reconciling_Change_of_Variables (r : ℝ) :
    I₅' r = -2 * ∫ t in Ioc 0 1, |f' t| • (g r (f t)) := by
  simp only [I₅'_eq_Ioc, f, f', g]
  congr 1
  apply setIntegral_congr_ae₀ nullMeasurableSet_Ioc
  apply ae_of_all
  intro t ht
  obtain ⟨ht₀, ht₁⟩ := ht
  simp only [Int.reduceNeg, zpow_neg, real_smul]
  have h₁ : |-1 / t ^ 2| = 1 / t ^ 2 := by rw [neg_div, abs_neg, abs_of_nonneg (by positivity)]
  have h₃ : -1 / (I * t) = I / t := by
    rw [div_mul_eq_div_div_swap, div_I, neg_div, neg_mul, neg_neg, mul_comm, mul_div, mul_one]
  have ht₀' : (t : ℂ) ^ 2 ≠ 0 := by
    norm_cast
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
    exact ne_of_gt ht₀
  rw [h₁, h₃]
  simp only [neg_mul, ofReal_div, ofReal_one, ofReal_pow, mul_div_assoc', mul_one, div_zpow,
    one_zpow, inv_div, div_one, div_div_eq_mul_div, mul_neg, div_mul_eq_mul_div, one_mul, neg_div']
  rw [eq_div_iff ht₀', neg_mul, neg_inj]
  ring_nf
  ac_rfl

theorem Complete_Change_of_Variables (r : ℝ) : I₅' r = -2 * ∫ s in Ici (1 : ℝ), (g r s) := by
  rw [Reconciling_Change_of_Variables, ← Changing_Variables, ← Changing_Domain_of_Integration]

end Change

end Change_of_Variables

----------------------------------------------------------------

section Bounding

section Bounding_Integrand

lemma I₅'_bounding_aux_1 (r : ℝ) : ∀ x ∈ Ici 1, ‖g r x‖ ≤ ‖φ₀'' (I * ↑x)‖ * rexp (-π * r / x) := by
  intro s hs
  rw [mem_Ici] at hs
  simp only [g, neg_mul, Int.reduceNeg, zpow_neg, norm_neg, norm_mul, norm_I, one_mul, norm_inv,
    norm_zpow, norm_real, norm_eq_abs, norm_exp, neg_re, mul_re, ofReal_re, mul_zero,
    ofReal_im, div_ofReal_re, sub_zero]
  conv_rhs => rw [← mul_one ‖φ₀'' (I * ↑s)‖]
  gcongr
  rw [abs_of_nonneg (zero_le_one.trans hs)]
  apply inv_le_one_of_one_le₀
  exact one_le_zpow₀ hs <| Int.zero_le_ofNat 4

lemma I₅'_bounding_aux_2 (r : ℝ) : ∃ C₀ > 0, ∀ x ∈ Ici 1,
    ‖g r x‖ ≤ C₀ * rexp (-2 * π * x) * rexp (-π * r / x) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀_le -- The `PolyFourierCoeffBound` of `φ₀`
  use C₀, hC₀_pos
  intro s hs
  rw [mem_Ici] at hs
  apply (I₅'_bounding_aux_1 r s hs).trans
  gcongr
  have him : (I * s).im = s := by simp
  have hpos : 0 < s := by positivity
  have hpos' : 0 < (I * ↑s).im := by rw [him]; exact hpos
  let z : ℍ := ⟨I * s, hpos'⟩
  have him' : z.im = s := by simp [z, him, UpperHalfPlane.im]
  have him'_gt_half : 1 / 2 < z.im := by rw [him']; linarith
  specialize hC₀ z him'_gt_half
  simp only [z, him'] at hC₀
  simp only [φ₀'', mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul, zero_add, hpos,
    ↓reduceDIte]
  exact hC₀

end Bounding_Integrand

section Integrability

lemma Bound_integrableOn (r C₀ : ℝ) :
    IntegrableOn (fun s ↦ C₀ * rexp (-2 * π * s) * rexp (-π * r / s)) (Ici 1) volume := by
  have h_exp : IntegrableOn (fun s => rexp ((-2 * π) * s)) (Ici 1) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr <| by
      simpa [mul_comm] using integrableOn_exp_mul_Ioi (by linarith [Real.pi_pos] : -2 * π < 0) 1
  have h_bnd : ∀ᵐ s ∂volume.restrict (Ici (1:ℝ)), ‖rexp (-π * r / s)‖ ≤ rexp (π * |r|) := by
    rw [ae_restrict_iff' measurableSet_Ici]; refine .of_forall fun s (hs : 1 ≤ s) ↦ ?_
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]; apply Real.exp_le_exp.mpr
    calc -π * r / s ≤ |-(π * r) / s| := by simpa [neg_mul] using le_abs_self _
      _ = (π * |r|) / s := by simp [abs_div, abs_neg, abs_mul, abs_of_nonneg Real.pi_pos.le,
                                abs_of_nonneg (zero_le_one.trans hs)]
      _ ≤ _ := div_le_self (mul_nonneg Real.pi_pos.le (abs_nonneg _)) hs
  simpa [IntegrableOn, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using
    (h_exp.const_mul C₀).bdd_mul (Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_id.inv)).aestronglyMeasurable h_bnd

end Integrability

section Bounding_Integral

lemma I₅'_bounding_1_aux_3 (r : ℝ) : ∃ C₀ > 0, ∫ (s : ℝ) in Ici 1, ‖g r s‖ ≤
    ∫ (s : ℝ) in Ici 1, C₀ * rexp (-2 * π * s) * rexp (-π * r / s) := by
  wlog hint : IntegrableOn (fun t ↦ ‖g r t‖) (Ici (1 : ℝ)) volume
  · refine ⟨1, by positivity, ?_⟩
    haveI h₁ : CompleteSpace ℝ := inferInstance
    have h₂ : ¬ (Integrable (fun t ↦ ‖g r t‖) (volume.restrict (Ici 1))) := hint
    conv_lhs => simp only [integral, h₁, h₂, ↓reduceDIte]
    positivity
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := I₅'_bounding_aux_2 r
  use C₀, hC₀_pos
  exact setIntegral_mono_on hint (Bound_integrableOn r C₀) measurableSet_Ici hC₀

theorem I₅'_bounding (r : ℝ) : ∃ C₀ > 0,
    ‖I₅' r‖ ≤ 2 * ∫ s in Ici (1 : ℝ), C₀ * rexp (-2 * π * s) * rexp (-π * r / s) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := I₅'_bounding_1_aux_3 r
  use C₀, hC₀_pos
  calc
  _ = ‖-2 * ∫ s in Ici (1 : ℝ), g r s‖ := by simp only [Complete_Change_of_Variables, g]
  _ ≤ 2 * ∫ s in Ici (1 : ℝ), ‖g r s‖ := by
      simp only [norm_mul, norm_neg, Complex.norm_ofNat, Nat.ofNat_pos, mul_le_mul_iff_right₀]
      exact norm_integral_le_integral_norm (g r)
  _ ≤ 2 * ∫ s in Ici (1 : ℝ), C₀ * rexp (-2 * π * s) * rexp (-π * r / s) := by gcongr

-- The following may be useful:
-- #check MeasureTheory.integral_mono_of_nonneg -- integrability can't be avoided...
-- #check MeasureTheory.setLIntegral_mono
-- #check MeasureTheory.setIntegral_mono_on

end Bounding_Integral

end Bounding

end I₅

end IntegralEstimates

end a

end MagicFunction

----------------------------------------------------------------
