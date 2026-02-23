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

noncomputable section Change_of_Variables

variable (r : ℝ)

/-! We begin by performing changes of variables. We use `Ioc` intervals everywhere because of the
way `intervalIntegral` is defined. -/

section Setup

def f : ℝ → ℝ := fun t ↦ 1 / t

def f' : ℝ → ℝ := fun t ↦ -1 / t ^ 2

/-- The integrand on `Ici 1` obtained from `I₁'` after an inversion change of variables. -/
@[expose] public def g : ℝ → ℝ → ℂ := fun r s ↦ -I
  * φ₀'' (I * s)
  * (s ^ (-4 : ℤ))
  * cexp (-π * I * r)
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
    I₁' r = ∫ t in Ioc 0 1, |(-1 / t ^ 2)| • (g r (1 / t)) := by
  simp only [I₁'_eq_Ioc, g]
  refine setIntegral_congr_ae₀ nullMeasurableSet_Ioc (ae_of_all _ fun t ht => ?_)
  -- shared algebraic reconciliation lemma (also used in `I₃`/`I₅`)
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (MagicFunction.a.IntegralEstimates.I₃.inv_integrand_eq_integrand (t := t) ht.1 r
      (cexp (-π * I * r)))

/-- Rewrite `I₁' r` as an integral of `g r` over `Ici 1`. -/
public theorem Complete_Change_of_Variables (r : ℝ) :
    I₁' r = ∫ s in Ici (1 : ℝ), (g r s) := by
  refine (Reconciling_Change_of_Variables (r := r)).trans ?_
  simpa using
    (SpherePacking.Integration.InvChangeOfVariables.integral_Ici_one_eq_integral_abs_deriv_smul
      (g := g r)).symm

end Change_of_Variables.Change

----------------------------------------------------------------

section Bounding

section Bounding_Integrand

lemma I₁'_bounding_aux_1 (r : ℝ) : ∀ x ∈ Ici 1, ‖g r x‖ ≤ ‖φ₀'' (I * ↑x)‖ * rexp (-π * r / x) := by
  intro s hs
  rw [mem_Ici] at hs
  simp only [g, neg_mul, Int.reduceNeg, zpow_neg, norm_neg, norm_mul, norm_I, one_mul, norm_inv,
    norm_zpow, norm_real, norm_eq_abs, norm_exp, neg_re, mul_re, ofReal_re, I_re, mul_zero,
    ofReal_im, I_im, mul_one, _root_.sub_self, zero_mul, mul_im, add_zero, neg_zero,
    Real.exp_zero, div_ofReal_re, sub_zero]
  conv_rhs => rw [← mul_one ‖φ₀'' (I * ↑s)‖]
  gcongr
  rw [abs_of_nonneg (zero_le_one.trans hs)]
  apply inv_le_one_of_one_le₀
  exact one_le_zpow₀ hs <| Int.zero_le_ofNat 4

lemma I₁'_bounding_aux_2 (r : ℝ) : ∃ C₀ > 0, ∀ x ∈ Ici 1,
    ‖g r x‖ ≤ C₀ * rexp (-2 * π * x) * rexp (-π * r / x) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀_le -- The `PolyFourierCoeffBound` of `φ₀`
  use C₀, hC₀_pos
  intro s hs
  rw [mem_Ici] at hs
  apply (I₁'_bounding_aux_1 r s hs).trans
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
  set μ := volume.restrict (Ici (1 : ℝ))
  have h_g : Integrable (fun s ↦ C₀ * rexp (-2 * π * s)) μ :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_exp_mul_Ioi (by linarith [pi_pos]) 1)).const_mul C₀
  have hφ : AEStronglyMeasurable (fun s ↦ rexp (-π * r / s)) μ :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_inv)).aestronglyMeasurable
  have hb : ∀ᵐ s ∂μ, ‖rexp (-π * r / s)‖ ≤ rexp (π * |r|) :=
    (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s (hs : 1 ≤ s) ↦ by
      simp only [Real.norm_eq_abs, abs_of_nonneg (exp_pos _).le]
      refine exp_le_exp.mpr <| (le_abs_self _).trans ?_
      rw [abs_div, abs_mul, abs_neg, abs_of_nonneg pi_pos.le, abs_of_nonneg (by linarith : 0 ≤ s)]
      exact div_le_self (by positivity) hs
  simpa [mul_comm] using h_g.bdd_mul hφ hb

end Integrability

section Bounding_Integral

lemma I₁'_bounding_1_aux_3 (r : ℝ) : ∃ C₀ > 0, ∫ (s : ℝ) in Ici 1, ‖g r s‖ ≤
    ∫ (s : ℝ) in Ici 1, C₀ * rexp (-2 * π * s) * rexp (-π * r / s) := by
  wlog hint : IntegrableOn (fun t ↦ ‖g r t‖) (Ici (1 : ℝ)) volume
  · refine ⟨1, by positivity, ?_⟩
    haveI h₁ : CompleteSpace ℝ := inferInstance
    have h₂ : ¬ (Integrable (fun t ↦ ‖g r t‖) (volume.restrict (Ici 1))) := hint
    conv_lhs => simp only [integral, h₁, h₂, ↓reduceDIte]
    positivity
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := I₁'_bounding_aux_2 r
  use C₀, hC₀_pos
  exact setIntegral_mono_on hint (Bound_integrableOn r C₀) measurableSet_Ici hC₀

theorem I₁'_bounding (r : ℝ) : ∃ C₀ > 0,
    ‖I₁' r‖ ≤ ∫ s in Ici (1 : ℝ), C₀ * rexp (-2 * π * s) * rexp (-π * r / s) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := I₁'_bounding_1_aux_3 r
  use C₀, hC₀_pos
  calc
  _ = ‖∫ s in Ici (1 : ℝ), g r s‖ := by simp only [Complete_Change_of_Variables, g]
  _ ≤ ∫ s in Ici (1 : ℝ), ‖g r s‖ := norm_integral_le_integral_norm (g r)
  _ ≤ ∫ s in Ici (1 : ℝ), C₀ * rexp (-2 * π * s) * rexp (-π * r / s) := hC₀

-- The following may be useful:
-- #check MeasureTheory.integral_mono_of_nonneg -- integrability can't be avoided...
-- #check MeasureTheory.setLIntegral_mono
-- #check MeasureTheory.setIntegral_mono_on

end Bounding_Integral

end Bounding

end I₁

end MagicFunction.a.IntegralEstimates
----------------------------------------------------------------
