module
public import SpherePacking.MagicFunction.a.Basic
public import SpherePacking.MagicFunction.a.Integrability.RealIntegrands
public import SpherePacking.MagicFunction.a.Schwartz.SmoothI24Common
public import SpherePacking.Integration.UpperHalfPlaneComp

import SpherePacking.MagicFunction.IntegralParametrisationsContinuity

/-!
# Smoothness of `RealIntegrals.I₄'`

This file proves `ContDiff ℝ (⊤ : ℕ∞) RealIntegrals.I₄'` by differentiating under the integral
sign over `Ioo (0, 1)`. The heavy lifting is delegated to
`MagicFunction.a.Schwartz.SmoothI24Common` which handles the common pattern shared with
`SmoothI2`; this file only provides the `I₄'`-specific parametrization (`z = z₄'`, `shift = -1`,
`prefactor = -1`) and the geometric facts about its Mobius image.

## Main statement
* `I₄'_contDiff`
-/

namespace MagicFunction.a.Schwartz.I4Smooth

noncomputable section

open scoped Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter intervalIntegral
open MagicFunction.Parametrisations
open MagicFunction.a.RealIntegrals
open MagicFunction.a.RealIntegrands
open MagicFunction.a.ComplexIntegrands
open MagicFunction.a.Schwartz.SmoothI24Common
open SpherePacking.Integration SpherePacking.ForMathlib

private lemma I₄'_eq_integral_g_Ioo (x : ℝ) :
    I₄' x = ∫ t in Ioo (0 : ℝ) 1,
      DifferentiationUnderIntegral.g (coeff := coeff z₄')
        (hf := hf z₄' (-1 : ℂ) (-1 : ℂ)) x t := by
  simp [RealIntegrals.I₄', MagicFunction.a.RealIntegrands.Φ₄_def,
    DifferentiationUnderIntegral.g, Φ₄', Φ₃', coeff, hf, SmoothI24Common.arg,
    sub_eq_add_neg,
    intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le, integral_Ioc_eq_integral_Ioo,
    mul_assoc, mul_left_comm, mul_comm]

private lemma arg_z₄'_eq_neg_one_div (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    arg z₄' (-1 : ℂ) t = (-1 : ℂ) / ((-t : ℂ) + I) := by
  change (-1 : ℂ) / (z₄' t + (-1 : ℂ)) = (-1 : ℂ) / ((-t : ℂ) + I)
  simpa [sub_eq_add_neg, add_left_comm, add_comm, add_assoc] using
    congrArg (fun z : ℂ => (-1 : ℂ) / (z - 1)) (z₄'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht))

private lemma arg_z₄'_im_eq (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (arg z₄' (-1 : ℂ) t).im = 1 / (t ^ 2 + 1) := by
  simpa [arg_z₄'_eq_neg_one_div (t := t) ht] using
    im_neg_one_div_neg_ofReal_add_I (t := t)

private lemma arg_z₄'_im_pos (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < (arg z₄' (-1 : ℂ) t).im := by
  have : 0 < t ^ 2 + 1 := by positivity
  simpa [arg_z₄'_im_eq (t := t) ht] using one_div_pos.2 this

private lemma arg_z₄'_im_half (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1 / 2 : ℝ) < (arg z₄' (-1 : ℂ) t).im := by
  simpa [arg_z₄'_im_eq (t := t) ht] using
    one_half_lt_one_div_sq_add_one_of_mem_Ioo01 ht

private lemma den_z₄'_ne_zero (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    z₄' t + (-1 : ℂ) ≠ 0 := by
  intro h0
  have h0im : ((z₄' t : ℂ) + (-1 : ℂ)).im = 0 := by simpa using congrArg Complex.im h0
  simp [z₄'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht), sub_eq_add_neg, add_comm, add_assoc] at h0im

/-- Smoothness of `RealIntegrals.I₄'` as a function `ℝ → ℂ`. -/
public theorem I₄'_contDiff : ContDiff ℝ (⊤ : ℕ∞) I₄' :=
  contDiff_of_eq_integral_g_Ioo (z := z₄') (shift := (-1 : ℂ)) (prefactor := (-1 : ℂ))
    (f := I₄') I₄'_eq_integral_g_Ioo continuous_z₄' norm_z₄'_le_two (by norm_num)
    den_z₄'_ne_zero arg_z₄'_im_pos arg_z₄'_im_half

end

end MagicFunction.a.Schwartz.I4Smooth
