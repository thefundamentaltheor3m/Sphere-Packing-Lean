module
public import SpherePacking.MagicFunction.a.Basic
public import SpherePacking.MagicFunction.a.Integrability.RealIntegrands
public import SpherePacking.MagicFunction.a.Schwartz.SmoothI24Common
public import SpherePacking.Integration.UpperHalfPlaneComp

import SpherePacking.MagicFunction.IntegralParametrisationsContinuity

/-!
# Smoothness of `RealIntegrals.I₂'`

This file proves `ContDiff ℝ (⊤ : ℕ∞) RealIntegrals.I₂'` by differentiating under the integral
sign over `Ioo (0, 1)`. The heavy lifting is delegated to
`MagicFunction.a.Schwartz.SmoothI24Common` which handles the common pattern shared with
`SmoothI4`; this file only provides the `I₂'`-specific parametrization (`z = z₂'`) and the
geometric facts about its Mobius image.

## Main statement
* `I₂'_contDiff`
-/

namespace MagicFunction.a.Schwartz.I2Smooth

noncomputable section

open scoped Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter intervalIntegral
open MagicFunction.Parametrisations
open MagicFunction.a.RealIntegrals
open MagicFunction.a.RealIntegrands
open MagicFunction.a.ComplexIntegrands
open MagicFunction.a.Schwartz.SmoothI24Common
open SpherePacking.Integration SpherePacking.ForMathlib

private lemma I₂'_eq_integral_g_Ioo (x : ℝ) :
    I₂' x = ∫ t in Ioo (0 : ℝ) 1,
      DifferentiationUnderIntegral.g (coeff := coeff z₂')
        (hf := hf z₂' (1 : ℂ) (1 : ℂ)) x t := by
  simp [RealIntegrals.I₂', MagicFunction.a.RealIntegrands.Φ₂_def,
    DifferentiationUnderIntegral.g, Φ₂', Φ₁', coeff, hf, SmoothI24Common.arg,
    intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le, integral_Ioc_eq_integral_Ioo,
    mul_assoc, mul_left_comm, mul_comm]

private lemma arg_z₂'_eq_neg_one_div (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    arg z₂' (1 : ℂ) t = (-1 : ℂ) / ((t : ℂ) + I) := by
  change (-1 : ℂ) / (z₂' t + 1) = (-1 : ℂ) / ((t : ℂ) + I)
  simpa [add_left_comm, add_comm, add_assoc] using
    congrArg (fun z : ℂ => (-1 : ℂ) / (z + 1)) (z₂'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht))

private lemma arg_z₂'_im_eq (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (arg z₂' (1 : ℂ) t).im = 1 / (t ^ 2 + 1) := by
  simpa [arg_z₂'_eq_neg_one_div (t := t) ht] using im_neg_one_div_ofReal_add_I (t := t)

private lemma arg_z₂'_im_pos (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < (arg z₂' (1 : ℂ) t).im := by rw [arg_z₂'_im_eq t ht]; positivity

private lemma arg_z₂'_im_half (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1 / 2 : ℝ) < (arg z₂' (1 : ℂ) t).im := by
  simpa [arg_z₂'_im_eq (t := t) ht] using one_half_lt_one_div_sq_add_one_of_mem_Ioo01 ht

private lemma den_z₂'_ne_zero (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    z₂' t + (1 : ℂ) ≠ 0 := fun h0 => by
  simpa [z₂'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht), add_left_comm, add_comm] using
    congrArg Complex.im h0

/-- Smoothness of `RealIntegrals.I₂'` as a function `ℝ → ℂ`. -/
public theorem I₂'_contDiff : ContDiff ℝ (⊤ : ℕ∞) I₂' :=
  contDiff_of_eq_integral_g_Ioo (z := z₂') (shift := (1 : ℂ)) (prefactor := (1 : ℂ))
    (f := I₂') I₂'_eq_integral_g_Ioo continuous_z₂' norm_z₂'_le_two (by norm_num)
    den_z₂'_ne_zero arg_z₂'_im_pos arg_z₂'_im_half

end

end MagicFunction.a.Schwartz.I2Smooth
