module
public import SpherePacking.MagicFunction.a.Basic
public import SpherePacking.MagicFunction.a.Integrability.RealIntegrands
public import SpherePacking.MagicFunction.a.Schwartz.SmoothI24Common
public import SpherePacking.Integration.UpperHalfPlaneComp

import SpherePacking.MagicFunction.IntegralParametrisationsContinuity

/-!
# Smoothness of `RealIntegrals.I₁'`

This file proves `ContDiff ℝ (⊤ : ℕ∞) RealIntegrals.I₁'` by differentiating under the integral
sign over `Ioo (0, 1)`. The heavy lifting is delegated to
`MagicFunction.a.Schwartz.SmoothI24Common` which handles the common pattern shared with
`SmoothI2`/`SmoothI4`; this file only provides the `I₁'`-specific parametrization
(`z = z₁'`, `shift = 1`, `prefactor = I`) and the geometric facts about its Mobius image.

## Main statement
* `I₁'_contDiff`
-/

namespace MagicFunction.a.Schwartz.I1Smooth

noncomputable section

open scoped Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter intervalIntegral
open MagicFunction.Parametrisations
open MagicFunction.a.RealIntegrals
open MagicFunction.a.RealIntegrands
open MagicFunction.a.ComplexIntegrands
open MagicFunction.a.Schwartz.SmoothI24Common
open SpherePacking.Integration SpherePacking.ForMathlib

private lemma I₁'_eq_integral_g_Ioo (x : ℝ) :
    I₁' x = ∫ t in Ioo (0 : ℝ) 1,
      DifferentiationUnderIntegral.g (coeff := coeff z₁')
        (hf := hf z₁' (1 : ℂ) I) x t := by
  simp [RealIntegrals.I₁', MagicFunction.a.RealIntegrands.Φ₁_def,
    DifferentiationUnderIntegral.g, Φ₁', coeff, hf, SmoothI24Common.arg,
    intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le, integral_Ioc_eq_integral_Ioo,
    mul_assoc, mul_left_comm, mul_comm]

private lemma arg_z₁'_eq_I_div (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    arg z₁' (1 : ℂ) t = I / t := by
  have htne : (t : ℂ) ≠ 0 := mod_cast ht.1.ne'
  change (-1 : ℂ) / (z₁' t + 1) = I / t
  rw [z₁'_eq_of_mem (mem_Icc_of_Ioo ht)]
  field_simp; ring_nf; simp [Complex.I_sq]

private lemma arg_z₁'_im_pos (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < (arg z₁' (1 : ℂ) t).im := by
  simpa [arg_z₁'_eq_I_div (t := t) ht] using one_div_pos.2 ht.1

private lemma arg_z₁'_im_half (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1 / 2 : ℝ) < (arg z₁' (1 : ℂ) t).im := by
  have him : (arg z₁' (1 : ℂ) t).im = 1 / t := by simp [arg_z₁'_eq_I_div (t := t) ht]
  linarith [(one_lt_one_div ht.1) ht.2, him]

private lemma den_z₁'_ne_zero (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    z₁' t + (1 : ℂ) ≠ 0 := fun h0 => by
  have h1 := congrArg Complex.im h0
  simp [z₁'_eq_of_mem (mem_Icc_of_Ioo ht)] at h1; exact ht.1.ne' h1

/-- Smoothness of `RealIntegrals.I₁'` as a function `ℝ → ℂ`. -/
public theorem I₁'_contDiff : ContDiff ℝ (⊤ : ℕ∞) I₁' :=
  contDiff_of_eq_integral_g_Ioo (z := z₁') (shift := (1 : ℂ)) (prefactor := I)
    (f := I₁') I₁'_eq_integral_g_Ioo continuous_z₁' norm_z₁'_le_two (by norm_num)
    den_z₁'_ne_zero arg_z₁'_im_pos arg_z₁'_im_half

end

end MagicFunction.a.Schwartz.I1Smooth
