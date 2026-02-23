module
import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.Basic
public import SpherePacking.MagicFunction.a.Integrability.RealIntegrands
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands

import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.IteratedDeriv
import SpherePacking.Integration.DifferentiationUnderIntegral
import SpherePacking.Integration.UpperHalfPlaneComp
public import SpherePacking.Integration.Measure
import SpherePacking.MagicFunction.IntegralParametrisationsContinuity

/-!
# Smoothness of `RealIntegrals.I₂'`

This file proves `ContDiff ℝ (⊤ : ℕ∞) RealIntegrals.I₂'` by differentiating under the integral sign
over `Ioo (0, 1)`.

## Main statement
* `I₂'_contDiff`
-/

namespace MagicFunction.a.Schwartz.I2Smooth

noncomputable section

open scoped Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter intervalIntegral

open MagicFunction.PolyFourierCoeffBound
open MagicFunction.Parametrisations
open MagicFunction.a.RealIntegrals
open MagicFunction.a.RealIntegrands
open MagicFunction.a.ComplexIntegrands

open SpherePacking.Integration (μIoo01)
open SpherePacking.Integration
open SpherePacking.ForMathlib

def coeff (t : ℝ) : ℂ := ((π : ℂ) * I) * z₂' t

private def arg (t : ℝ) : ℂ := (-1 : ℂ) / ((z₂' t : ℂ) + 1)

def hf (t : ℝ) : ℂ := φ₀'' (arg t) * ((z₂' t : ℂ) + 1) ^ (2 : ℕ)

def g (x t : ℝ) : ℂ :=
  SpherePacking.Integration.DifferentiationUnderIntegral.g (coeff := coeff) (hf := hf) x t

lemma I₂'_eq_integral_g_Ioo (x : ℝ) :
    I₂' x = ∫ t in Ioo (0 : ℝ) 1, g x t := by
  simp [RealIntegrals.I₂', MagicFunction.a.RealIntegrands.Φ₂_def, g, hf, arg, coeff,
    SpherePacking.Integration.DifferentiationUnderIntegral.g, Φ₂', Φ₁',
    intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le, integral_Ioc_eq_integral_Ioo,
    mul_assoc, mul_left_comm, mul_comm]

lemma coeff_norm_le (t : ℝ) : ‖coeff t‖ ≤ 2 * π := by
  simpa [coeff, mul_assoc] using (norm_mul_pi_I_le_two_pi (z := z₂' t) (hz := norm_z₂'_le_two t))

lemma continuous_coeff : Continuous coeff := by
  simpa [coeff, mul_assoc] using (continuous_const.mul continuous_z₂')

private lemma arg_eq_neg_one_div (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    arg t = (-1 : ℂ) / ((t : ℂ) + I) := by
  simpa [arg, add_left_comm, add_comm, add_assoc] using
    congrArg (fun z : ℂ => (-1 : ℂ) / (z + 1)) (z₂'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht))

private lemma arg_im_eq (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (arg t).im = 1 / (t ^ 2 + 1) := by
  simpa [arg_eq_neg_one_div (t := t) ht] using im_neg_one_div_ofReal_add_I (t := t)

private lemma arg_mem_upperHalfPlaneSet (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    arg t ∈ UpperHalfPlane.upperHalfPlaneSet := by
  simpa [UpperHalfPlane.upperHalfPlaneSet, arg_im_eq (t := t) ht] using
    (one_div_pos.2 (by positivity : 0 < t ^ 2 + 1))

lemma continuousOn_hf : ContinuousOn hf (Ioo (0 : ℝ) 1) := by
  have hden : ∀ t ∈ Ioo (0 : ℝ) 1, ((z₂' t : ℂ) + 1) ≠ 0 := by
    intro t ht h0
    have h0im : ((z₂' t : ℂ) + 1).im = 0 := by simpa using congrArg Complex.im h0
    simp [z₂'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht), add_left_comm, add_comm] at h0im
  have harg : ContinuousOn arg (Ioo (0 : ℝ) 1) := by
    refine (continuousOn_const.div ?_ hden)
    simpa using (continuous_z₂'.continuousOn.add continuousOn_const)
  have hpow : ContinuousOn (fun t : ℝ => ((z₂' t : ℂ) + 1) ^ (2 : ℕ)) (Ioo (0 : ℝ) 1) := by
    simpa using (Continuous.continuousOn ((continuous_z₂'.add continuous_const).pow 2))
  have hφ : ContinuousOn φ₀'' UpperHalfPlane.upperHalfPlaneSet :=
    (MagicFunction.a.ComplexIntegrands.φ₀''_holo).continuousOn
  have hφcomp : ContinuousOn (fun t : ℝ => φ₀'' (arg t)) (Ioo (0 : ℝ) 1) := by
    refine hφ.comp harg ?_
    intro t ht
    exact arg_mem_upperHalfPlaneSet (t := t) ht
  simpa [hf, mul_assoc] using hφcomp.mul hpow

lemma exists_bound_norm_hf : ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖hf t‖ ≤ M := by
  rcases norm_φ₀_le with ⟨C₀, hC₀_pos, hC₀⟩
  refine ⟨C₀ * rexp (-π) * ((3 : ℝ) ^ (2 : ℕ)), ?_⟩
  intro t ht
  have hpos : 0 < (arg t).im := by
    have hden : 0 < t ^ 2 + 1 := by positivity
    simpa [arg_im_eq (t := t) ht] using (one_div_pos.2 hden)
  let z : ℍ := ⟨arg t, hpos⟩
  have hz_half : (1 / 2 : ℝ) < z.im := by
    simpa [z, UpperHalfPlane.im, arg_im_eq (t := t) ht] using
      (SpherePacking.Integration.one_half_lt_one_div_sq_add_one_of_mem_Ioo01 ht)
  have hφle : ‖φ₀'' (arg t)‖ ≤ C₀ * rexp (-π) := by
    simpa [z] using
      (norm_φ₀''_le_mul_exp_neg_pi_of_one_half_lt_im (C₀ := C₀) (hC₀_pos := hC₀_pos)
        (hC₀ := hC₀) (z := z) hz_half)
  have hpow : ‖((z₂' t : ℂ) + 1) ^ (2 : ℕ)‖ ≤ (3 : ℝ) ^ (2 : ℕ) := by
    have hz : ‖z₂' t‖ ≤ 2 := norm_z₂'_le_two t
    have hnorm : ‖(z₂' t : ℂ) + 1‖ ≤ 3 := by
      calc
        ‖(z₂' t : ℂ) + 1‖ ≤ ‖z₂' t‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ 2 + 1 := by
              refine add_le_add hz ?_
              simp
        _ = 3 := by ring
    simpa [norm_pow] using (pow_le_pow_left₀ (norm_nonneg _) hnorm 2)
  calc
    ‖hf t‖ = ‖φ₀'' (arg t)‖ * ‖((z₂' t : ℂ) + 1) ^ (2 : ℕ)‖ := by
      simp [hf]
    _ ≤ (C₀ * rexp (-π)) * ((3 : ℝ) ^ (2 : ℕ)) := by gcongr
    _ = C₀ * rexp (-π) * ((3 : ℝ) ^ (2 : ℕ)) := by simp [mul_assoc]

/-- Smoothness of `RealIntegrals.I₂'` as a function `ℝ → ℂ`. -/
public theorem I₂'_contDiff : ContDiff ℝ (⊤ : ℕ∞) I₂' := by
  refine DifferentiationUnderIntegral.contDiff_of_eq_integral_g_Ioo (coeff := coeff) (hf := hf) I₂'
    (fun x => by simpa [g] using I₂'_eq_integral_g_Ioo (x := x))
    continuousOn_hf continuous_coeff exists_bound_norm_hf coeff_norm_le

end

end MagicFunction.a.Schwartz.I2Smooth
