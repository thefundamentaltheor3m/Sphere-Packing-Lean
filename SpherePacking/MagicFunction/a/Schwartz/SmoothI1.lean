module
import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.Basic
public import SpherePacking.MagicFunction.a.Integrability.RealIntegrands
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands

import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.IteratedDeriv
import SpherePacking.Integration.DifferentiationUnderIntegral
public import SpherePacking.Integration.Measure
import SpherePacking.MagicFunction.IntegralParametrisationsContinuity

/-!
# Smoothness of `RealIntegrals.I₁'`

This file proves `ContDiff ℝ (⊤ : ℕ∞) RealIntegrals.I₁'` by differentiating under the integral sign
over `Ioo (0, 1)`.

## Main statement
* `I₁'_contDiff`
-/

namespace MagicFunction.a.Schwartz.I1Smooth

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

def coeff (t : ℝ) : ℂ := ((π : ℂ) * I) * z₁' t

private def arg (t : ℝ) : ℂ := (-1 : ℂ) / ((z₁' t : ℂ) + 1)

def hf (t : ℝ) : ℂ := (Complex.I : ℂ) * (φ₀'' (arg t) * ((z₁' t : ℂ) + 1) ^ (2 : ℕ))

def g (x t : ℝ) : ℂ :=
  SpherePacking.Integration.DifferentiationUnderIntegral.g (coeff := coeff) (hf := hf) x t

lemma I₁'_eq_integral_g_Ioo (x : ℝ) :
    I₁' x = ∫ t in Ioo (0 : ℝ) 1, g x t := by
  -- Replace the interval integral over `Ioc` by the integral over `Ioo`.
  -- The endpoints have measure zero.
  simp [RealIntegrals.I₁', MagicFunction.a.RealIntegrands.Φ₁_def, g, hf, arg, coeff,
    SpherePacking.Integration.DifferentiationUnderIntegral.g, MagicFunction.a.ComplexIntegrands.Φ₁',
    intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le, integral_Ioc_eq_integral_Ioo,
    mul_assoc, mul_left_comm, mul_comm]

lemma coeff_norm_le (t : ℝ) : ‖coeff t‖ ≤ 2 * π := by
  simpa [coeff, mul_assoc] using (norm_mul_pi_I_le_two_pi (z := z₁' t) (hz := norm_z₁'_le_two t))

lemma continuous_coeff : Continuous coeff := by
  simpa [coeff, mul_assoc] using (continuous_const.mul continuous_z₁')

private lemma arg_eq_I_div (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : arg t = (Complex.I : ℂ) / t := by
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht.1)
  have hz_add : (z₁' t : ℂ) + 1 = I * (t : ℂ) := by
    simpa [add_left_comm, add_comm, add_assoc] using
      congrArg (fun z : ℂ => z + 1) (z₁'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht))
  simp [arg, hz_add]
  field_simp [Complex.I_ne_zero, htne]
  simp [Complex.I_sq]

private lemma arg_mem_upperHalfPlaneSet (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    arg t ∈ UpperHalfPlane.upperHalfPlaneSet := by
  simpa [UpperHalfPlane.upperHalfPlaneSet, arg_eq_I_div (t := t) ht] using (one_div_pos.2 ht.1)

lemma continuousOn_hf : ContinuousOn hf (Ioo (0 : ℝ) 1) := by
  have hden :
      ∀ t ∈ Ioo (0 : ℝ) 1, ((z₁' t : ℂ) + 1) ≠ 0 := by
    intro t ht
    have htne : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht.1)
    have hz : z₁' t = (-1 : ℂ) + I * t := by
      simpa [add_left_comm, add_comm, add_assoc] using z₁'_eq_of_mem (mem_Icc_of_Ioo ht)
    have hz_add : (z₁' t : ℂ) + 1 = I * t := by simp [hz, add_left_comm, add_comm]
    simpa [hz_add, mul_eq_zero] using (mul_ne_zero Complex.I_ne_zero htne)
  have harg : ContinuousOn arg (Ioo (0 : ℝ) 1) := by
    refine (continuousOn_const.div ?_ hden)
    simpa using (continuous_z₁'.continuousOn.add continuousOn_const)
  have hpow : ContinuousOn (fun t : ℝ => ((z₁' t : ℂ) + 1) ^ (2 : ℕ)) (Ioo (0 : ℝ) 1) := by
    simpa using (Continuous.continuousOn ((continuous_z₁'.add continuous_const).pow 2))
  have hφ : ContinuousOn φ₀'' UpperHalfPlane.upperHalfPlaneSet :=
    (MagicFunction.a.ComplexIntegrands.φ₀''_holo).continuousOn
  have hφcomp : ContinuousOn (fun t : ℝ => φ₀'' (arg t)) (Ioo (0 : ℝ) 1) := by
    refine hφ.comp harg ?_
    intro t ht
    exact arg_mem_upperHalfPlaneSet (t := t) ht
  -- Multiply the continuous factors.
  simpa [hf, mul_assoc] using
    (continuousOn_const.mul (hφcomp.mul hpow))

lemma exists_bound_norm_hf : ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖hf t‖ ≤ M := by
  rcases norm_φ₀_le with ⟨C₀, hC₀_pos, hC₀⟩
  refine ⟨C₀, ?_⟩
  intro t ht
  have ht0 : 0 < t := ht.1
  have hz : z₁' t = (-1 : ℂ) + I * t := by
    simpa [add_left_comm, add_comm, add_assoc] using z₁'_eq_of_mem (mem_Icc_of_Ioo ht)
  have hz_add : (z₁' t : ℂ) + 1 = I * t := by
    simp [hz, add_left_comm, add_comm]
  have harg_im : 0 < (arg t).im := by
    simpa [arg_eq_I_div (t := t) ht] using (one_div_pos.2 ht0)
  let z : ℍ := ⟨arg t, harg_im⟩
  have hz_half : (1 / 2 : ℝ) < z.im := by
    have h1 : (1 : ℝ) < 1 / t := (one_lt_one_div ht0) ht.2
    have hzim : z.im = 1 / t := by simp [z, arg_eq_I_div (t := t) ht]
    exact hzim ▸ (half_lt_self one_pos).trans h1
  have hφ'' : φ₀'' (arg t) = φ₀ z := by
    simpa [z] using (φ₀''_def (z := arg t) harg_im)
  have hφ : ‖φ₀ z‖ ≤ C₀ * rexp (-2 * π * z.im) := hC₀ z hz_half
  have hexp : rexp (-2 * π * z.im) ≤ 1 := by
    have : (-2 * π * z.im : ℝ) ≤ 0 := by
      have : 0 ≤ z.im := le_of_lt harg_im
      nlinarith [Real.pi_pos, this]
    simpa using (Real.exp_le_one_iff.2 this)
  have hφle : ‖φ₀'' (arg t)‖ ≤ C₀ := by
    calc
      ‖φ₀'' (arg t)‖ = ‖φ₀ z‖ := by simp [hφ'']
      _ ≤ C₀ * rexp (-2 * π * z.im) := hφ
      _ ≤ C₀ := by nlinarith [hexp]
  have hpow : ‖((z₁' t : ℂ) + 1) ^ (2 : ℕ)‖ ≤ 1 := by
    have ht1 : t ≤ 1 := le_of_lt ht.2
    have ht0' : 0 ≤ t := le_of_lt ht0
    have hIt : ‖(Complex.I : ℂ) * (t : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_mul, Complex.norm_real, abs_of_nonneg ht0'] using ht1
    simpa [hz_add, norm_pow, pow_two] using
      (mul_le_mul hIt hIt (by positivity) (by positivity))
  calc
    ‖hf t‖ = ‖φ₀'' (arg t)‖ * ‖((z₁' t : ℂ) + 1) ^ (2 : ℕ)‖ := by
      simp [hf]
    _ ≤ C₀ * 1 := by gcongr
    _ = C₀ := by ring

/-- Smoothness of `RealIntegrals.I₁'` as a function `ℝ → ℂ`. -/
public theorem I₁'_contDiff : ContDiff ℝ (⊤ : ℕ∞) I₁' := by
  refine DifferentiationUnderIntegral.contDiff_of_eq_integral_g_Ioo (coeff := coeff) (hf := hf) I₁'
    (fun x => by simpa [g] using I₁'_eq_integral_g_Ioo (x := x))
    continuousOn_hf continuous_coeff exists_bound_norm_hf coeff_norm_le

end

end MagicFunction.a.Schwartz.I1Smooth
