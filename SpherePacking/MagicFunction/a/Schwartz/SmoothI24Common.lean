module
public import SpherePacking.MagicFunction.a.Basic
public import SpherePacking.Integration.DifferentiationUnderIntegral
public import SpherePacking.Integration.Measure

import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.Integration.UpperHalfPlaneComp

/-!
# Smooth `I₂'`/`I₄'` common skeleton

Shared infrastructure for proving `ContDiff ℝ ⊤ I₂'` and `ContDiff ℝ ⊤ I₄'`.

Both `I₂'` and `I₄'` have integrands of the form
`t ↦ prefactor * φ₀''(arg t) * (z t + shift)^2 * cexp (x * coeff t)`
where `coeff t = (π*I) * z t`, `arg t = -1 / (z t + shift)`, and
`shift, prefactor ∈ {1, -1}` are small constants. The only genuine
differences between the `I₂'` and `I₄'` files are the parametrization
`z` (`z₂'` vs `z₄'`) and these constants.

This module extracts the common lemmas parameterized by
`(z, shift, prefactor)` together with the geometric facts that pin down
`arg`'s imaginary part.
-/

namespace MagicFunction.a.Schwartz.SmoothI24Common

noncomputable section

open scoped Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter intervalIntegral
open MagicFunction.PolyFourierCoeffBound
open MagicFunction.a.ComplexIntegrands
open SpherePacking.Integration
open SpherePacking.ForMathlib

/-- The coefficient function `t ↦ (π * I) * z t` shared by `I₂'` and `I₄'`. -/
@[expose] public def coeff (z : ℝ → ℂ) : ℝ → ℂ := fun t : ℝ => ((π : ℂ) * I) * z t

/-- The Mobius argument `t ↦ -1 / (z t + shift)` used to feed `φ₀''`. -/
@[expose] public def arg (z : ℝ → ℂ) (shift : ℂ) : ℝ → ℂ :=
    fun t : ℝ => (-1 : ℂ) / (z t + shift)

/-- The integrand `t ↦ prefactor * (φ₀''(arg t) * (z t + shift)^2)`. -/
@[expose] public def hf (z : ℝ → ℂ) (shift prefactor : ℂ) : ℝ → ℂ :=
    fun t : ℝ => prefactor * (φ₀'' (arg z shift t) * (z t + shift) ^ (2 : ℕ))

public lemma coeff_norm_le {z : ℝ → ℂ} (hnorm : ∀ t : ℝ, ‖z t‖ ≤ 2) (t : ℝ) :
    ‖coeff z t‖ ≤ 2 * π := by
  simpa [coeff, mul_assoc] using norm_mul_pi_I_le_two_pi (z := z t) (hz := hnorm t)

public lemma continuous_coeff {z : ℝ → ℂ} (hz : Continuous z) : Continuous (coeff z) := by
  simpa [coeff, mul_assoc] using continuous_const.mul hz

/-- If the Mobius image has positive imaginary part on `Ioo 0 1`, it lies in the
upper half-plane set. -/
public lemma arg_mem_upperHalfPlaneSet {z : ℝ → ℂ} {shift : ℂ}
    (harg_im_pos : ∀ t, t ∈ Ioo (0 : ℝ) 1 → 0 < (arg z shift t).im)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    arg z shift t ∈ UpperHalfPlane.upperHalfPlaneSet := harg_im_pos t ht

/-- Continuity of `hf` on `Ioo 0 1` given the continuity of `z`, non-vanishing of
`z + shift`, and the geometric fact that `arg` lands in the upper half-plane. -/
public lemma continuousOn_hf {z : ℝ → ℂ} (shift prefactor : ℂ)
    (hz : Continuous z)
    (hden : ∀ t, t ∈ Ioo (0 : ℝ) 1 → z t + shift ≠ 0)
    (harg_im_pos : ∀ t, t ∈ Ioo (0 : ℝ) 1 → 0 < (arg z shift t).im) :
    ContinuousOn (hf z shift prefactor) (Ioo (0 : ℝ) 1) := by
  have harg : ContinuousOn (arg z shift) (Ioo (0 : ℝ) 1) :=
    continuousOn_const.div (hz.continuousOn.add continuousOn_const) hden
  have hφcomp : ContinuousOn (fun t : ℝ => φ₀'' (arg z shift t)) (Ioo (0 : ℝ) 1) :=
    φ₀''_holo.continuousOn.comp harg harg_im_pos
  simpa [hf, mul_assoc] using
    continuousOn_const.mul (hφcomp.mul ((hz.add continuous_const).pow 2).continuousOn)

/-- Uniform bound on `hf` over `Ioo 0 1` given `‖z t‖ ≤ 2` and `Im(arg t) > 1/2`. -/
public lemma exists_bound_norm_hf {z : ℝ → ℂ} (shift prefactor : ℂ)
    (hnorm : ∀ t : ℝ, ‖z t‖ ≤ 2) (hshift : ‖shift‖ ≤ 1)
    (harg_im_half : ∀ t, t ∈ Ioo (0 : ℝ) 1 → (1 / 2 : ℝ) < (arg z shift t).im) :
    ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖hf z shift prefactor t‖ ≤ M := by
  rcases norm_φ₀_le with ⟨C₀, hC₀_pos, hC₀⟩
  refine ⟨‖prefactor‖ * (C₀ * rexp (-π) * ((3 : ℝ) ^ (2 : ℕ))), fun t ht => ?_⟩
  have hpos : 0 < (arg z shift t).im :=
    lt_trans (by norm_num : (0 : ℝ) < 1 / 2) (harg_im_half t ht)
  have hφle : ‖φ₀'' (arg z shift t)‖ ≤ C₀ * rexp (-π) :=
    norm_φ₀''_le_mul_exp_neg_pi_of_one_half_lt_im (C₀ := C₀) (hC₀_pos := hC₀_pos)
      (hC₀ := hC₀) (z := ⟨arg z shift t, hpos⟩) (harg_im_half t ht)
  have hpow : ‖(z t + shift) ^ (2 : ℕ)‖ ≤ (3 : ℝ) ^ (2 : ℕ) := by
    simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _)
      ((norm_add_le _ _).trans <| by linarith [hnorm t, hshift]) 2
  calc ‖hf z shift prefactor t‖
      = ‖prefactor‖ * (‖φ₀'' (arg z shift t)‖ * ‖(z t + shift) ^ (2 : ℕ)‖) := by simp [hf]
    _ ≤ ‖prefactor‖ * ((C₀ * rexp (-π)) * ((3 : ℝ) ^ (2 : ℕ))) := by gcongr
    _ = ‖prefactor‖ * (C₀ * rexp (-π) * ((3 : ℝ) ^ (2 : ℕ))) := by ring

/-- Smoothness of the integral `f` expressed via `DifferentiationUnderIntegral.g`
with kernel `coeff z` and integrand `hf z shift prefactor`. -/
public theorem contDiff_of_eq_integral_g_Ioo {z : ℝ → ℂ} {shift prefactor : ℂ} {f : ℝ → ℂ}
    (hfEq :
      ∀ x : ℝ, f x = ∫ t in Ioo (0 : ℝ) 1,
        DifferentiationUnderIntegral.g (coeff := coeff z) (hf := hf z shift prefactor) x t)
    (hz : Continuous z)
    (hnorm : ∀ t : ℝ, ‖z t‖ ≤ 2) (hshift : ‖shift‖ ≤ 1)
    (hden : ∀ t, t ∈ Ioo (0 : ℝ) 1 → z t + shift ≠ 0)
    (harg_im_pos : ∀ t, t ∈ Ioo (0 : ℝ) 1 → 0 < (arg z shift t).im)
    (harg_im_half : ∀ t, t ∈ Ioo (0 : ℝ) 1 → (1 / 2 : ℝ) < (arg z shift t).im) :
    ContDiff ℝ (⊤ : ℕ∞) f := by
  simpa [funext hfEq] using
    (DifferentiationUnderIntegral.contDiff_integral_g_Ioo
      (coeff := coeff z) (hf := hf z shift prefactor)
      (continuousOn_hf shift prefactor hz hden harg_im_pos)
      (continuous_coeff hz)
      (exists_bound_norm_hf shift prefactor hnorm hshift harg_im_half)
      (coeff_norm_le hnorm))

end

end MagicFunction.a.Schwartz.SmoothI24Common
