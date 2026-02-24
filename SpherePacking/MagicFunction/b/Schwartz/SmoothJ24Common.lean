module
public import SpherePacking.MagicFunction.b.PsiBounds
public import SpherePacking.Integration.SmoothIntegralCommon
import SpherePacking.Integration.UpperHalfPlaneComp

/-!
# Smooth `J₂'`/`J₄'` common skeleton

Wrappers around `SpherePacking.Integration.SmoothIntegralCommon` for
`coeff t = (π*I) * z t` and `hf t = c * ψT' (z t)`.
-/

namespace MagicFunction.b.Schwartz.SmoothJ24Common

noncomputable section

open scoped Interval UpperHalfPlane

open Complex Real Set MeasureTheory Filter intervalIntegral
open MagicFunction.b.PsiBounds SpherePacking.ForMathlib

/-- The coefficient function `t ↦ (π * I) * z t` used for smooth integral kernels. -/
@[expose] public def coeff (z : ℝ → ℂ) : ℝ → ℂ := fun t : ℝ ↦ ((π : ℂ) * I) * z t

private lemma continuous_ψT'_comp {z : ℝ → ℂ} (hz : Continuous z) (him : ∀ t : ℝ, 0 < (z t).im) :
    Continuous fun t : ℝ => ψT' (z t) := by
  refine SpherePacking.Integration.continuous_comp_upperHalfPlane_mk
    (ψT := ψT) (ψT' := ψT') (MagicFunction.b.PsiBounds.continuous_ψT)
    (z := z) hz him (fun t => by simp [ψT', him t])
private lemma coeff_norm_le {z : ℝ → ℂ} (hnorm : ∀ t : ℝ, ‖z t‖ ≤ 2) (t : ℝ) :
    ‖coeff z t‖ ≤ 2 * π := by
  simpa [coeff, mul_assoc] using norm_mul_pi_I_le_two_pi (z := z t) (hz := hnorm t)
private lemma exists_bound_norm_hf_mul {z : ℝ → ℂ} (c : ℂ) (hz : Continuous z)
    (him : ∀ t : ℝ, 0 < (z t).im) :
    ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖c * ψT' (z t)‖ ≤ M := by
  simpa using
    SpherePacking.Integration.exists_bound_norm_uIoc_zero_one_of_continuous
      (f := fun t : ℝ => c * ψT' (z t))
      (continuous_const.mul (continuous_ψT'_comp (z := z) hz him))

/-- `ContDiff` for a function defined as `SmoothIntegralCommon.I` with `coeff t = (π * I) * z t`. -/
public theorem contDiff_of_eq_I0_mul {z : ℝ → ℂ} {c : ℂ} {f : ℝ → ℂ}
    (hfEq :
      ∀ x : ℝ,
        f x =
          SpherePacking.Integration.SmoothIntegralCommon.I
            (coeff := coeff z) (hf := fun t : ℝ ↦ c * ψT' (z t)) 0 x)
    (hz : Continuous z) (him : ∀ t : ℝ, 0 < (z t).im) (hnorm : ∀ t : ℝ, ‖z t‖ ≤ 2) :
    ContDiff ℝ (⊤ : ℕ∞) f := by
  refine
    (SpherePacking.Integration.SmoothIntegralCommon.contDiff_of_eq_I0
      (coeff := coeff z) (hf := fun t : ℝ ↦ c * ψT' (z t)) (f := f) (hfEq := hfEq)
      (continuous_const.mul (continuous_ψT'_comp (z := z) hz him))
      (by simpa [coeff] using (continuous_const.mul hz))
      (exists_bound_norm_hf_mul (z := z) (c := c) hz him) (coeff_norm_le (z := z) hnorm))

/-- Polynomial decay bounds for iterated derivatives of `f`, assuming `im (z t) = 1`. -/
public theorem decay_of_eq_I0_of_coeff_re_mul {z : ℝ → ℂ} {c : ℂ} {f : ℝ → ℂ}
    (hfEq :
      ∀ x : ℝ,
        f x =
          SpherePacking.Integration.SmoothIntegralCommon.I
            (coeff := coeff z) (hf := fun t : ℝ ↦ c * ψT' (z t)) 0 x)
    (hz : Continuous z) (him : ∀ t : ℝ, 0 < (z t).im) (hnorm : ∀ t : ℝ, ‖z t‖ ≤ 2)
    (him1 : ∀ t : ℝ, (z t).im = 1) :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  refine
    (SpherePacking.Integration.SmoothIntegralCommon.decay_of_eq_I0_of_coeff_re
      (coeff := coeff z) (hf := fun t : ℝ ↦ c * ψT' (z t)) (f := f) (hfEq := hfEq)
      (continuous_const.mul (continuous_ψT'_comp (z := z) hz him))
      (by simpa [coeff] using (continuous_const.mul hz))
      (exists_bound_norm_hf_mul (z := z) (c := c) hz him) (coeff_norm_le (z := z) hnorm)
      (coeff_re := fun t => by
        -- `re ((π*I) * z) = -π * im z`, so `im z = 1` gives `-π`.
        simp [coeff, Complex.mul_re, him1 t, mul_assoc]))
end
end MagicFunction.b.Schwartz.SmoothJ24Common
