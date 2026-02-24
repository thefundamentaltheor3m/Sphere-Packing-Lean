module
public import SpherePacking.MagicFunction.g.Basic
import SpherePacking.ForMathlib.FourierLinearEquiv


/-!
# The scaled magic function

This file defines the scaled Schwartz function `scaledMagic`, obtained from Viazovska's magic
function `g` by precomposing with scaling by `Real.sqrt 2`, and computes its value and Fourier
value at `0`.

## Main definitions
* `SpherePacking.scaledMagic`

## Main statements
* `SpherePacking.scaledMagic_zero`
* `SpherePacking.fourier_scaledMagic_zero`
* `SpherePacking.scaledMagic_ratio`
-/

namespace SpherePacking

open scoped FourierTransform

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section FourierScalingAtZero

open SchwartzMap SpherePacking.ForMathlib.Fourier

local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ)

/-- Non-vanishing of `Real.sqrt 2`. -/
public lemma sqrt2_ne_zero : (Real.sqrt (2 : ℝ)) ≠ 0 :=
  Real.sqrt_ne_zero'.2 (by positivity)

/-- The scaled Schwartz function used for the dimension-8 Cohn-Elkies LP bound. -/
@[expose] public noncomputable def scaledMagic : 𝓢(ℝ⁸, ℂ) :=
  let c : ℝ := Real.sqrt 2
  let A : ℝ⁸ ≃ₗ[ℝ] ℝ⁸ := LinearEquiv.smulOfNeZero (K := ℝ) (M := ℝ⁸) c sqrt2_ne_zero
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv g

/-- The value of `scaledMagic` at `0` is `1`. -/
public theorem scaledMagic_zero : scaledMagic 0 = 1 := by
  simp [scaledMagic, g_zero]

/-- The value of the Fourier transform of `scaledMagic` at `0` is `1 / 16`. -/
public theorem fourier_scaledMagic_zero : FT scaledMagic 0 = (1 / 16 : ℂ) := by
  let c : ℝ := Real.sqrt 2
  let A : ℝ⁸ ≃ₗ[ℝ] ℝ⁸ := LinearEquiv.smulOfNeZero (K := ℝ) (M := ℝ⁸) c sqrt2_ne_zero
  have hdet : abs (LinearMap.det (A : ℝ⁸ →ₗ[ℝ] ℝ⁸)) = (16 : ℝ) := by
    have hA : (A : ℝ⁸ →ₗ[ℝ] ℝ⁸) = c • (LinearMap.id : ℝ⁸ →ₗ[ℝ] ℝ⁸) := by
      ext x
      simp [A]
    have hc_pow : c ^ 8 = (16 : ℝ) := by
      calc
        c ^ 8 = (c ^ 2) ^ 4 := by simpa using (pow_mul c 2 4)
        _ = (2 : ℝ) ^ 4 := by
              simp [c, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
        _ = 16 := by norm_num
    rw [hA]
    simp [LinearMap.det_smul, LinearMap.det_id, hc_pow]
  have hg0 : (𝓕 (g : ℝ⁸ → ℂ)) 0 = (1 : ℂ) := by
    simpa [FourierTransform.fourierCLE_apply, SchwartzMap.fourier_coe] using
      (fourier_g_zero : FT g 0 = 1)
  have hscaled :
      FT scaledMagic 0 =
        (abs (LinearMap.det (A : ℝ⁸ →ₗ[ℝ] ℝ⁸)))⁻¹ • (𝓕 (g : ℝ⁸ → ℂ)) 0 := by
    simpa [FourierTransform.fourierCLE_apply, SchwartzMap.fourier_coe, scaledMagic, c, A,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      (SpherePacking.ForMathlib.Fourier.fourier_comp_linearEquiv
        (A := A) (f := (g : ℝ⁸ → ℂ)) (w := (0 : ℝ⁸)))
  calc
    FT scaledMagic 0
        = (abs (LinearMap.det (A : ℝ⁸ →ₗ[ℝ] ℝ⁸)))⁻¹ • (𝓕 (g : ℝ⁸ → ℂ)) 0 := hscaled
    _ = (1 / 16 : ℂ) := by
            simp [hg0, hdet, one_div]

/-- Convenience form of `fourier_scaledMagic_zero` for the coerced function `⇑scaledMagic`. -/
public theorem fourier_scaledMagic_zero_fun : 𝓕 (⇑scaledMagic) 0 = (1 / 16 : ℂ) := by
  simpa [FourierTransform.fourierCLE_apply, SchwartzMap.fourier_coe] using fourier_scaledMagic_zero

/-- The ratio `(scaledMagic 0).re / (𝓕 (⇑scaledMagic) 0).re` equals `16`. -/
public theorem scaledMagic_ratio :
    (scaledMagic 0).re / (𝓕 (⇑scaledMagic) 0).re = (16 : ℝ) := by
  simp [scaledMagic_zero, fourier_scaledMagic_zero_fun]

end FourierScalingAtZero

end SpherePacking
