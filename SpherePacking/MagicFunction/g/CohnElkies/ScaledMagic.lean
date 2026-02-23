module
public import SpherePacking.ScaledMagic
import SpherePacking.MagicFunction.g.CohnElkies.RealValued
import SpherePacking.MagicFunction.g.CohnElkies.SignConditions
import SpherePacking.ForMathlib.FourierLinearEquiv

/-!
# Scaling the Cohn-Elkies hypotheses

This file transfers the Cohn-Elkies sign conditions from `g` to the scaled function `scaledMagic`
used in `SpherePacking.UpperBound`.

## Main statements
* `SpherePacking.scaledMagic_real'`
* `SpherePacking.scaledMagic_real_fourier'`
* `SpherePacking.scaledMagic_cohnElkies₁'`
* `SpherePacking.scaledMagic_cohnElkies₂'`
-/

namespace SpherePacking

open scoped FourierTransform SchwartzMap
open Real Complex SpherePacking

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open MagicFunction.g.CohnElkies

private noncomputable def scaleEquiv : ℝ⁸ ≃ₗ[ℝ] ℝ⁸ :=
  LinearEquiv.smulOfNeZero (K := ℝ) (M := ℝ⁸) (Real.sqrt 2) sqrt2_ne_zero

/--
`scaledMagic` is real-valued.

The prime `'` indicates this is the scaled variant of the corresponding real-valuedness lemma
for `g`.
-/
public theorem scaledMagic_real' : ∀ x : ℝ⁸, (↑(scaledMagic x).re : ℂ) = scaledMagic x := by
  simpa [SpherePacking.scaledMagic] using fun x => (g_real (x := (Real.sqrt 2) • x))

lemma fourier_scaledMagic_fun_eq (x : ℝ⁸) :
    (𝓕 (fun y : ℝ⁸ => scaledMagic y) x) =
      |LinearMap.det
          (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸)|⁻¹ •
  𝓕 (fun y : ℝ⁸ => g y)
          ((LinearMap.adjoint
              ((scaleEquiv.symm : ℝ⁸ ≃ₗ[ℝ] ℝ⁸) : ℝ⁸ →ₗ[ℝ] ℝ⁸)) x) := by
  simpa [SpherePacking.scaledMagic, scaleEquiv] using
    SpherePacking.ForMathlib.Fourier.fourier_comp_linearEquiv (A := scaleEquiv) (f := g) (w := x)

private lemma fourier_scaledMagic_eq (x : ℝ⁸) :
    (𝓕 scaledMagic x) =
      |LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸)|⁻¹ •
        𝓕 g ((LinearMap.adjoint ((scaleEquiv.symm : ℝ⁸ ≃ₗ[ℝ] ℝ⁸) : ℝ⁸ →ₗ[ℝ] ℝ⁸)) x) := by
  simpa [SchwartzMap.fourier_coe, scaleEquiv] using (fourier_scaledMagic_fun_eq (x := x))

/--
The Fourier transform `𝓕 scaledMagic` is real-valued.

The prime `'` indicates this is the scaled variant of the corresponding real-valuedness lemma
for `𝓕 g`.
-/
public theorem scaledMagic_real_fourier' :
    ∀ x : ℝ⁸, (↑((𝓕 scaledMagic x).re : ℂ)) = (𝓕 scaledMagic x) := by
  intro x
  let y0 : ℝ⁸ :=
    (LinearMap.adjoint ((scaleEquiv.symm : ℝ⁸ ≃ₗ[ℝ] ℝ⁸) : ℝ⁸ →ₗ[ℝ] ℝ⁸)) x
  have hImG : (𝓕 g y0).im = 0 := by
    simpa using (congrArg Complex.im (g_real_fourier (x := y0))).symm
  have hImScaled : (𝓕 scaledMagic x).im = 0 := by
    simpa [y0, Complex.smul_im, hImG] using congrArg Complex.im (fourier_scaledMagic_eq (x := x))
  exact Complex.ext (by simp) (by simp [hImScaled])

/--
Cohn-Elkies sign condition for `scaledMagic` outside the unit ball.

The prime `'` indicates this is the scaled variant of the corresponding lemma for `g`.
-/
public theorem scaledMagic_cohnElkies₁' : ∀ x : ℝ⁸, ‖x‖ ≥ 1 → (scaledMagic x).re ≤ 0 := by
  intro x hx
  have hxSq : (1 : ℝ) ≤ ‖x‖ ^ (2 : ℕ) := by
    simpa [pow_two] using (mul_le_mul hx hx (by positivity) (norm_nonneg x))
  have hnorm : ‖(Real.sqrt 2) • x‖ ^ (2 : ℕ) = (2 : ℝ) * ‖x‖ ^ (2 : ℕ) := by
    simp [norm_smul, pow_two, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    ring_nf
    simp [Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ 2), pow_two]
    simp [mul_comm]
  have h2 : (2 : ℝ) ≤ ‖(Real.sqrt 2) • x‖ ^ (2 : ℕ) := by
    simp_all
  have h := g_nonpos_of_norm_sq_ge_two (x := (Real.sqrt 2) • x) h2
  simpa [SpherePacking.scaledMagic] using h

/--
Cohn-Elkies nonnegativity condition for the Fourier transform `𝓕 scaledMagic`.

The prime `'` indicates this is the scaled variant of the corresponding lemma for `𝓕 g`.
-/
public theorem scaledMagic_cohnElkies₂' : ∀ x : ℝ⁸, (𝓕 scaledMagic x).re ≥ 0 := by
  intro x
  let y0 : ℝ⁸ :=
    (LinearMap.adjoint ((scaleEquiv.symm : ℝ⁸ ≃ₗ[ℝ] ℝ⁸) : ℝ⁸ →ₗ[ℝ] ℝ⁸)) x
  have hre :
      (𝓕 scaledMagic x).re = |LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸)|⁻¹ • (𝓕 g y0).re := by
    have hre' : (𝓕 scaledMagic x).re =
        (|LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸)|⁻¹ • 𝓕 g y0).re := by
      simpa [y0] using congrArg Complex.re (fourier_scaledMagic_eq (x := x))
    exact hre'.trans (by
      simpa using
        (Complex.smul_re (r := |LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸)|⁻¹) (z := 𝓕 g y0)))
  have : 0 ≤ |LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸)|⁻¹ • (𝓕 g y0).re :=
      smul_nonneg (inv_nonneg.2 (abs_nonneg _)) (by simpa using (fourier_g_nonneg (x := y0)))
  simpa [hre] using this

end SpherePacking
