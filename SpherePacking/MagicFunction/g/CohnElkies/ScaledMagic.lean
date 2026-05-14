module
public import SpherePacking.MagicFunction.g.Basic
public import SpherePacking.MagicFunction.g.CohnElkies.PureImaginary
import SpherePacking.MagicFunction.a.Eigenfunction.FourierPermutations
import SpherePacking.MagicFunction.b.Eigenfunction.FourierPermutations
import SpherePacking.MagicFunction.g.CohnElkies.SignConditions
import SpherePacking.ForMathlib.FourierLinearEquiv

/-!
# Scaling the Cohn-Elkies hypotheses

Defines `scaledMagic`, obtained from Viazovska's magic function `g` by precomposing with scaling
by `Real.sqrt 2`, and transfers the Cohn-Elkies sign conditions from `g` to the scaled function
`scaledMagic` used in `SpherePacking.UpperBound`. Also includes `g_real` / `g_real_fourier`
(blueprint `thm:g1`/`thm:g`) showing that `g` and its Fourier transform are real-valued.
-/

namespace SpherePacking

open scoped FourierTransform
open SchwartzMap SpherePacking.ForMathlib.Fourier

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ)

/-- Non-vanishing of `Real.sqrt 2`. -/
public lemma sqrt2_ne_zero : (Real.sqrt (2 : ℝ)) ≠ 0 :=
  Real.sqrt_ne_zero'.2 (by positivity)

/-- The scaled Schwartz function used for the dimension-8 Cohn-Elkies LP bound. -/
@[expose] public noncomputable def scaledMagic : 𝓢(ℝ⁸, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero (K := ℝ) (M := ℝ⁸) (Real.sqrt 2) sqrt2_ne_zero).toContinuousLinearEquiv
    g

/-- The value of `scaledMagic` at `0` is `1`. -/
public theorem scaledMagic_zero : scaledMagic 0 = 1 := by
  simp [scaledMagic, g_zero]

/-- The value of the Fourier transform of `scaledMagic` at `0` is `1 / 16`. -/
public theorem fourier_scaledMagic_zero : FT scaledMagic 0 = (1 / 16 : ℂ) := by
  let c : ℝ := Real.sqrt 2
  let A : ℝ⁸ ≃ₗ[ℝ] ℝ⁸ := LinearEquiv.smulOfNeZero (K := ℝ) (M := ℝ⁸) c sqrt2_ne_zero
  have hdet : abs (LinearMap.det (A : ℝ⁸ →ₗ[ℝ] ℝ⁸)) = (16 : ℝ) := by
    have hA : (A : ℝ⁸ →ₗ[ℝ] ℝ⁸) = c • (LinearMap.id : ℝ⁸ →ₗ[ℝ] ℝ⁸) := by ext x; simp [A]
    have hc_pow : c ^ 8 = (16 : ℝ) := by
      rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul,
        show c ^ 2 = 2 from Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
      norm_num
    rw [hA]; simp [LinearMap.det_smul, LinearMap.det_id, hc_pow]
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
  simp_all

/-- Convenience form of `fourier_scaledMagic_zero` for the coerced function `⇑scaledMagic`. -/
public theorem fourier_scaledMagic_zero_fun : 𝓕 (⇑scaledMagic) 0 = (1 / 16 : ℂ) := by
  simpa [FourierTransform.fourierCLE_apply, SchwartzMap.fourier_coe] using fourier_scaledMagic_zero

end SpherePacking

namespace MagicFunction.g.CohnElkies

open scoped FourierTransform SchwartzMap
open Real Complex MagicFunction.FourierEigenfunctions

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ)

private theorem ofReal_re_eq (z : ℂ) (hz : z.im = 0) : (↑z.re : ℂ) = z :=
  Complex.ext (by simp) (by simp [hz])

/-- The magic function `g` is real-valued. -/
public theorem g_real (x : ℝ⁸) : (↑(g x).re : ℂ) = g x :=
  ofReal_re_eq (g x) <| by
    simp [g, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, Complex.sub_im,
      Complex.mul_im, a_pureImag (x := x), b_pureImag (x := x), div_eq_mul_inv, Complex.mul_re]

/-- The Fourier transform `𝓕 g` is real-valued. -/
public theorem g_real_fourier (x : ℝ⁸) : (↑((𝓕 g x).re : ℂ)) = (𝓕 g x) := by
  refine ofReal_re_eq (𝓕 g x) ?_
  have hFg : FT g = ((↑π * I) / 8640) • a + (I / (240 * (↑π))) • b := by
    simp [g, map_sub, map_smul, MagicFunction.a.Fourier.eig_a, MagicFunction.b.Fourier.eig_b,
      -FourierTransform.fourierCLE_apply]
  change ((𝓕 g) x).im = 0
  rw [show (𝓕 g) = FT g from by simp, hFg]
  simp [SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul, Complex.add_im, Complex.mul_im,
    a_pureImag (x := x), b_pureImag (x := x), div_eq_mul_inv, Complex.mul_re]

end MagicFunction.g.CohnElkies

namespace SpherePacking

open scoped FourierTransform SchwartzMap
open Real Complex SpherePacking

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open MagicFunction.g.CohnElkies

private noncomputable def scaleEquiv : ℝ⁸ ≃ₗ[ℝ] ℝ⁸ :=
  LinearEquiv.smulOfNeZero (K := ℝ) (M := ℝ⁸) (Real.sqrt 2) sqrt2_ne_zero

/-- `scaledMagic` is real-valued (scaled variant of `g_real`). -/
public theorem scaledMagic_real' : ∀ x : ℝ⁸, (↑(scaledMagic x).re : ℂ) = scaledMagic x := by
  simpa [SpherePacking.scaledMagic] using fun x => g_real (x := (Real.sqrt 2) • x)

private lemma fourier_scaledMagic_eq (x : ℝ⁸) :
    (𝓕 scaledMagic x) =
      |LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸)|⁻¹ •
        𝓕 g ((LinearMap.adjoint ((scaleEquiv.symm : ℝ⁸ ≃ₗ[ℝ] ℝ⁸) : ℝ⁸ →ₗ[ℝ] ℝ⁸)) x) := by
  simpa [SpherePacking.scaledMagic, scaleEquiv, SchwartzMap.fourier_coe] using
    SpherePacking.ForMathlib.Fourier.fourier_comp_linearEquiv (A := scaleEquiv) (f := g) (w := x)

/-- The Fourier transform `𝓕 scaledMagic` is real-valued (scaled variant of `g_real_fourier`). -/
public theorem scaledMagic_real_fourier' :
    ∀ x : ℝ⁸, (↑((𝓕 scaledMagic x).re : ℂ)) = (𝓕 scaledMagic x) := by
  intro x
  let y0 : ℝ⁸ := (LinearMap.adjoint ((scaleEquiv.symm : ℝ⁸ ≃ₗ[ℝ] ℝ⁸) : ℝ⁸ →ₗ[ℝ] ℝ⁸)) x
  have hImG : (𝓕 g y0).im = 0 := by
    simpa using (congrArg Complex.im (g_real_fourier (x := y0))).symm
  have hImScaled : (𝓕 scaledMagic x).im = 0 := by
    simpa [y0, Complex.smul_im, hImG] using congrArg Complex.im (fourier_scaledMagic_eq (x := x))
  exact Complex.ext (by simp) (by simp [hImScaled])

/-- Cohn-Elkies sign condition for `scaledMagic` outside the unit ball (scaled variant). -/
public theorem scaledMagic_cohnElkies₁' : ∀ x : ℝ⁸, ‖x‖ ≥ 1 → (scaledMagic x).re ≤ 0 := by
  intro x hx
  have h2 : (2 : ℝ) ≤ ‖(Real.sqrt 2) • x‖ ^ (2 : ℕ) := by
    rw [norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
    nlinarith [mul_le_mul hx hx (by positivity) (norm_nonneg x), sq_nonneg ‖x‖]
  simpa [SpherePacking.scaledMagic] using
    g_nonpos_of_norm_sq_ge_two (x := (Real.sqrt 2) • x) h2

/-- Cohn-Elkies nonnegativity for `𝓕 scaledMagic` (scaled variant). -/
public theorem scaledMagic_cohnElkies₂' : ∀ x : ℝ⁸, (𝓕 scaledMagic x).re ≥ 0 := by
  intro x
  let y0 : ℝ⁸ := (LinearMap.adjoint ((scaleEquiv.symm : ℝ⁸ ≃ₗ[ℝ] ℝ⁸) : ℝ⁸ →ₗ[ℝ] ℝ⁸)) x
  have hre : (𝓕 scaledMagic x).re =
      |LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸)|⁻¹ • (𝓕 g y0).re := by
    have hre' : (𝓕 scaledMagic x).re =
        (|LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸)|⁻¹ • 𝓕 g y0).re := by
      simpa [y0] using congrArg Complex.re (fourier_scaledMagic_eq (x := x))
    exact hre'.trans (by
      simpa using
        Complex.smul_re (r := |LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸)|⁻¹) (z := 𝓕 g y0))
  simpa [hre] using
    smul_nonneg (inv_nonneg.2 (abs_nonneg (LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸))))
      (by simpa using fourier_g_nonneg (x := y0))

end SpherePacking
