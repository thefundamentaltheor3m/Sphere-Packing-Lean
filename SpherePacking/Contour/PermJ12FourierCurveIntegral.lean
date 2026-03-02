module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

import Mathlib.MeasureTheory.Integral.Prod

public import SpherePacking.ForMathlib.ScalarOneForm
public import SpherePacking.Contour.Segments
public import SpherePacking.Integration.Measure

/-!
# Fourier transform as a curve integral (template lemmas)

These lemmas implement the common Fubini argument used in the `perm_J1/J2` developments:
1. rewrite `𝓕 Jⱼ` using `fourier_eq'`;
2. express the radial profile as a `t`-integral of a kernel;
3. swap the order of integration via `MeasureTheory.integral_integral_swap`;
4. evaluate the inner `x`-integral to obtain a function of the segment parameter `t`;
5. identify the resulting `t`-integral with a curve integral on a segment.

The dimension-specific files only need to provide:
- the "phase * radial profile = t-integral of the kernel" bridge lemma;
- an `Integrable` hypothesis for Fubini; and
- a lemma identifying the `t`-integral with the desired curve integral.
-/

open scoped FourierTransform RealInnerProductSpace Complex
open MeasureTheory
open MagicFunction

namespace SpherePacking.Contour

noncomputable section

private lemma cexp_neg_two_pi_inner_mul_I
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x w : V) :
    cexp (-(2 * (↑Real.pi : ℂ) * (↑⟪x, w⟫ : ℂ) * Complex.I)) =
      cexp (↑(-2 * Real.pi * ⟪x, w⟫) * Complex.I) := by
  simp [mul_assoc]

private theorem fourier_J_eq_curveIntegral_of
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {μ : Measure ℝ} [SFinite μ]
    {J : SchwartzMap V ℂ} {J' : ℝ → ℂ}
    {permJKernel : V → V × ℝ → ℂ}
    {g : V → ℝ → ℂ}
    {Ψ_fourier : ℝ → ℂ → ℂ}
    (a b : ℂ)
    (J_apply : ∀ x : V, (J : V → ℂ) x = J' (‖x‖ ^ (2 : ℕ)))
    (phase_mul_J'_eq_integral_permJKernel :
      ∀ w x : V,
        cexp (↑(-2 * Real.pi * ⟪x, w⟫) * Complex.I) * J' (‖x‖ ^ (2 : ℕ)) =
          ∫ t : ℝ, permJKernel w (x, t) ∂μ)
    (integrable_permJKernel :
      ∀ w : V,
        Integrable (permJKernel w)
          ((volume : Measure V).prod μ))
    (integral_permJKernel_x_ae :
      ∀ w : V,
        (fun t : ℝ => (∫ x : V, permJKernel w (x, t) ∂(volume : Measure V))) =ᵐ[μ] fun t =>
          g w t)
    (integral_g_eq_curveIntegral :
      ∀ w : V,
        (∫ t : ℝ, g w t ∂μ) =
          (∫ᶜ z in Path.segment a b,
            scalarOneForm (Ψ_fourier (‖w‖ ^ (2 : ℕ))) z))
  (w : V) :
    (𝓕 (J : V → ℂ)) w =
      (∫ᶜ z in Path.segment a b,
        scalarOneForm (Ψ_fourier (‖w‖ ^ (2 : ℕ))) z) := by
  rw [Real.fourier_eq' (J : V → ℂ) w]
  simp only [neg_mul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat, smul_eq_mul]
  have htoIter :
      (fun x : V =>
          cexp (-(2 * (↑Real.pi : ℂ) * (↑⟪x, w⟫ : ℂ) * Complex.I)) * (J : V → ℂ) x) =
        fun x : V =>
          ∫ t : ℝ, permJKernel w (x, t) ∂μ := by
    funext x
    simpa [J_apply (x := x), cexp_neg_two_pi_inner_mul_I (x := x) (w := w)] using
      phase_mul_J'_eq_integral_permJKernel (w := w) (x := x)
  have hint :
      Integrable (Function.uncurry fun x t => permJKernel w (x, t))
        ((volume : Measure V).prod μ) := by
    simpa [Function.uncurry] using (integrable_permJKernel (w := w))
  have hAE :
      (fun t : ℝ => (∫ x : V, permJKernel w (x, t) ∂(volume : Measure V))) =ᵐ[μ] fun t =>
        g w t := by
    simpa using (integral_permJKernel_x_ae (w := w))
  have hswap :
      (∫ x : V, ∫ t : ℝ, permJKernel w (x, t) ∂μ) =
        ∫ t : ℝ, ∫ x : V, permJKernel w (x, t) ∂(volume : Measure V) ∂μ := by
    simpa using
      (MeasureTheory.integral_integral_swap (μ := (volume : Measure V)) (ν := μ)
        (f := fun x t => permJKernel w (x, t)) hint)
  calc
    (∫ x : V,
          cexp (-(2 * (↑Real.pi : ℂ) * (↑⟪x, w⟫ : ℂ) * Complex.I)) * (J : V → ℂ) x) =
        ∫ x : V, ∫ t : ℝ, permJKernel w (x, t) ∂μ := by simp [htoIter]
    _ = ∫ t : ℝ, ∫ x : V, permJKernel w (x, t) ∂(volume : Measure V) ∂μ := hswap
    _ = ∫ t : ℝ, g w t ∂μ := by simpa using (MeasureTheory.integral_congr_ae hAE)
    _ =
        (∫ᶜ z in Path.segment a b,
          scalarOneForm (Ψ_fourier (‖w‖ ^ (2 : ℕ))) z) := integral_g_eq_curveIntegral (w := w)

/--
Template lemma: prove a `curveIntegral` formula for `(𝓕 J₁) w` by a Fubini swap argument.

The hypotheses provide:
- a radial-profile description of `J₁`;
- a kernel representation of the Fourier integrand as an integral over `t`;
- integrability for Fubini; and
- an identification of the resulting `t`-integral with the target curve integral.
-/
public theorem fourier_J₁_eq_curveIntegral_of
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {μ : Measure ℝ} [SFinite μ]
    {J₁ : SchwartzMap V ℂ} {J₁' : ℝ → ℂ}
    {permJ1Kernel : V → V × ℝ → ℂ}
    {g : V → ℝ → ℂ}
    {Ψ₁_fourier : ℝ → ℂ → ℂ}
    (J₁_apply : ∀ x : V, (J₁ : V → ℂ) x = J₁' (‖x‖ ^ (2 : ℕ)))
    (phase_mul_J₁'_eq_integral_permJ1Kernel :
      ∀ w x : V,
        cexp (↑(-2 * Real.pi * ⟪x, w⟫) * Complex.I) * J₁' (‖x‖ ^ (2 : ℕ)) =
          ∫ t : ℝ, permJ1Kernel w (x, t) ∂μ)
    (integrable_permJ1Kernel :
      ∀ w : V,
        Integrable (permJ1Kernel w)
          ((volume : Measure V).prod μ))
    (integral_permJ1Kernel_x_ae :
      ∀ w : V,
        (fun t : ℝ => (∫ x : V, permJ1Kernel w (x, t) ∂(volume : Measure V))) =ᵐ[μ] fun t =>
          g w t)
    (integral_g_eq_curveIntegral :
      ∀ w : V,
        (∫ t : ℝ, g w t ∂μ) =
          (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
            scalarOneForm (Ψ₁_fourier (‖w‖ ^ (2 : ℕ))) z))
    (w : V) :
    (𝓕 (J₁ : V → ℂ)) w =
      (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
        scalarOneForm (Ψ₁_fourier (‖w‖ ^ (2 : ℕ))) z) := by
  simpa using
    (fourier_J_eq_curveIntegral_of (J := J₁) (J' := J₁') (permJKernel := permJ1Kernel) (g := g)
        (Ψ_fourier := Ψ₁_fourier) (a := (-1 : ℂ)) (b := (-1 : ℂ) + Complex.I) J₁_apply
        phase_mul_J₁'_eq_integral_permJ1Kernel integrable_permJ1Kernel integral_permJ1Kernel_x_ae
        integral_g_eq_curveIntegral w)

/--
Template lemma: prove a `curveIntegral` formula for `(𝓕 J₂) w` by the same Fubini pattern as for
`fourier_J₁_eq_curveIntegral_of`.
-/
public theorem fourier_J₂_eq_curveIntegral_of
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {μ : Measure ℝ} [SFinite μ]
    {J₂ : SchwartzMap V ℂ} {J₂' : ℝ → ℂ}
    {permJ2Kernel : V → V × ℝ → ℂ}
    {g : V → ℝ → ℂ}
    {Ψ₁_fourier : ℝ → ℂ → ℂ}
    (J₂_apply : ∀ x : V, (J₂ : V → ℂ) x = J₂' (‖x‖ ^ (2 : ℕ)))
    (phase_mul_J₂'_eq_integral_permJ2Kernel :
      ∀ w x : V,
        cexp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I) * J₂' (‖x‖ ^ (2 : ℕ)) =
          ∫ t : ℝ, permJ2Kernel w (x, t) ∂μ)
    (integrable_permJ2Kernel :
      ∀ w : V,
        Integrable (permJ2Kernel w)
          ((volume : Measure V).prod μ))
    (integral_permJ2Kernel_x_ae :
      ∀ w : V,
        (fun t : ℝ => (∫ x : V, permJ2Kernel w (x, t) ∂(volume : Measure V))) =ᵐ[μ] fun t =>
          g w t)
    (integral_g_eq_curveIntegral :
      ∀ w : V,
        (∫ t : ℝ, g w t ∂μ) =
          (∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (Ψ₁_fourier (‖w‖ ^ (2 : ℕ))) z))
    (w : V) :
    (𝓕 (J₂ : V → ℂ)) w =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
        scalarOneForm (Ψ₁_fourier (‖w‖ ^ (2 : ℕ))) z) := by
  have hphase' :
      ∀ w x : V,
        cexp (↑(-2 * Real.pi * ⟪x, w⟫) * Complex.I) * J₂' (‖x‖ ^ (2 : ℕ)) =
          ∫ t : ℝ, permJ2Kernel w (x, t) ∂μ := by
    intro w x
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      phase_mul_J₂'_eq_integral_permJ2Kernel (w := w) (x := x)
  simpa using
    (fourier_J_eq_curveIntegral_of (J := J₂) (J' := J₂') (permJKernel := permJ2Kernel) (g := g)
        (Ψ_fourier := Ψ₁_fourier) (a := (-1 : ℂ) + Complex.I) (b := Complex.I) J₂_apply hphase'
        integrable_permJ2Kernel integral_permJ2Kernel_x_ae integral_g_eq_curveIntegral w)

/-! ### `μIoc01` segment integral helpers -/

public lemma integral_I_mul_muIoc01_z₁line (F : ℂ → ℂ) :
    (∫ t : ℝ, (Complex.I : ℂ) * F (z₁line t) ∂SpherePacking.Integration.μIoc01) =
      (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I), scalarOneForm F z) := by
  simpa [SpherePacking.Contour.dir_z₁line] using
    (SpherePacking.Integration.integral_dir_mul_muIoc01_eq_curveIntegral_segment
      (F := F) (a := (-1 : ℂ)) (b := (-1 : ℂ) + Complex.I) (zline := z₁line)
      SpherePacking.Contour.lineMap_z₁line)

public lemma integral_muIoc01_z₂line (F : ℂ → ℂ) :
    (∫ t : ℝ, F (z₂line t) ∂SpherePacking.Integration.μIoc01) =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I, scalarOneForm F z) := by
  simpa [SpherePacking.Contour.dir_z₂line, one_mul] using
    (SpherePacking.Integration.integral_dir_mul_muIoc01_eq_curveIntegral_segment
      (F := F) (a := (-1 : ℂ) + Complex.I) (b := Complex.I) (zline := z₂line)
      SpherePacking.Contour.lineMap_z₂line)

end

end SpherePacking.Contour
