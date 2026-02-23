module
public import SpherePacking.MagicFunction.a.Eigenfunction.PermI12Prelude
import SpherePacking.MagicFunction.a.Eigenfunction.PermI5Kernel
import SpherePacking.MagicFunction.a.Eigenfunction.PermI12FourierIntegrableI2
import SpherePacking.MagicFunction.a.Eigenfunction.PermI12FourierIntegrableI1
import SpherePacking.MagicFunction.a.Eigenfunction.PermI12FourierAux
import SpherePacking.Integration.FubiniIoc01


/-!
# Fourier transforms of `I₁` and `I₂` as curve integrals

We rewrite the Fourier transforms of `I₁` and `I₂` as curve integrals of `Φ₁_fourier` along two
straight segments. This is the analytic input for the contour permutation identity.

## Main statements
* `fourier_I₁_eq_curveIntegral`
* `fourier_I₂_eq_curveIntegral`
-/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter

section Integral_Permutations

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section PermI12Fourier_Main

open MeasureTheory Set Complex Real
open SpherePacking.Integration
open SpherePacking.Contour
open scoped Interval


/-- Fourier transform of `I₁`, rewritten as a curve integral of `Φ₁_fourier` along the first
vertical segment. -/
public lemma fourier_I₁_eq_curveIntegral (w : ℝ⁸) :
    (𝓕 (I₁ : ℝ⁸ → ℂ)) w =
      (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + I),
        scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) := by
  -- Expand the Fourier transform as an integral and rewrite `I₁` using the segment parametrisation.
  rw [fourier_eq' (I₁ : ℝ⁸ → ℂ) w]
  simp only [smul_eq_mul, I₁_apply, mul_assoc]
  -- Replace `I₁'` by the curve integral along the vertical segment, then unfold it.
  have hI₁' (x : ℝ⁸) :
      MagicFunction.a.RealIntegrals.I₁' (‖x‖ ^ 2) =
        ∫ t in Ioc (0 : ℝ) 1,
          (I : ℂ) * MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (z₁line t) := by
    rw [I₁'_eq_curveIntegral_segment (r := ‖x‖ ^ 2)]
    rw [curveIntegral_segment
      (ω := scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2)))
      (-1 : ℂ) ((-1 : ℂ) + I)]
    rw [intervalIntegral.integral_of_le (μ := (volume : Measure ℝ))
      (a := (0 : ℝ)) (b := 1) (by norm_num)]
    have hdir : (((-1 : ℂ) + I) - (-1 : ℂ)) = (I : ℂ) :=
      SpherePacking.Contour.dir_z₁line
    simp [scalarOneForm_apply, hdir, SpherePacking.Contour.lineMap_z₁line]
  -- Move the `x`-dependent phase factor inside the `t` integral so we can use Fubini.
  have hmul :
      (fun x : ℝ⁸ ↦
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            (∫ t in Ioc (0 : ℝ) 1,
              (I : ℂ) * MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (z₁line t))) =
        fun x : ℝ⁸ ↦
          ∫ t in Ioc (0 : ℝ) 1,
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              ((I : ℂ) * MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (z₁line t)) := by
    ext x
    simpa [μIoc01] using
      (MeasureTheory.integral_const_mul (μ := μIoc01)
        (r := cexp (↑(-2 * (π * ⟪x, w⟫)) * I))
        (f := fun t : ℝ ↦
          (I : ℂ) * MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (z₁line t))).symm
  let f : ℝ⁸ → ℝ → ℂ := fun x t => permI1Kernel w (x, t)
  let g : ℝ → ℂ := fun t => (I : ℂ) * Φ₁_fourier (‖w‖ ^ 2) (z₁line t)
  have hint : Integrable (Function.uncurry f) ((volume : Measure ℝ⁸).prod μIoc01) := by
    simpa [f, Function.uncurry] using (integrable_perm_I₁_kernel (w := w))
  have hswapEq :
      (∫ x : ℝ⁸, ∫ t in Ioc (0 : ℝ) 1, f x t) =
        ∫ t in Ioc (0 : ℝ) 1, g t := by
    refine SpherePacking.Integration.integral_integral_swap_Ioc01 (V := ℝ⁸) (f := f) (g := g)
      hint ?_
    intro t ht
    simpa [f] using (integral_permI1Kernel_x (w := w) (t := t) ht)
  -- Put everything together and convert back to a curve integral.
  have hcurve :
      (∫ t in Ioc (0 : ℝ) 1, g t) =
        (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + I),
          scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) := by
    rw [curveIntegral_segment (ω := scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)))
      (-1 : ℂ) ((-1 : ℂ) + I)]
    have hdir : (((-1 : ℂ) + I) - (-1 : ℂ)) = (I : ℂ) :=
      SpherePacking.Contour.dir_z₁line
    simp [g, intervalIntegral.integral_of_le, scalarOneForm_apply, hdir,
      SpherePacking.Contour.lineMap_z₁line]
  calc
    (∫ x : ℝ⁸,
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * MagicFunction.a.RealIntegrals.I₁' (‖x‖ ^ 2)) =
        ∫ x : ℝ⁸,
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            (∫ t in Ioc (0 : ℝ) 1,
              (I : ℂ) * MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (z₁line t)) := by
          refine MeasureTheory.integral_congr_ae ?_
          refine ae_of_all _ ?_
          intro x
          simp [hI₁' x, mul_assoc]
    _ =
        ∫ x : ℝ⁸,
          ∫ t in Ioc (0 : ℝ) 1,
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              ((I : ℂ) * MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (z₁line t)) := by
          exact congrArg (fun F : ℝ⁸ → ℂ => ∫ x : ℝ⁸, F x) hmul
    _ =
        ∫ x : ℝ⁸, ∫ t in Ioc (0 : ℝ) 1, f x t := by
          simp [f, permI1Kernel, mul_assoc]
    _ =
        ∫ t in Ioc (0 : ℝ) 1, (I : ℂ) * Φ₁_fourier (‖w‖ ^ 2) (z₁line t) := hswapEq
    _ =
        (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + I),
          scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) := hcurve

/-- Fourier transform of `I₂`, rewritten as a curve integral of `Φ₁_fourier` along the second
segment. -/
public lemma fourier_I₂_eq_curveIntegral (w : ℝ⁸) :
    (𝓕 (I₂ : ℝ⁸ → ℂ)) w =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + I) I,
        scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) := by
  rw [fourier_eq' (I₂ : ℝ⁸ → ℂ) w]
  simp only [smul_eq_mul, I₂_apply, mul_assoc]
  have hI₂' (x : ℝ⁸) :
      MagicFunction.a.RealIntegrals.I₂' (‖x‖ ^ 2) =
        ∫ t in Ioc (0 : ℝ) 1,
          MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (z₂line t) := by
    rw [I₂'_eq_curveIntegral_segment (r := ‖x‖ ^ 2)]
    rw [curveIntegral_segment
      (ω := scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2)))
      ((-1 : ℂ) + I) I]
    rw [intervalIntegral.integral_of_le (μ := (volume : Measure ℝ))
      (a := (0 : ℝ)) (b := 1) (by norm_num)]
    have hdir : (I - ((-1 : ℂ) + I)) = (1 : ℂ) := SpherePacking.Contour.dir_z₂line
    simp [scalarOneForm_apply, hdir, SpherePacking.Contour.lineMap_z₂line]
  have hmul :
      (fun x : ℝ⁸ ↦
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            (∫ t in Ioc (0 : ℝ) 1,
              MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (z₂line t))) =
        fun x : ℝ⁸ ↦
          ∫ t in Ioc (0 : ℝ) 1,
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (z₂line t) := by
    ext x
    simpa [μIoc01] using
      (MeasureTheory.integral_const_mul (μ := μIoc01)
        (r := cexp (↑(-2 * (π * ⟪x, w⟫)) * I))
        (f := fun t : ℝ ↦ MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (z₂line t))).symm
  let f : ℝ⁸ → ℝ → ℂ := fun x t => permI2Kernel w (x, t)
  let g : ℝ → ℂ := fun t => Φ₁_fourier (‖w‖ ^ 2) (z₂line t)
  have hint : Integrable (Function.uncurry f) ((volume : Measure ℝ⁸).prod μIoc01) := by
    simpa [f, Function.uncurry] using (integrable_perm_I₂_kernel (w := w))
  have hswapEq :
      (∫ x : ℝ⁸, ∫ t in Ioc (0 : ℝ) 1, f x t) =
        ∫ t in Ioc (0 : ℝ) 1, g t := by
    refine SpherePacking.Integration.integral_integral_swap_Ioc01 (V := ℝ⁸) (f := f) (g := g)
      hint ?_
    intro t ht
    simpa [f] using (integral_permI2Kernel_x (w := w) (t := t))
  have hcurve :
      (∫ t in Ioc (0 : ℝ) 1, g t) =
        (∫ᶜ z in Path.segment ((-1 : ℂ) + I) I,
          scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) := by
    rw [curveIntegral_segment (ω := scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)))
      ((-1 : ℂ) + I) I]
    have hdir : (I - ((-1 : ℂ) + I)) = (1 : ℂ) := SpherePacking.Contour.dir_z₂line
    simp [g, intervalIntegral.integral_of_le, scalarOneForm_apply, hdir,
      SpherePacking.Contour.lineMap_z₂line]
  calc
    (∫ x : ℝ⁸,
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * MagicFunction.a.RealIntegrals.I₂' (‖x‖ ^ 2)) =
        ∫ x : ℝ⁸,
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            (∫ t in Ioc (0 : ℝ) 1,
              MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (z₂line t)) := by
          refine MeasureTheory.integral_congr_ae ?_
          refine ae_of_all _ ?_
          intro x
          simp [hI₂' x, mul_assoc]
    _ =
        ∫ x : ℝ⁸,
          ∫ t in Ioc (0 : ℝ) 1,
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (z₂line t) := by
          exact congrArg (fun F : ℝ⁸ → ℂ => ∫ x : ℝ⁸, F x) hmul
    _ =
        ∫ x : ℝ⁸, ∫ t in Ioc (0 : ℝ) 1, f x t := by
          simp [f, permI2Kernel, mul_assoc]
    _ =
        ∫ t in Ioc (0 : ℝ) 1, Φ₁_fourier (‖w‖ ^ 2) (z₂line t) := hswapEq
    _ =
        (∫ᶜ z in Path.segment ((-1 : ℂ) + I) I,
          scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) := hcurve

end Integral_Permutations.PermI12Fourier_Main
end
end MagicFunction.a.Fourier
