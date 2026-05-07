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
-/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter

section Integral_Permutations

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section PermI12Fourier_Main

open MeasureTheory Set Complex Real SpherePacking.Integration SpherePacking.Contour
open MagicFunction.a.RealIntegrals MagicFunction.a.ComplexIntegrands
open scoped Interval

/-- Fourier transform of `I₁`, rewritten as a curve integral of `Φ₁_fourier` along the first
vertical segment. -/
public lemma fourier_I₁_eq_curveIntegral (w : ℝ⁸) :
    (𝓕 (I₁ : ℝ⁸ → ℂ)) w =
      (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + I),
        scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) := by
  rw [fourier_eq' (I₁ : ℝ⁸ → ℂ) w]
  simp only [smul_eq_mul, I₁_apply, mul_assoc]
  have hI₁' (x : ℝ⁸) : RealIntegrals.I₁' (‖x‖ ^ 2) =
      ∫ t in Ioc (0 : ℝ) 1, (I : ℂ) * Φ₁' (‖x‖ ^ 2) (z₁line t) := by
    rw [I₁'_eq_curveIntegral_segment,
      curveIntegral_segment (ω := scalarOneForm (Φ₁' (‖x‖ ^ 2))) (-1 : ℂ) ((-1 : ℂ) + I),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simp [lineMap_z₁line]
  let f : ℝ⁸ → ℝ → ℂ := fun x t => permI1Kernel w (x, t)
  let g : ℝ → ℂ := fun t => (I : ℂ) * Φ₁_fourier (‖w‖ ^ 2) (z₁line t)
  have hswapEq : (∫ x : ℝ⁸, ∫ t in Ioc (0 : ℝ) 1, f x t) = ∫ t in Ioc (0 : ℝ) 1, g t := by
    simpa [μIoc01] using
      integral_integral_swap_muIoc01 (V := ℝ⁸) (f := f) (g := g)
        (integrable_perm_I₁_kernel (w := w)) fun t ht => by
          simpa [f] using integral_permI1Kernel_x (w := w) (t := t) ht
  calc
    (∫ x : ℝ⁸, cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * RealIntegrals.I₁' (‖x‖ ^ 2)) =
        ∫ x : ℝ⁸, ∫ t in Ioc (0 : ℝ) 1,
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * ((I : ℂ) * Φ₁' (‖x‖ ^ 2) (z₁line t)) := by
        simp_rw [hI₁', integral_const_mul]
    _ = ∫ x : ℝ⁸, ∫ t in Ioc (0 : ℝ) 1, f x t := by simp [f, permI1Kernel]
    _ = ∫ t in Ioc (0 : ℝ) 1, (I : ℂ) * Φ₁_fourier (‖w‖ ^ 2) (z₁line t) := hswapEq
    _ = (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + I),
          scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) := by
      rw [curveIntegral_segment (ω := scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)))
        (-1 : ℂ) ((-1 : ℂ) + I)]
      simp [g, intervalIntegral.integral_of_le, lineMap_z₁line]

/-- Fourier transform of `I₂`, rewritten as a curve integral of `Φ₁_fourier` along the second
segment. -/
public lemma fourier_I₂_eq_curveIntegral (w : ℝ⁸) :
    (𝓕 (I₂ : ℝ⁸ → ℂ)) w =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + I) I,
        scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) := by
  rw [fourier_eq' (I₂ : ℝ⁸ → ℂ) w]
  simp only [smul_eq_mul, I₂_apply, mul_assoc]
  have hI₂' (x : ℝ⁸) : RealIntegrals.I₂' (‖x‖ ^ 2) =
      ∫ t in Ioc (0 : ℝ) 1, Φ₁' (‖x‖ ^ 2) (z₂line t) := by
    rw [I₂'_eq_curveIntegral_segment,
      curveIntegral_segment (ω := scalarOneForm (Φ₁' (‖x‖ ^ 2))) ((-1 : ℂ) + I) I,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simp [lineMap_z₂line]
  let f : ℝ⁸ → ℝ → ℂ := fun x t => permI2Kernel w (x, t)
  let g : ℝ → ℂ := fun t => Φ₁_fourier (‖w‖ ^ 2) (z₂line t)
  have hswapEq : (∫ x : ℝ⁸, ∫ t in Ioc (0 : ℝ) 1, f x t) = ∫ t in Ioc (0 : ℝ) 1, g t := by
    simpa [μIoc01] using
      integral_integral_swap_muIoc01 (V := ℝ⁸) (f := f) (g := g)
        (integrable_perm_I₂_kernel (w := w)) fun t _ => by
          simpa [f] using integral_permI2Kernel_x (w := w) (t := t)
  calc
    (∫ x : ℝ⁸, cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * RealIntegrals.I₂' (‖x‖ ^ 2)) =
        ∫ x : ℝ⁸, ∫ t in Ioc (0 : ℝ) 1,
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * Φ₁' (‖x‖ ^ 2) (z₂line t) := by
        simp_rw [hI₂', integral_const_mul]
    _ = ∫ x : ℝ⁸, ∫ t in Ioc (0 : ℝ) 1, f x t := by simp [f, permI2Kernel]
    _ = ∫ t in Ioc (0 : ℝ) 1, Φ₁_fourier (‖w‖ ^ 2) (z₂line t) := hswapEq
    _ = (∫ᶜ z in Path.segment ((-1 : ℂ) + I) I,
          scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) := by
      rw [curveIntegral_segment (ω := scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)))
        ((-1 : ℂ) + I) I]
      simp [g, intervalIntegral.integral_of_le, lineMap_z₂line]

end Integral_Permutations.PermI12Fourier_Main
end
end MagicFunction.a.Fourier
