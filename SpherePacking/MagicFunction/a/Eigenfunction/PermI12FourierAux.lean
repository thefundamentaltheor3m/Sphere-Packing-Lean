module
public import SpherePacking.MagicFunction.a.Eigenfunction.PermI12Fourier
import SpherePacking.Contour.Segments
import SpherePacking.Contour.GaussianIntegral
import SpherePacking.ForMathlib.GaussianFourierCommon
import Mathlib.Tactic.Ring.RingNF


/-!
# Inner integrals for the `I₁/I₂` kernels

We compute the inner `x`-integrals of `permI1Kernel` and `permI2Kernel`, reducing them to the
Fourier-side integrand `Φ₁_fourier`.

## Main statements
* `integral_permI1Kernel_x`
* `integral_permI2Kernel_x`
-/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter

section Integral_Permutations

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section PermI12Fourier_Aux

open MeasureTheory Set Complex Real
open SpherePacking.ForMathlib
open SpherePacking.Contour
open scoped Interval

/-- The `x`-integral of `permI1Kernel` is `Φ₁_fourier` evaluated at `z₁line t`. -/
public lemma integral_permI1Kernel_x (w : ℝ⁸) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : ℝ⁸, permI1Kernel w (x, t)) =
      (I : ℂ) * Φ₁_fourier (‖w‖ ^ 2) (z₁line t) := by
  have hz : 0 < (z₁line t).im := by
    simpa using (SpherePacking.Contour.z₁line_im_pos_Ioc (t := t) ht)
  let c : ℂ := (I : ℂ) * (φ₀'' (-1 / (z₁line t + 1)) * (z₁line t + 1) ^ 2)
  have hfactor :
      (fun x : ℝ⁸ => permI1Kernel w (x, t)) =
        fun x : ℝ⁸ =>
          c *
            (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z₁line t)) := by
    funext x
    dsimp [permI1Kernel, MagicFunction.a.ComplexIntegrands.Φ₁', c]
    ac_rfl
  have hgauss :=
    SpherePacking.Contour.integral_const_mul_phase_gaussian_pi_mul_I_mul_even
      (k := 4) (w := w) (z := z₁line t) hz (c := c)
  calc
    (∫ x : ℝ⁸, permI1Kernel w (x, t)) =
        c * ((((I : ℂ) / (z₁line t)) ^ (4 : ℕ)) *
          cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z₁line t))) := by
          simpa [hfactor] using hgauss
    _ = (I : ℂ) * Φ₁_fourier (‖w‖ ^ 2) (z₁line t) := by
          simp [c, Φ₁_fourier, mul_assoc, mul_left_comm, mul_comm]

/-- The `x`-integral of `permI2Kernel` is `Φ₁_fourier` evaluated at `z₂line t`. -/
public lemma integral_permI2Kernel_x (w : ℝ⁸) (t : ℝ) :
    (∫ x : ℝ⁸, permI2Kernel w (x, t)) =
      Φ₁_fourier (‖w‖ ^ 2) (z₂line t) := by
  have hz : 0 < (z₂line t).im := by simp
  let c : ℂ := φ₀'' (-1 / (z₂line t + 1)) * (z₂line t + 1) ^ 2
  have hfactor :
      (fun x : ℝ⁸ => permI2Kernel w (x, t)) =
        fun x : ℝ⁸ =>
          c *
            (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z₂line t)) := by
    funext x
    dsimp [permI2Kernel, MagicFunction.a.ComplexIntegrands.Φ₁', c]
    ac_rfl
  have hgauss :=
    SpherePacking.Contour.integral_const_mul_phase_gaussian_pi_mul_I_mul_even
      (k := 4) (w := w) (z := z₂line t) hz (c := c)
  calc
    (∫ x : ℝ⁸, permI2Kernel w (x, t)) =
        c * ((((I : ℂ) / (z₂line t)) ^ (4 : ℕ)) *
          cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z₂line t))) := by
          simpa [hfactor] using hgauss
    _ = Φ₁_fourier (‖w‖ ^ 2) (z₂line t) := by
          simp [c, Φ₁_fourier, mul_assoc, mul_left_comm, mul_comm]

end Integral_Permutations.PermI12Fourier_Aux
end
end MagicFunction.a.Fourier
