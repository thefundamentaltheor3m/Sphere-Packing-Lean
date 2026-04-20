module

public import SpherePacking.MagicFunction.a.Eigenfunction.PermI12Fourier
public import SpherePacking.MagicFunction.a.Eigenfunction.PermI5Kernel

import SpherePacking.Contour.Segments
import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.ForMathlib.FourierPhase
import SpherePacking.ForMathlib.GaussianRexpIntegral
import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.Integration.EndpointIntegrability

/-!
# Integrability of the `I₁/I₂` Fourier kernels (I1 side)

We prove integrability on the product measure for the kernel `permI1Kernel`, following the same
pattern as for `permI5Kernel`: slice integrability in `x`, bounds on `t ↦ ∫ ‖kernel‖`, and then
`integrable_prod_iff'`.

We also record the a.e. slice integrability statement for `permI2Kernel`, which is used in the
companion file for the `I₂` kernel.

## Main statements
* `integrable_perm_I₁_kernel`
* `ae_integrable_permI2Kernel_slice`
-/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped RealInnerProductSpace

section Integral_Permutations

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section PermI12Fourier_Integrable

open MeasureTheory Set Complex Real
open SpherePacking.ForMathlib
open SpherePacking.Contour
open SpherePacking.Integration
open MagicFunction.a.ComplexIntegrands

/-- A closed form for the `ℝ⁸` Gaussian integral used in the kernel bounds. -/
public lemma integral_rexp_neg_pi_mul_sq_norm (t : ℝ) (ht : 0 < t) :
    (∫ x : ℝ⁸, rexp (-Real.pi * t * (‖x‖ ^ 2))) = (1 / t) ^ (4 : ℕ) := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    integral_gaussian_rexp (s := (1 / t)) (by positivity)

lemma integrable_permI1Kernel_slice (w : ℝ⁸) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun x : ℝ⁸ ↦ permI1Kernel w (x, t)) (volume : Measure ℝ⁸) := by
  have hz : 0 < (z₁line t).im := by simpa using z₁line_im_pos_Ioc (t := t) ht
  let phase : ℝ⁸ → ℂ := fun x : ℝ⁸ ↦ cexp (↑(-2 * (π * ⟪x, w⟫)) * I)
  let g : ℝ⁸ → ℂ := fun x : ℝ⁸ ↦ (I : ℂ) * Φ₁' (‖x‖ ^ 2) (z₁line t)
  have hg : Integrable g (volume : Measure ℝ⁸) := by
    have hc : Integrable (fun x : ℝ⁸ ↦
        ((I : ℂ) * (φ₀'' (-1 / (z₁line t + 1)) * (z₁line t + 1) ^ 2)) *
          cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * z₁line t)) (volume : Measure ℝ⁸) :=
      (integrable_gaussian_cexp_pi_mul_I_mul (z := z₁line t) hz).const_mul _
    simpa [g, Φ₁', mul_assoc] using hc
  have hprod : Integrable (fun x : ℝ⁸ ↦ phase x * g x) (volume : Measure ℝ⁸) :=
    hg.bdd_mul (c := (1 : ℝ))
      (by simpa [phase] using aestronglyMeasurable_phase (V := ℝ⁸) (w := w))
      (by simpa [phase] using ae_norm_phase_le_one (V := ℝ⁸) (w := w))
  simpa [phase, g, permI1Kernel, permI5Phase, mul_assoc] using hprod

lemma integrable_permI2Kernel_slice (w : ℝ⁸) (t : ℝ) :
    Integrable (fun x : ℝ⁸ ↦ permI2Kernel w (x, t)) (volume : Measure ℝ⁸) := by
  have hz : 0 < (z₂line t).im := by simp
  let phase : ℝ⁸ → ℂ := fun x : ℝ⁸ ↦ cexp (↑(-2 * (π * ⟪x, w⟫)) * I)
  let g : ℝ⁸ → ℂ := fun x : ℝ⁸ ↦ Φ₁' (‖x‖ ^ 2) (z₂line t)
  have hg : Integrable g (volume : Measure ℝ⁸) := by
    have hc : Integrable (fun x : ℝ⁸ ↦
        (φ₀'' (-1 / (z₂line t + 1)) * (z₂line t + 1) ^ 2) *
          cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * z₂line t)) (volume : Measure ℝ⁸) :=
      (integrable_gaussian_cexp_pi_mul_I_mul (z := z₂line t) hz).const_mul _
    simpa [g, Φ₁'] using hc
  have hprod : Integrable (fun x : ℝ⁸ ↦ phase x * g x) (volume : Measure ℝ⁸) :=
    hg.bdd_mul (c := (1 : ℝ))
      (by simpa [phase] using aestronglyMeasurable_phase (V := ℝ⁸) (w := w))
      (by simpa [phase] using ae_norm_phase_le_one (V := ℝ⁸) (w := w))
  simpa [phase, g, permI2Kernel, permI5Phase, mul_assoc] using hprod

lemma ae_integrable_permI1Kernel_slice (w : ℝ⁸) :
    (∀ᵐ t : ℝ ∂μIoc01, Integrable (fun x : ℝ⁸ ↦ permI1Kernel w (x, t)) (volume : Measure ℝ⁸)) :=
  (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht =>
    integrable_permI1Kernel_slice (w := w) (t := t) ht

/-- For almost every `t ∈ Ioc 0 1`, the slice `x ↦ permI2Kernel w (x, t)` is integrable. -/
public lemma ae_integrable_permI2Kernel_slice (w : ℝ⁸) :
    (∀ᵐ t : ℝ ∂μIoc01, Integrable (fun x : ℝ⁸ ↦ permI2Kernel w (x, t)) (volume : Measure ℝ⁸)) :=
  (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t _ =>
    integrable_permI2Kernel_slice (w := w) (t := t)

lemma integral_norm_permI1Kernel_bound (w : ℝ⁸) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : ℝ⁸, ‖permI1Kernel w (x, t)‖) ≤ ‖φ₀'' ((I : ℂ) / t)‖ * (1 / t ^ 2) := by
  have ht0 : 0 < t := ht.1
  have harg : (-1 / (z₁line t + 1) : ℂ) = (I : ℂ) / t := by
    have : (-1 / ((I : ℂ) * (t : ℂ)) : ℂ) = (I : ℂ) / t := by
      field_simp [ht0.ne']; simp [Complex.I_sq]
    simpa [z₁line_add_one] using this
  have hexp (x : ℝ⁸) :
      ‖cexp (Real.pi * I * (‖x‖ ^ 2) * (z₁line t : ℂ))‖ =
        rexp (-(Real.pi * (t * (‖x‖ ^ 2)))) := by
    have h' : ‖cexp (Real.pi * I * (‖x‖ ^ 2) * (z₁line t : ℂ))‖ =
        rexp (-Real.pi * (‖x‖ ^ 2) * t) := by
      simpa [z₁line_im, mul_assoc, mul_left_comm, mul_comm] using
        norm_cexp_pi_mul_I_mul_sq (z := z₁line t) (x := x)
    rw [h']; congr 1; ring
  have hnorm (x : ℝ⁸) :
      ‖permI1Kernel w (x, t)‖ =
        ‖φ₀'' ((I : ℂ) / t)‖ * t ^ 2 * rexp (-(Real.pi * (t * (‖x‖ ^ 2)))) := by
    have hphase : ‖cexp (-(2 * (↑π * ↑⟪x, w⟫) * I))‖ = (1 : ℝ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using norm_phase_eq_one (w := w) (x := x)
    calc ‖permI1Kernel w (x, t)‖
        = ‖cexp (↑(-2 * (π * ⟪x, w⟫)) * I)‖ *
            ‖(I : ℂ) * Φ₁' (‖x‖ ^ 2) (z₁line t)‖ := by simp [permI1Kernel, mul_assoc]
      _ = ‖Φ₁' (‖x‖ ^ 2) (z₁line t)‖ := by simp [hphase]
      _ = ‖φ₀'' (-1 / (z₁line t + 1))‖ * ‖(z₁line t + 1) ^ 2‖ *
            ‖cexp (Real.pi * I * (‖x‖ ^ 2) * (z₁line t : ℂ))‖ := by simp [Φ₁', mul_assoc]
      _ = ‖φ₀'' ((I : ℂ) / t)‖ * t ^ 2 * rexp (-(Real.pi * (t * (‖x‖ ^ 2)))) := by
            rw [harg, show ‖(z₁line t + 1) ^ 2‖ = t ^ 2 by simp, hexp x]
  have hgauss_int :
      (∫ x : ℝ⁸, rexp (-(Real.pi * (t * (‖x‖ ^ 2))))) = (1 / t) ^ (4 : ℕ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      integral_rexp_neg_pi_mul_sq_norm (t := t) ht0
  refine le_of_eq ?_
  calc (∫ x : ℝ⁸, ‖permI1Kernel w (x, t)‖)
      = ∫ x : ℝ⁸, ‖φ₀'' ((I : ℂ) / t)‖ * t ^ 2 * rexp (-(Real.pi * (t * (‖x‖ ^ 2)))) := by
        simp only [funext hnorm]
    _ = ‖φ₀'' ((I : ℂ) / t)‖ * t ^ 2 * ∫ x : ℝ⁸, rexp (-(Real.pi * (t * (‖x‖ ^ 2)))) :=
        integral_const_mul _ _
    _ = ‖φ₀'' ((I : ℂ) / t)‖ * (1 / t ^ 2) := by
        rw [hgauss_int, mul_assoc]; field_simp

lemma integrable_integral_norm_permI1Kernel (w : ℝ⁸) :
    Integrable (fun t : ℝ ↦ ∫ x : ℝ⁸, ‖permI1Kernel w (x, t)‖) μIoc01 := by
  -- Majorize by `C₀ * (1/t^2) * exp(-2π/t)`.
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  have hmajor :
      Integrable (fun t : ℝ ↦ (C₀ : ℝ) * (1 / t ^ 2) * rexp (-(2 * π) / t)) μIoc01 := by
    have hI : IntegrableOn
        (fun t : ℝ ↦ (1 / t ^ 2) * rexp (-(2 * π) / t)) (Ioc (0 : ℝ) 1) volume := by
      simpa [div_eq_mul_inv] using
        integrableOn_one_div_sq_mul_exp_neg_div (c := (2 * π)) (by positivity)
    simpa [μIoc01, IntegrableOn, mul_assoc, mul_left_comm, mul_comm] using hI.const_mul C₀
  have hmeas :
      AEStronglyMeasurable (fun t : ℝ ↦ ∫ x : ℝ⁸, ‖permI1Kernel w (x, t)‖) μIoc01 := by
    simpa using ((permI1Kernel_measurable (w := w)).norm.prod_swap.integral_prod_right'
      (μ := μIoc01) (ν := (volume : Measure ℝ⁸)))
  refine Integrable.mono' hmajor hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => ?_
  have ht0 : 0 < t := ht.1
  have him : ((I : ℂ) / t).im = t⁻¹ := by norm_num
  have hzpos : 0 < ((I : ℂ) / t).im := by simpa [him] using inv_pos.2 ht0
  let z : UpperHalfPlane := ⟨(I : ℂ) / t, hzpos⟩
  have hz_im : z.im = t⁻¹ := by simp [z, UpperHalfPlane.im, him]
  have hz_half : (1 / 2 : ℝ) < z.im := by
    rw [hz_im]
    exact lt_of_lt_of_le (by norm_num) (one_le_inv_iff₀.2 ⟨ht0, ht.2⟩)
  have hφ_bound : ‖φ₀'' ((I : ℂ) / t)‖ ≤ (C₀ : ℝ) * rexp (-(2 * π) / t) := by
    have hrew : rexp (-(2 * π * z.im)) = rexp (-(2 * π) / t) := by
      rw [hz_im]; congr 1; simp [div_eq_mul_inv, mul_assoc]
    have hφ₀_eq : φ₀ z = φ₀'' ((I : ℂ) / t) := by
      simpa [z] using (φ₀''_def (z := (I : ℂ) / t) hzpos).symm
    simpa [hφ₀_eq, hrew] using hC₀ z hz_half
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (integral_norm_permI1Kernel_bound (w := w) (t := t) ht).trans
      (mul_le_mul_of_nonneg_right hφ_bound (by positivity))

/-- Integrability of `permI1Kernel` on the product measure `volume × μIoc01`. -/
public lemma integrable_perm_I₁_kernel (w : ℝ⁸) :
    Integrable (permI1Kernel w) ((volume : Measure ℝ⁸).prod μIoc01) :=
  (integrable_prod_iff' (μ := (volume : Measure ℝ⁸)) (ν := μIoc01)
    (permI1Kernel_measurable (w := w))).2
    ⟨ae_integrable_permI1Kernel_slice (w := w), integrable_integral_norm_permI1Kernel (w := w)⟩

end Integral_Permutations.PermI12Fourier_Integrable
end
end MagicFunction.a.Fourier
