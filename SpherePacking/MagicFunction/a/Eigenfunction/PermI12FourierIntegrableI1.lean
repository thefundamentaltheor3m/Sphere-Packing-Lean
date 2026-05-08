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

Integrability of `permI1Kernel` on the product measure: slice integrability in `x`, bound on
`t ↦ ∫ ‖kernel‖`, then `integrable_prod_iff'`. Also records a.e. slice integrability for
`permI2Kernel`.
-/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped RealInnerProductSpace

section Integral_Permutations

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section PermI12Fourier_Integrable

open MeasureTheory Set Complex Real
open SpherePacking.ForMathlib SpherePacking.Contour SpherePacking.Integration
open MagicFunction.a.ComplexIntegrands

/-- Closed form for the `ℝ⁸` Gaussian integral used in the kernel bounds. -/
public lemma integral_rexp_neg_pi_mul_sq_norm (t : ℝ) (ht : 0 < t) :
    (∫ x : ℝ⁸, rexp (-Real.pi * t * (‖x‖ ^ 2))) = (1 / t) ^ (4 : ℕ) := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    integral_gaussian_rexp (s := (1 / t)) (by positivity)

/-- For almost every `t ∈ Ioc 0 1`, the slice `x ↦ permI2Kernel w (x, t)` is integrable. -/
public lemma ae_integrable_permI2Kernel_slice (w : ℝ⁸) :
    (∀ᵐ t : ℝ ∂μIoc01, Integrable (fun x : ℝ⁸ ↦ permI2Kernel w (x, t)) (volume : Measure ℝ⁸)) :=
  (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t _ => by
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

lemma integral_norm_permI1Kernel_bound (w : ℝ⁸) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : ℝ⁸, ‖permI1Kernel w (x, t)‖) ≤ ‖φ₀'' ((I : ℂ) / t)‖ * (1 / t ^ 2) := by
  have ht0 : 0 < t := ht.1
  have harg : (-1 / (z₁line t + 1) : ℂ) = (I : ℂ) / t := by
    simpa [z₁line_add_one] using show (-1 / ((I : ℂ) * (t : ℂ)) : ℂ) = (I : ℂ) / t by
      field_simp [ht0.ne']; simp [Complex.I_sq]
  have hexp (x : ℝ⁸) : ‖cexp (Real.pi * I * (‖x‖ ^ 2) * (z₁line t : ℂ))‖ =
      rexp (-(Real.pi * (t * (‖x‖ ^ 2)))) := by
    rw [show ‖cexp (Real.pi * I * (‖x‖ ^ 2) * (z₁line t : ℂ))‖ =
        rexp (-Real.pi * (‖x‖ ^ 2) * t) from by
      simpa [z₁line_im, mul_assoc, mul_left_comm, mul_comm] using
        norm_cexp_pi_mul_I_mul_sq (z := z₁line t) (x := x)]; ring_nf
  have hnorm (x : ℝ⁸) :
      ‖permI1Kernel w (x, t)‖ =
        ‖φ₀'' ((I : ℂ) / t)‖ * t ^ 2 * rexp (-(Real.pi * (t * (‖x‖ ^ 2)))) := calc
    ‖permI1Kernel w (x, t)‖
        = ‖cexp (↑(-2 * (π * ⟪x, w⟫)) * I)‖ *
            ‖(I : ℂ) * Φ₁' (‖x‖ ^ 2) (z₁line t)‖ := by simp [permI1Kernel, mul_assoc]
      _ = ‖Φ₁' (‖x‖ ^ 2) (z₁line t)‖ := by simp [show ‖cexp (-(2 * (↑π * ↑⟪x, w⟫) * I))‖ = (1 : ℝ)
            from by simpa [mul_assoc, mul_left_comm, mul_comm] using
              norm_phase_eq_one (w := w) (x := x)]
      _ = ‖φ₀'' (-1 / (z₁line t + 1))‖ * ‖(z₁line t + 1) ^ 2‖ *
            ‖cexp (Real.pi * I * (‖x‖ ^ 2) * (z₁line t : ℂ))‖ := by simp [Φ₁', mul_assoc]
      _ = ‖φ₀'' ((I : ℂ) / t)‖ * t ^ 2 * rexp (-(Real.pi * (t * (‖x‖ ^ 2)))) := by
            rw [harg, show ‖(z₁line t + 1) ^ 2‖ = t ^ 2 by simp, hexp x]
  refine le_of_eq ?_
  rw [show (fun x : ℝ⁸ => ‖permI1Kernel w (x, t)‖) =
        fun x : ℝ⁸ => ‖φ₀'' ((I : ℂ) / t)‖ * t ^ 2 * rexp (-(Real.pi * (t * (‖x‖ ^ 2)))) from
      funext hnorm, integral_const_mul,
    show (∫ x : ℝ⁸, rexp (-(Real.pi * (t * (‖x‖ ^ 2))))) = (1 / t) ^ (4 : ℕ) from by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        integral_rexp_neg_pi_mul_sq_norm (t := t) ht0]
  field_simp

lemma integrable_integral_norm_permI1Kernel (w : ℝ⁸) :
    Integrable (fun t : ℝ ↦ ∫ x : ℝ⁸, ‖permI1Kernel w (x, t)‖) μIoc01 := by
  obtain ⟨C₀, _, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  have hmajor :
      Integrable (fun t : ℝ ↦ (C₀ : ℝ) * (1 / t ^ 2) * rexp (-(2 * π) / t)) μIoc01 := by
    simpa [μIoc01, IntegrableOn, mul_assoc, mul_left_comm, mul_comm] using
      ((show IntegrableOn (fun t : ℝ ↦ (1 / t ^ 2) * rexp (-(2 * π) / t)) (Ioc (0 : ℝ) 1) volume by
        simpa [div_eq_mul_inv] using
          integrableOn_one_div_sq_mul_exp_neg_div (c := (2 * π)) (by positivity)).const_mul C₀)
  refine Integrable.mono' hmajor (by
    simpa using ((permI1Kernel_measurable w).norm.prod_swap.integral_prod_right'
      (μ := μIoc01) (ν := (volume : Measure ℝ⁸)))) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => ?_
  have ht0 : 0 < t := ht.1
  have hzpos : 0 < ((I : ℂ) / t).im := by
    simpa [show ((I : ℂ) / t).im = t⁻¹ by norm_num] using inv_pos.2 ht0
  let z : UpperHalfPlane := ⟨(I : ℂ) / t, hzpos⟩
  have hz_im : z.im = t⁻¹ := by simp [z, UpperHalfPlane.im]
  have hφ_bound : ‖φ₀'' ((I : ℂ) / t)‖ ≤ (C₀ : ℝ) * rexp (-(2 * π) / t) := by
    simpa [show φ₀ z = φ₀'' ((I : ℂ) / t) from by
        simpa [z] using (φ₀''_def (z := (I : ℂ) / t) hzpos).symm,
      show rexp (-(2 * π * z.im)) = rexp (-(2 * π) / t) by
        rw [hz_im]; congr 1; simp [div_eq_mul_inv, mul_assoc]] using
      hC₀ z (by rw [hz_im]
                exact lt_of_lt_of_le (by norm_num) (one_le_inv_iff₀.2 ⟨ht0, ht.2⟩))
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (integral_norm_permI1Kernel_bound (w := w) (t := t) ht).trans
      (mul_le_mul_of_nonneg_right hφ_bound (by positivity))

/-- Integrability of `permI1Kernel` on the product measure `volume × μIoc01`. -/
public lemma integrable_perm_I₁_kernel (w : ℝ⁸) :
    Integrable (permI1Kernel w) ((volume : Measure ℝ⁸).prod μIoc01) :=
  (integrable_prod_iff' (μ := (volume : Measure ℝ⁸)) (ν := μIoc01) (permI1Kernel_measurable w)).2
    ⟨(ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => by
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
      simpa [phase, g, permI1Kernel, permI5Phase, mul_assoc] using hprod,
      integrable_integral_norm_permI1Kernel w⟩

end Integral_Permutations.PermI12Fourier_Integrable
end
end MagicFunction.a.Fourier
