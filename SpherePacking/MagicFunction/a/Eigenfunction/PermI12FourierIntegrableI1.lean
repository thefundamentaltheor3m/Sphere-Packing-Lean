module
public import SpherePacking.MagicFunction.a.Eigenfunction.PermI12Fourier
public import SpherePacking.MagicFunction.a.Eigenfunction.PermI5Kernel
import SpherePacking.Contour.Segments
import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.ForMathlib.FourierPhase
import SpherePacking.ForMathlib.GaussianRexpIntegral
import SpherePacking.ForMathlib.IntegralProd
import SpherePacking.MagicFunction.PolyFourierCoeffBound
import Mathlib.Tactic.Ring.RingNF
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

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter

section Integral_Permutations

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section PermI12Fourier_Integrable

open MeasureTheory Set Complex Real
open SpherePacking.ForMathlib
open SpherePacking.Integration
open scoped Interval

/-- A closed form for the `ℝ⁸` Gaussian integral used in the kernel bounds. -/
public lemma integral_rexp_neg_pi_mul_sq_norm (t : ℝ) (ht : 0 < t) :
    (∫ x : ℝ⁸, rexp (-Real.pi * t * (‖x‖ ^ 2))) = (1 / t) ^ (4 : ℕ) := by
  have hs : 0 < (1 / t) := by positivity
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (SpherePacking.ForMathlib.integral_gaussian_rexp (s := (1 / t)) hs)

lemma integrable_permI1Kernel_slice (w : ℝ⁸) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun x : ℝ⁸ ↦ permI1Kernel w (x, t)) (volume : Measure ℝ⁸) := by
  have hz : 0 < (SpherePacking.Contour.z₁line t).im := by
    simpa using (SpherePacking.Contour.z₁line_im_pos_Ioc (t := t) ht)
  let phase : ℝ⁸ → ℂ := fun x : ℝ⁸ ↦ cexp (↑(-2 * (π * ⟪x, w⟫)) * I)
  let g : ℝ⁸ → ℂ :=
    fun x : ℝ⁸ ↦
      (I : ℂ) *
        MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (SpherePacking.Contour.z₁line t)
  have hg : Integrable g (volume : Measure ℝ⁸) := by
    let c : ℂ := (I : ℂ) * (φ₀'' (-1 / (SpherePacking.Contour.z₁line t + 1)) *
      (SpherePacking.Contour.z₁line t + 1) ^ 2)
    have hc :
        Integrable (fun x : ℝ⁸ ↦ c * cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) *
          SpherePacking.Contour.z₁line t))
          (volume : Measure ℝ⁸) :=
      (integrable_gaussian_cexp_pi_mul_I_mul (z := SpherePacking.Contour.z₁line t) hz).const_mul c
    have hg' :
        g = fun x : ℝ⁸ ↦ c * cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) *
          SpherePacking.Contour.z₁line t) := by
      funext x
      simp [g, c, MagicFunction.a.ComplexIntegrands.Φ₁', mul_assoc]
    simpa [hg'] using hc
  have hprod : Integrable (fun x : ℝ⁸ ↦ phase x * g x) (volume : Measure ℝ⁸) :=
    Integrable.bdd_mul (hg := hg) (f := phase) (g := g) (c := (1 : ℝ))
      (by simpa [phase] using (aestronglyMeasurable_phase (V := ℝ⁸) (w := w)))
      (by simpa [phase] using (ae_norm_phase_le_one (V := ℝ⁸) (w := w)))
  simpa [phase, g, permI1Kernel, permI5Phase, mul_assoc] using hprod

lemma integrable_permI2Kernel_slice (w : ℝ⁸) (t : ℝ) :
    Integrable (fun x : ℝ⁸ ↦ permI2Kernel w (x, t)) (volume : Measure ℝ⁸) := by
  have hz : 0 < (SpherePacking.Contour.z₂line t).im := by simp
  let phase : ℝ⁸ → ℂ := fun x : ℝ⁸ ↦ cexp (↑(-2 * (π * ⟪x, w⟫)) * I)
  let g : ℝ⁸ → ℂ := fun x : ℝ⁸ ↦
    MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (SpherePacking.Contour.z₂line t)
  have hg : Integrable g (volume : Measure ℝ⁸) := by
    let c : ℂ := φ₀'' (-1 / (SpherePacking.Contour.z₂line t + 1)) *
      (SpherePacking.Contour.z₂line t + 1) ^ 2
    have hc :
        Integrable (fun x : ℝ⁸ ↦ c * cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) *
          SpherePacking.Contour.z₂line t))
          (volume : Measure ℝ⁸) :=
      (integrable_gaussian_cexp_pi_mul_I_mul (z := SpherePacking.Contour.z₂line t) hz).const_mul c
    assumption
  have hprod : Integrable (fun x : ℝ⁸ ↦ phase x * g x) (volume : Measure ℝ⁸) :=
    Integrable.bdd_mul (hg := hg) (f := phase) (g := g) (c := (1 : ℝ))
      (by simpa [phase] using (aestronglyMeasurable_phase (V := ℝ⁸) (w := w)))
      (by simpa [phase] using (ae_norm_phase_le_one (V := ℝ⁸) (w := w)))
  simpa [phase, g, permI2Kernel, permI5Phase, mul_assoc] using hprod

lemma ae_integrable_permI1Kernel_slice (w : ℝ⁸) :
    (∀ᵐ t : ℝ ∂μIoc01, Integrable (fun x : ℝ⁸ ↦ permI1Kernel w (x, t)) (volume : Measure ℝ⁸)) := by
  refine (ae_restrict_iff' measurableSet_Ioc).2 <| Filter.Eventually.of_forall ?_
  intro t ht
  exact integrable_permI1Kernel_slice (w := w) (t := t) ht

/-- For almost every `t ∈ Ioc 0 1`, the slice `x ↦ permI2Kernel w (x, t)` is integrable. -/
public lemma ae_integrable_permI2Kernel_slice (w : ℝ⁸) :
    (∀ᵐ t : ℝ ∂μIoc01, Integrable (fun x : ℝ⁸ ↦ permI2Kernel w (x, t)) (volume : Measure ℝ⁸)) := by
  refine (ae_restrict_iff' measurableSet_Ioc).2 <| Filter.Eventually.of_forall ?_
  intro t ht
  exact integrable_permI2Kernel_slice (w := w) (t := t)

lemma integral_norm_permI1Kernel_bound (w : ℝ⁸) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : ℝ⁸, ‖permI1Kernel w (x, t)‖) ≤ ‖φ₀'' ((I : ℂ) / t)‖ * (1 / t ^ 2) := by
  have ht0 : 0 < t := ht.1
  have ht_ne0 : t ≠ 0 := ht0.ne'
  have hz_im : (SpherePacking.Contour.z₁line t).im = t := SpherePacking.Contour.z₁line_im (t := t)
  have hz_add1 : SpherePacking.Contour.z₁line t + 1 = (I : ℂ) * (t : ℂ) :=
    SpherePacking.Contour.z₁line_add_one (t := t)
  have harg : (-1 / (SpherePacking.Contour.z₁line t + 1) : ℂ) = (I : ℂ) / t := by
    have : (-1 / ((I : ℂ) * (t : ℂ)) : ℂ) = (I : ℂ) / t := by
      field_simp [ht_ne0]
      simp [Complex.I_sq]
    simpa [hz_add1] using this
  have hpow : ‖(SpherePacking.Contour.z₁line t + 1) ^ 2‖ = t ^ 2 := by
    have ht0' : 0 ≤ t := ht0.le
    calc
      ‖(SpherePacking.Contour.z₁line t + 1) ^ 2‖ = ‖(I : ℂ) * (t : ℂ)‖ ^ 2 := by
        simp [norm_pow]
      _ = ‖(t : ℂ)‖ ^ 2 := by simp [norm_I]
      _ = t ^ 2 := by simp [Complex.norm_real, abs_of_nonneg ht0']
  have hexp (x : ℝ⁸) :
      ‖cexp (Real.pi * I * (‖x‖ ^ 2) * (SpherePacking.Contour.z₁line t : ℂ))‖ =
        rexp (-(Real.pi * (t * (‖x‖ ^ 2)))) := by
    have h' :
        ‖cexp (Real.pi * I * (‖x‖ ^ 2) * (SpherePacking.Contour.z₁line t : ℂ))‖ =
          rexp (-Real.pi * (‖x‖ ^ 2) * t) := by
      simpa [hz_im, mul_assoc, mul_left_comm, mul_comm] using
        (norm_cexp_pi_mul_I_mul_sq (z := SpherePacking.Contour.z₁line t) (x := x))
    have : rexp (-Real.pi * (‖x‖ ^ 2) * t) = rexp (-(Real.pi * (t * (‖x‖ ^ 2)))) := by
      congr 1
      ring
    exact h'.trans this
  have hnorm (x : ℝ⁸) :
      ‖permI1Kernel w (x, t)‖ =
        ‖φ₀'' ((I : ℂ) / t)‖ * t ^ 2 * rexp (-(Real.pi * (t * (‖x‖ ^ 2)))) := by
    have hphase : ‖cexp (↑(-2 * (π * ⟪x, w⟫)) * I)‖ = (1 : ℝ) := by
      simpa [permI5Phase] using norm_phase_eq_one (w := w) (x := x)
    have hphase' : ‖cexp (-(2 * (↑π * ↑⟪x, w⟫) * I))‖ = (1 : ℝ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hphase
    calc
      ‖permI1Kernel w (x, t)‖
          = ‖cexp (↑(-2 * (π * ⟪x, w⟫)) * I)‖ *
              ‖(I : ℂ) * MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2)
                (SpherePacking.Contour.z₁line t)‖ := by
            simp [permI1Kernel, mul_assoc]
      _ =
          ‖(I : ℂ) * MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2)
            (SpherePacking.Contour.z₁line t)‖ := by
            simp [hphase']
      _ = ‖MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (SpherePacking.Contour.z₁line t)‖ := by
            simp
      _ = ‖φ₀'' (-1 / (SpherePacking.Contour.z₁line t + 1))‖ *
            ‖(SpherePacking.Contour.z₁line t + 1) ^ 2‖ *
              ‖cexp (Real.pi * I * (‖x‖ ^ 2) * (SpherePacking.Contour.z₁line t : ℂ))‖ := by
            simp [MagicFunction.a.ComplexIntegrands.Φ₁', mul_assoc]
      _ = ‖φ₀'' ((I : ℂ) / t)‖ * t ^ 2 * rexp (-(Real.pi * (t * (‖x‖ ^ 2)))) := by
            rw [harg, hpow, hexp x]
            -- goal is closed by rewriting
  -- integrate the explicit norm formula
  have hgauss_int :
      (∫ x : ℝ⁸, rexp (-(Real.pi * (t * (‖x‖ ^ 2))))) = (1 / t) ^ (4 : ℕ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (integral_rexp_neg_pi_mul_sq_norm (t := t) ht0)
  have hEq :
      (∫ x : ℝ⁸, ‖permI1Kernel w (x, t)‖) = ‖φ₀'' ((I : ℂ) / t)‖ * (1 / t ^ 2) := by
    calc
      (∫ x : ℝ⁸, ‖permI1Kernel w (x, t)‖)
          = ∫ x : ℝ⁸, ‖φ₀'' ((I : ℂ) / t)‖ * t ^ 2 * rexp (-(Real.pi * (t * (‖x‖ ^ 2)))) := by
            refine congrArg (fun f : (ℝ⁸ → ℝ) => ∫ x : ℝ⁸, f x) ?_
            ext x
            exact hnorm x
      _ = ‖φ₀'' ((I : ℂ) / t)‖ * ∫ x : ℝ⁸, t ^ 2 * rexp (-(Real.pi * (t * (‖x‖ ^ 2)))) := by
            simpa [mul_assoc] using
              (MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ⁸))
                (r := ‖φ₀'' ((I : ℂ) / t)‖)
                (f := fun x : ℝ⁸ ↦ t ^ 2 * rexp (-(Real.pi * (t * (‖x‖ ^ 2))))))
      _ = ‖φ₀'' ((I : ℂ) / t)‖ * (t ^ 2 * ∫ x : ℝ⁸, rexp (-(Real.pi * (t * (‖x‖ ^ 2))))) := by
            rw [integral_const_mul]
      _ = ‖φ₀'' ((I : ℂ) / t)‖ * (t ^ 2 * (1 / t) ^ (4 : ℕ)) := by
            rw [hgauss_int]
      _ = ‖φ₀'' ((I : ℂ) / t)‖ * (1 / t ^ 2) := by
            field_simp [ht_ne0]
  exact le_of_eq hEq

lemma integrable_integral_norm_permI1Kernel (w : ℝ⁸) :
    Integrable (fun t : ℝ ↦ ∫ x : ℝ⁸, ‖permI1Kernel w (x, t)‖) μIoc01 := by
  -- Majorize by `C₀ * (1/t^2) * exp(-2π/t)`.
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  have hmajor :
      Integrable (fun t : ℝ ↦ (C₀ : ℝ) * (1 / t ^ 2) * rexp (-(2 * π) / t)) μIoc01 := by
    have h0 :
        IntegrableOn (fun t : ℝ ↦ (1 / t ^ 2) * rexp (-(2 * π) / t)) (Ioc (0 : ℝ) 1) volume := by
      simpa [div_eq_mul_inv] using
        (SpherePacking.Integration.integrableOn_one_div_sq_mul_exp_neg_div
          (c := (2 * π)) (by positivity))
    have h0' :
        IntegrableOn
          (fun t : ℝ ↦ (C₀ : ℝ) * ((1 / t ^ 2) * rexp (-(2 * π) / t)))
          (Ioc (0 : ℝ) 1) volume := h0.const_mul C₀
    simpa [μIoc01, IntegrableOn, mul_assoc, mul_left_comm, mul_comm] using h0'
  have hmeas :
      AEStronglyMeasurable (fun t : ℝ ↦ ∫ x : ℝ⁸, ‖permI1Kernel w (x, t)‖) μIoc01 := by
    have hker :
        AEStronglyMeasurable (permI1Kernel w) ((volume : Measure ℝ⁸).prod μIoc01) :=
      permI1Kernel_measurable (w := w)
    simpa using
      (SpherePacking.ForMathlib.aestronglyMeasurable_integral_norm_prod_right'
        (μ := μIoc01) (ν := (volume : Measure ℝ⁸)) (f := permI1Kernel w) hker)
  refine Integrable.mono' hmajor hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall ?_
  intro t ht
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have him : ((I : ℂ) / t).im = t⁻¹ := by
    norm_num
  have hzpos : 0 < ((I : ℂ) / t).im := by
    simpa [him] using (inv_pos.2 ht0)
  let z : UpperHalfPlane := ⟨(I : ℂ) / t, hzpos⟩
  have hz_im : z.im = t⁻¹ := by
    simp [z, UpperHalfPlane.im, him]
  have hz_half : (1 / 2 : ℝ) < z.im := by
    have ht_inv : (1 : ℝ) ≤ t⁻¹ := (one_le_inv_iff₀.2 ⟨ht0, ht1⟩)
    have : (1 / 2 : ℝ) < t⁻¹ := lt_of_lt_of_le (by norm_num) ht_inv
    simpa [hz_im] using this
  have hφ₀ : ‖φ₀ z‖ ≤ (C₀ : ℝ) * rexp (-2 * π * z.im) := hC₀ z hz_half
  have hφ₀_eq : φ₀ z = φ₀'' ((I : ℂ) / t) := by
    simpa [z] using (φ₀''_def (z := (I : ℂ) / t) hzpos).symm
  have hφ_bound :
      ‖φ₀'' ((I : ℂ) / t)‖ ≤ (C₀ : ℝ) * rexp (-(2 * π) / t) := by
    have hrew : rexp (-(2 * π * z.im)) = rexp (-(2 * π) / t) := by
      congr 1
      rw [hz_im]
      simp [div_eq_mul_inv, mul_assoc]
    simpa [hφ₀_eq, hrew] using hφ₀
  have hkernel := integral_norm_permI1Kernel_bound (w := w) (t := t) ht
  have hn0 : 0 ≤ ∫ x : ℝ⁸, ‖permI1Kernel w (x, t)‖ := by
    exact MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  have habs :
      ‖∫ x : ℝ⁸, ‖permI1Kernel w (x, t)‖‖ =
        ∫ x : ℝ⁸, ‖permI1Kernel w (x, t)‖ := by
    simp [Real.norm_eq_abs, abs_of_nonneg hn0]
  have : ∫ x : ℝ⁸, ‖permI1Kernel w (x, t)‖ ≤
      (C₀ : ℝ) * (1 / t ^ 2) * rexp (-(2 * π) / t) := by
    have := hkernel.trans (mul_le_mul_of_nonneg_right hφ_bound (by positivity))
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  -- turn the estimate into an estimate without the outer norm
  simpa [habs] using this

/-- Integrability of `permI1Kernel` on the product measure `volume × μIoc01`. -/
public lemma integrable_perm_I₁_kernel (w : ℝ⁸) :
    Integrable (permI1Kernel w) ((volume : Measure ℝ⁸).prod μIoc01) := by
  have hmeas :
      AEStronglyMeasurable (permI1Kernel w) ((volume : Measure ℝ⁸).prod μIoc01) :=
    permI1Kernel_measurable (w := w)
  refine
    (MeasureTheory.integrable_prod_iff' (μ := (volume : Measure ℝ⁸)) (ν := μIoc01) hmeas).2 ?_
  exact ⟨ae_integrable_permI1Kernel_slice (w := w), integrable_integral_norm_permI1Kernel (w := w)⟩


end Integral_Permutations.PermI12Fourier_Integrable
end
end MagicFunction.a.Fourier
