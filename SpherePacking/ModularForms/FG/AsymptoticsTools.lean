module
public import SpherePacking.ModularForms.FG.Basic


/-!
# Asymptotics tools for `L₁₀`

This file contains small analytic lemmas used in the asymptotics argument for `L₁₀` along the
imaginary axis.

## Main declarations
* `tendsto_ofComplex_I_mul_atTop_atImInfty`
* `mdifferentiable_cexp_mul`, `D_cexp_mul`
* `ResToImagAxis.Real.D_of_real`
-/

open scoped Real Manifold Topology ModularForm
open Filter Complex UpperHalfPlane ModularForm

/-!
## Basic convergence and differentiability lemmas
-/

/-- As `t → ∞`, the point `i * t` tends to `atImInfty` in `ℍ`. -/
public lemma tendsto_ofComplex_I_mul_atTop_atImInfty :
    Tendsto (fun t : ℝ =>
      (UpperHalfPlane.ofComplex (Complex.I * t))) atTop UpperHalfPlane.atImInfty := by
  refine UpperHalfPlane.tendsto_comap_im_ofComplex.comp ?_
  refine (tendsto_comap_iff.2 ?_)
  have hEq : (Complex.im ∘ fun t : ℝ => (Complex.I : ℂ) * t) = (fun t : ℝ => t) := by
    funext t
    simp [Function.comp]
  simpa [hEq] using (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)

/-- The map `z ↦ cexp (c * z)` is holomorphic on the upper half-plane. -/
public lemma mdifferentiable_cexp_mul (c : ℂ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : UpperHalfPlane => cexp (c * (z : ℂ))) := by
  intro z
  refine (UpperHalfPlane.mdifferentiableAt_iff).2 ?_
  refine ((differentiableAt_id.const_mul c).cexp.congr_of_eventuallyEq ?_)
  filter_upwards [(UpperHalfPlane.isOpen_upperHalfPlaneSet).mem_nhds z.im_pos] with w hw
  simp [Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hw]

/-- The operator `D` applied to `z ↦ cexp (c * z)` gives a scalar multiple of the same function. -/
public lemma D_cexp_mul (c : ℂ) (z : UpperHalfPlane) :
    D (fun w : UpperHalfPlane => cexp (c * (w : ℂ))) z =
      (c / (2 * π * Complex.I)) * cexp (c * (z : ℂ)) := by
  simp only [D]
  have h_agree :
      ((fun w : UpperHalfPlane => cexp (c * (w : ℂ))) ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds (z : ℂ)]
        fun w : ℂ => cexp (c * w) := by
    filter_upwards [(UpperHalfPlane.isOpen_upperHalfPlaneSet).mem_nhds z.im_pos] with w hw
    simp [Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  have hderiv :
      deriv (fun w : ℂ => cexp (c * w)) (z : ℂ) = c * cexp (c * (z : ℂ)) := by
    have hmul : HasDerivAt (fun w : ℂ => c * w) c (z : ℂ) := by
      simpa [mul_assoc] using (hasDerivAt_id (z : ℂ)).const_mul c
    simpa [mul_assoc] using ((Complex.hasDerivAt_exp (c * (z : ℂ))).scomp (z : ℂ) hmul).deriv
  simp [h_agree.deriv_eq, hderiv, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- If `F` is real-valued on the imaginary axis, then so is `D F`. -/
public lemma ResToImagAxis.Real.D_of_real {F : UpperHalfPlane → ℂ}
    (hF : ResToImagAxis.Real F) (hFholo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    ResToImagAxis.Real (D F) := by
  intro t ht
  have hdiff : DifferentiableAt ℝ F.resToImagAxis t :=
    ResToImagAxis.Differentiable F hFholo t ht
  have hderivC : HasDerivAt F.resToImagAxis (deriv F.resToImagAxis t) t :=
    hdiff.hasDerivAt
  have h_im0 : (fun u : ℝ => (F.resToImagAxis u).im) =ᶠ[nhds t] fun _ => 0 := by
    filter_upwards [lt_mem_nhds ht] with u hu
    have : (F.resToImagAxis u).im = 0 := by
      simpa [Function.resToImagAxis, ResToImagAxis, hu] using hF u hu
    simpa [this]
  have hderiv_im :
      HasDerivAt (fun u : ℝ => (F.resToImagAxis u).im) (deriv F.resToImagAxis t).im t := by
    simpa using
      (hasDerivAt_const (x := t) (c := (Complex.imCLM : ℂ →L[ℝ] ℝ))).clm_apply hderivC
  have hderiv_im0 : HasDerivAt (fun u : ℝ => (F.resToImagAxis u).im) 0 t :=
    (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq h_im0
  have him_deriv : (deriv F.resToImagAxis t).im = 0 := hderiv_im.unique hderiv_im0
  have hD : deriv F.resToImagAxis t = -2 * π * (D F).resToImagAxis t :=
    deriv_resToImagAxis_eq F hFholo ht
  have hpi : (-2 * Real.pi : ℝ) ≠ 0 := by
    have h2 : (-2 : ℝ) ≠ 0 := by norm_num
    exact mul_ne_zero h2 Real.pi_ne_zero
  have : ((D F).resToImagAxis t).im = 0 := by
    have himEq : (deriv F.resToImagAxis t).im = (-2 * Real.pi) * ((D F).resToImagAxis t).im := by
      simpa [Complex.mul_im, mul_assoc, mul_left_comm, mul_comm] using congrArg Complex.im hD
    have hmul0 : (-2 * Real.pi) * ((D F).resToImagAxis t).im = 0 := by
      nlinarith [himEq, him_deriv]
    exact (mul_eq_zero.mp hmul0).resolve_left hpi
  simpa [Function.resToImagAxis, ResToImagAxis, ht] using this
