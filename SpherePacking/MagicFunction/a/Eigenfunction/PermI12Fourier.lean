module
public import SpherePacking.MagicFunction.a.Eigenfunction.PermI12Prelude
public import SpherePacking.Contour.Segments
public import SpherePacking.Integration.Measure
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
import Mathlib.Tactic.Ring.RingNF

/-!
# Fourier kernels for `I₁` and `I₂`

We introduce the product-measure kernels used to express the Fourier transforms of `I₁` and `I₂`
as iterated integrals, and record their measurability.

## Main definitions
* `permI1Kernel`
* `permI2Kernel`

## Main statements
* `permI1Kernel_measurable`
* `permI2Kernel_measurable`
-/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter

open MeasureTheory Set Complex Real SpherePacking.Integration SpherePacking.Contour
open scoped Interval

/-- The kernel used to rewrite `𝓕 I₁` as an integral over `x` and the segment parameter `t`. -/
@[expose] public def permI1Kernel (w : EuclideanSpace ℝ (Fin 8)) :
    (EuclideanSpace ℝ (Fin 8)) × ℝ → ℂ := fun p =>
  cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I) *
    ((I : ℂ) * MagicFunction.a.ComplexIntegrands.Φ₁' (‖p.1‖ ^ 2) (z₁line p.2))

/-- The kernel used to rewrite `𝓕 I₂` as an integral over `x` and the segment parameter `t`. -/
@[expose] public def permI2Kernel (w : EuclideanSpace ℝ (Fin 8)) :
    (EuclideanSpace ℝ (Fin 8)) × ℝ → ℂ := fun p =>
  cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I) *
    MagicFunction.a.ComplexIntegrands.Φ₁' (‖p.1‖ ^ 2) (z₂line p.2)

/-- Helper: continuity of `φ₀'' ∘ (-1 / (z · + 1))` at `t` given `(z t + 1).im > 0`. -/
private lemma continuousAt_φ₀''_inv_add_one {z : ℝ → ℂ} (hz : Continuous z) {t : ℝ}
    (hpos : 0 < (z t + 1).im) :
    ContinuousAt (fun s : ℝ => φ₀'' ((-1 : ℂ) / (z s + 1))) t := by
  have hden : z t + 1 ≠ 0 := fun h => hpos.ne' (by simp [h])
  have hmem : (-1 : ℂ) / (z t + 1) ∈ UpperHalfPlane.upperHalfPlaneSet := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using neg_one_div_im_pos (z t + 1) hpos
  have hφ : ContinuousAt (fun w : ℂ => φ₀'' w) ((-1 : ℂ) / (z t + 1)) :=
    (MagicFunction.a.ComplexIntegrands.φ₀''_holo.differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hmem)).continuousAt
  exact ContinuousAt.comp (f := fun s : ℝ => (-1 : ℂ) / (z s + 1)) hφ
    (continuousAt_const.div ((hz.continuousAt).add continuousAt_const) (by simpa using hden))

/-- Continuity of `(x, t) ↦ Φ₁'(‖x‖², z t)` at points where `(z p.2 + 1).im > 0`. -/
private lemma continuousAt_Φ₁'_comp {z : ℝ → ℂ} (hz : Continuous z)
    {p : (EuclideanSpace ℝ (Fin 8)) × ℝ} (hpos : 0 < (z p.2 + 1).im) :
    ContinuousAt (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
      MagicFunction.a.ComplexIntegrands.Φ₁' (‖q.1‖ ^ 2) (z q.2)) p := by
  have hφterm : ContinuousAt
      (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => φ₀'' ((-1 : ℂ) / (z q.2 + 1))) p := by
    simpa [Function.comp] using (continuousAt_φ₀''_inv_add_one hz hpos).comp continuousAt_snd
  have hz_pt : ContinuousAt (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => z q.2) p :=
    (hz.continuousAt).comp continuousAt_snd
  have hpow : ContinuousAt
      (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => (z q.2 + 1) ^ (2 : ℕ)) p :=
    (hz_pt.add continuousAt_const).pow 2
  have hexp : ContinuousAt
      (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
        cexp ((π : ℂ) * I * ((‖q.1‖ ^ 2 : ℝ) : ℂ) * z q.2)) p :=
    (((continuousAt_const.mul continuousAt_const).mul (by fun_prop)).mul hz_pt).cexp
  dsimp [MagicFunction.a.ComplexIntegrands.Φ₁']
  exact (hφterm.mul hpow).mul hexp

/-- Measurability for the restricted product measure via continuity on `univ ×ˢ Ioc 0 1`. -/
private lemma aestronglyMeasurable_of_continuousOn_univ_prod_Ioc01
    {f : (EuclideanSpace ℝ (Fin 8)) × ℝ → ℂ}
    (hcont : ContinuousOn f (univ ×ˢ Ioc (0 : ℝ) 1)) :
    AEStronglyMeasurable f ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μIoc01) := by
  have hμ : ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μIoc01) =
      (((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod (volume : Measure ℝ)).restrict
        (univ ×ˢ Ioc (0 : ℝ) 1)) := by
    simpa using prod_muIoc01_eq_restrict (μ := (volume : Measure (EuclideanSpace ℝ (Fin 8))))
  simpa [hμ] using hcont.aestronglyMeasurable (MeasurableSet.univ.prod measurableSet_Ioc)

/-- Measurability of `permI1Kernel` with respect to the product measure `volume × μIoc01`. -/
public lemma permI1Kernel_measurable (w : EuclideanSpace ℝ (Fin 8)) :
    AEStronglyMeasurable (permI1Kernel w)
      ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod (μIoc01)) := by
  refine aestronglyMeasurable_of_continuousOn_univ_prod_Ioc01 fun p hp => ?_
  have hpos : 0 < (z₁line p.2 + 1).im := by simpa using ((Set.mem_prod.mp hp).2).1
  have hphase : ContinuousAt (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
      cexp (↑(-2 * (π * ⟪q.1, w⟫)) * I)) p := by fun_prop
  exact (hphase.mul (continuousAt_const.mul
    (continuousAt_Φ₁'_comp continuous_z₁line hpos))).continuousWithinAt

/-- Measurability of `permI2Kernel` with respect to the product measure `volume × μIoc01`. -/
public lemma permI2Kernel_measurable (w : EuclideanSpace ℝ (Fin 8)) :
    AEStronglyMeasurable (permI2Kernel w)
      ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod (μIoc01)) := by
  refine aestronglyMeasurable_of_continuousOn_univ_prod_Ioc01 fun p _ => ?_
  have hphase : ContinuousAt (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
      cexp (↑(-2 * (π * ⟪q.1, w⟫)) * I)) p := by fun_prop
  exact (hphase.mul (continuousAt_Φ₁'_comp continuous_z₂line (by simp))).continuousWithinAt

end
end MagicFunction.a.Fourier
