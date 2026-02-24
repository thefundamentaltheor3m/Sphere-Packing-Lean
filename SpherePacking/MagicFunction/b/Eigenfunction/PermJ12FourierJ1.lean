module
public import SpherePacking.MagicFunction.b.Schwartz.Basic
public import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12FourierJ1Kernel
public import SpherePacking.Integration.Measure
import SpherePacking.Contour.PermJ12FourierCurveIntegral
import SpherePacking.Integration.FubiniIoc01
import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.Contour.GaussianIntegral
import SpherePacking.MagicFunction.b.Eigenfunction.Prelude


/-!
# Perm J12 Fourier J1

This file proves results such as `integrable_permJ1Kernel`, `integral_permJ1Kernel_x`.
-/

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology

open MagicFunction.b.SchwartzIntegrals

section Integral_Permutations

open scoped Real

open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral
open SpherePacking.ForMathlib
open SpherePacking.Integration
open SpherePacking.Contour


section PermJ12

open MeasureTheory Set Complex Real
open Filter
open scoped Interval

lemma integrable_permJ1Kernel (w : EuclideanSpace ℝ (Fin 8)) :
    Integrable (permJ1Kernel w)
      ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μIoc01) := by
  let sProd : Set (EuclideanSpace ℝ (Fin 8) × ℝ) := (Set.univ : Set (EuclideanSpace ℝ (Fin 8))) ×ˢ
    (Ioc (0 : ℝ) 1)
  have hsProd : MeasurableSet sProd := by
    simpa [sProd] using (MeasurableSet.univ.prod measurableSet_Ioc)
  have hmeas :
      AEStronglyMeasurable (permJ1Kernel w)
        ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μIoc01) := by
    let μProd : Measure (EuclideanSpace ℝ (Fin 8) × ℝ) :=
      (volume : Measure (EuclideanSpace ℝ (Fin 8))).prod (volume : Measure ℝ)
    have hμ :
        ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μIoc01) =
          μProd.restrict sProd := by
      simpa [sProd, μProd] using
        (SpherePacking.Integration.prod_muIoc01_eq_restrict
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin 8)))))
    have hcontψ : ContinuousOn (fun t : ℝ => ψT' (z₁line t)) (Ioc (0 : ℝ) 1) :=
      continuousOn_ψT'_z₁line
    have hcont :
        ContinuousOn (permJ1Kernel w) sProd := by
      have hphase :
          Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ =>
            cexp ((-2 * (π * ⟪p.1, w⟫)) * I) := by
        have hinner : Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ => (⟪p.1, w⟫ : ℝ) := by
          simpa using (continuous_fst.inner continuous_const)
        have hreal :
            Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ =>
              (-2 : ℝ) * ((π : ℝ) * (⟪p.1, w⟫ : ℝ)) :=
          continuous_const.mul (continuous_const.mul hinner)
        have harg :
            Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ =>
              ((((-2 : ℝ) * ((π : ℝ) * (⟪p.1, w⟫ : ℝ))) : ℝ) : ℂ) * (Complex.I : ℂ) := by
          exact (Complex.continuous_ofReal.comp hreal).mul continuous_const
        simpa [mul_assoc] using (Complex.continuous_exp.comp harg)
      have hψ : ContinuousOn (fun p : EuclideanSpace ℝ (Fin 8) × ℝ => ψT' (z₁line p.2)) sProd := by
        refine hcontψ.comp continuousOn_snd ?_
        intro p hp
        exact (Set.mem_prod.mp hp).2
      have hgauss :
          Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ =>
            cexp ((π : ℂ) * I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₁line p.2)) := by
        have hnormsq : Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ => (‖p.1‖ ^ 2 : ℝ) :=
          (continuous_fst.norm.pow 2)
        have hz : Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ => z₁line p.2 :=
          continuous_z₁line.comp continuous_snd
        have harg' :
            Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ =>
              (π : ℂ) * I * (((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₁line p.2)) :=
          continuous_const.mul ((continuous_ofReal.comp hnormsq).mul hz)
        simpa [mul_assoc] using (Complex.continuous_exp.comp harg')
      have hconst : ContinuousOn (fun _p : EuclideanSpace ℝ (Fin 8) × ℝ => (Complex.I : ℂ)) sProd :=
        continuousOn_const
      have hmul1 :
          ContinuousOn
            (fun p : EuclideanSpace ℝ (Fin 8) × ℝ => (Complex.I : ℂ) * ψT' (z₁line p.2)) sProd :=
        hconst.mul hψ
      have hmul2 :
          ContinuousOn
            (fun p : EuclideanSpace ℝ (Fin 8) × ℝ =>
              ((Complex.I : ℂ) * ψT' (z₁line p.2)) *
                cexp ((π : ℂ) * I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₁line p.2))) sProd :=
        hmul1.mul hgauss.continuousOn
      refine (hphase.continuousOn.mul hmul2).congr ?_
      intro p _hp
      simp [permJ1Kernel, mul_assoc]
    have hker : AEStronglyMeasurable (permJ1Kernel w) (μProd.restrict sProd) := by
      simpa [μProd] using (hcont.aestronglyMeasurable (μ := μProd) (s := sProd) hsProd)
    simpa [hμ] using hker
  refine
    (MeasureTheory.integrable_prod_iff' (μ := (volume : Measure (EuclideanSpace ℝ (Fin 8))))
      (ν := μIoc01) hmeas).2 ?_
  exact ⟨ae_integrable_permJ1Kernel_slice (w := w), integrable_integral_norm_permJ1Kernel (w := w)⟩

lemma integral_permJ1Kernel_x (w : EuclideanSpace ℝ (Fin 8))
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : EuclideanSpace ℝ (Fin 8), permJ1Kernel w (x, t)) =
      (Complex.I : ℂ) * Ψ₁_fourier (‖w‖ ^ 2) (z₁line t) := by
  have hz : 0 < (z₁line t).im := by simpa [z₁line] using ht.1
  let c : ℂ := (Complex.I : ℂ) * ψT' (z₁line t)
  have hfactor :
      (fun x : EuclideanSpace ℝ (Fin 8) ↦ permJ1Kernel w (x, t)) =
        fun x : EuclideanSpace ℝ (Fin 8) ↦
          c *
            (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t))) := by
    funext x
    dsimp [permJ1Kernel, c]
    simp [mul_assoc, mul_left_comm, mul_comm]
  have hgauss :=
    SpherePacking.Contour.integral_const_mul_phase_gaussian_pi_mul_I_mul_even
      (k := 4) (w := w) (z := z₁line t) hz (c := c)
  calc
    (∫ x : EuclideanSpace ℝ (Fin 8), permJ1Kernel w (x, t)) =
        c * ((((I : ℂ) / (z₁line t)) ^ (4 : ℕ)) *
          cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / (z₁line t)))) := by
          simpa [hfactor] using hgauss
    _ = (Complex.I : ℂ) * Ψ₁_fourier (‖w‖ ^ 2) (z₁line t) := by
          simp [c, Ψ₁_fourier, mul_assoc, mul_left_comm, mul_comm]

private lemma integral_permJ1Kernel_x_ae (w : EuclideanSpace ℝ (Fin 8)) :
    (fun t : ℝ =>
        (∫ x : EuclideanSpace ℝ (Fin 8), permJ1Kernel w (x, t) ∂(volume : Measure _))) =ᵐ[μIoc01]
      fun t : ℝ => (Complex.I : ℂ) * Ψ₁_fourier (‖w‖ ^ 2) (z₁line t) := by
  simpa [SpherePacking.Integration.μIoc01] using
    (ae_restrict_iff' (μ := (volume : Measure ℝ)) (s := Ioc (0 : ℝ) 1) measurableSet_Ioc).2 <|
      .of_forall fun t ht => by simpa using (integral_permJ1Kernel_x (w := w) (t := t) ht)

/-- Fourier transform of `J₁` as a curve integral of `Ψ₁_fourier` along the segment
`Path.segment (-1) (-1 + I)`. -/
public lemma fourier_J₁_eq_curveIntegral (w : EuclideanSpace ℝ (Fin 8)) :
    𝓕 (J₁ : EuclideanSpace ℝ (Fin 8) → ℂ) w =
      (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + I),
        scalarOneForm (Ψ₁_fourier (‖w‖ ^ 2)) z) := by
  simpa using
    SpherePacking.Contour.fourier_J₁_eq_curveIntegral_of
      (fun x => by
        simpa using (J₁_apply (x := x)))
      phase_mul_J₁'_eq_integral_permJ1Kernel
      integrable_permJ1Kernel
      integral_permJ1Kernel_x_ae
      (fun w' => by
        simpa using
          (integral_I_mul_muIoc01_z₁line (F := Ψ₁_fourier (‖w'‖ ^ 2))))
      w


end Integral_Permutations.PermJ12
end

end MagicFunction.b.Fourier
