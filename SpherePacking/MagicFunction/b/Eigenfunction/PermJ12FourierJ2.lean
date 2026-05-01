module
public import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12FourierJ1
import SpherePacking.Contour.PermJ12FourierCurveIntegral
import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.ForMathlib.FourierPhase
import SpherePacking.Integration.FubiniIoc01
import SpherePacking.Contour.GaussianIntegral
import SpherePacking.MagicFunction.b.Eigenfunction.Prelude


/-!
# Perm J12 Fourier J2

##### Fourier transform of `J₂`

-/

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology

open MagicFunction.b.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap

section Integral_Permutations

open scoped Real

open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral
open SpherePacking.ForMathlib
open SpherePacking.Contour
open SpherePacking.Integration


section PermJ12

open MeasureTheory Set Complex Real
open Filter
open scoped Interval


def permJ2Kernel (w : EuclideanSpace ℝ (Fin 8)) : EuclideanSpace ℝ (Fin 8) × ℝ → ℂ :=
  fun p =>
    cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I) *
      (ψT' (z₂line p.2) *
        cexp ((π : ℂ) * I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₂line p.2)))

lemma phase_mul_J₂'_eq_integral_permJ2Kernel (w x : EuclideanSpace ℝ (Fin 8)) :
    cexp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I) *
        MagicFunction.b.RealIntegrals.J₂' (‖x‖ ^ (2 : ℕ)) =
      ∫ t : ℝ, permJ2Kernel w (x, t) ∂μIoc01 := by
  rw [show MagicFunction.b.RealIntegrals.J₂' (‖x‖ ^ (2 : ℕ)) =
      ∫ t : ℝ, ψT' (z₂line t) *
        cexp ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) * (z₂line t)) ∂μIoc01 from by
    simpa [μIoc01] using (J₂'_eq_Ioc (r := ‖x‖ ^ (2 : ℕ))).trans
      (MeasureTheory.integral_congr_ae <| (ae_restrict_iff' measurableSet_Ioc).2 <|
        .of_forall fun t ht => by
          simp [SpherePacking.Contour.z₂'_eq_z₂line (t := t) (mem_Icc_of_Ioc ht)])]
  simpa [permJ2Kernel] using
    (MeasureTheory.integral_const_mul (μ := μIoc01)
      (r := cexp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I))
      (f := fun t => ψT' (z₂line t) *
        cexp ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) * (z₂line t)))).symm

lemma norm_permJ2Kernel (w x : EuclideanSpace ℝ (Fin 8)) (t : ℝ) :
    ‖permJ2Kernel w (x, t)‖ = ‖ψT' (z₂line t)‖ * rexp (-(π * ‖x‖ ^ 2)) := by
  have hgauss :
      ‖cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₂line t))‖ = rexp (-(π * ‖x‖ ^ 2)) := by
    simpa [z₂line, show (-π * (‖x‖ ^ 2) : ℝ) = -(π * ‖x‖ ^ 2) from by ring] using
      norm_cexp_pi_mul_I_mul_sq (z := z₂line t) (x := x)
  dsimp [permJ2Kernel]
  rw [norm_mul, norm_phase_eq_one (w := w) (x := x)]
  simp_all

lemma integrable_permJ2Kernel_slice (w : EuclideanSpace ℝ (Fin 8)) (t : ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 8) ↦ permJ2Kernel w (x, t))
      (volume : Measure (EuclideanSpace ℝ (Fin 8))) := by
  simpa [permJ2Kernel, mul_assoc] using Integrable.bdd_mul (c := (1 : ℝ))
    (hg := by simpa [mul_assoc] using
      (SpherePacking.ForMathlib.integrable_gaussian_cexp_pi_mul_I_mul
        (z := z₂line t) (by simp [z₂line] : 0 < (z₂line t).im)).const_mul (ψT' (z₂line t)))
    (aestronglyMeasurable_phase (w := w)) (ae_norm_phase_le_one (w := w))

lemma ae_integrable_permJ2Kernel_slice (w : EuclideanSpace ℝ (Fin 8)) :
    ∀ᵐ t : ℝ ∂μIoc01,
      Integrable (fun x : EuclideanSpace ℝ (Fin 8) ↦ permJ2Kernel w (x, t))
        (volume : Measure (EuclideanSpace ℝ (Fin 8))) :=
  .of_forall fun t => integrable_permJ2Kernel_slice (w := w) (t := t)

lemma integral_permJ2Kernel_x (w : EuclideanSpace ℝ (Fin 8)) (t : ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin 8), permJ2Kernel w (x, t)) =
      Ψ₁_fourier (‖w‖ ^ 2) (z₂line t) := by
  simpa [permJ2Kernel, Ψ₁_fourier, mul_assoc, mul_left_comm, mul_comm] using
    SpherePacking.Contour.integral_const_mul_phase_gaussian_pi_mul_I_mul_even
      (k := 4) (w := w) (z := z₂line t) (by simp [z₂line]) (c := ψT' (z₂line t))

lemma integrable_permJ2Kernel (w : EuclideanSpace ℝ (Fin 8)) :
    Integrable (permJ2Kernel w)
      ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μIoc01) := by
  have hψ : Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ => ψT' (z₂line p.2) :=
    continuous_ψT'_z₂line.comp continuous_snd
  have hzline : Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ => z₂line p.2 :=
    continuous_z₂line.comp continuous_snd
  rcases exists_bound_norm_ψT'_z₂' with ⟨Mψ, hMψ'⟩
  set Cgauss : ℝ := ∫ x : EuclideanSpace ℝ (Fin 8), rexp (-(π * ‖x‖ ^ 2))
  have hCgauss : 0 ≤ Cgauss := MeasureTheory.integral_nonneg fun x => by positivity
  have hbound :
      ∀ᵐ t : ℝ ∂μIoc01,
        (∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ2Kernel w (x, t)‖) ≤ (Mψ : ℝ) * Cgauss := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => ?_
    rw [show (∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ2Kernel w (x, t)‖) =
        ‖ψT' (z₂line t)‖ * Cgauss from by
      simpa [funext fun x => norm_permJ2Kernel (w := w) (x := x) (t := t), Cgauss, mul_assoc]
        using MeasureTheory.integral_const_mul (μ := (volume : Measure (EuclideanSpace ℝ (Fin 8))))
          (r := ‖ψT' (z₂line t)‖) (f := fun x => rexp (-(π * ‖x‖ ^ 2)))]
    refine mul_le_mul_of_nonneg_right ?_ hCgauss
    simpa [show z₂' t = z₂line t from by
      simpa [z₂line, add_assoc, add_left_comm, add_comm] using
        z₂'_eq_of_mem (t := t) (mem_Icc_of_Ioc ht)] using hMψ' t ht
  have hcont : Continuous (permJ2Kernel w) := by unfold permJ2Kernel; fun_prop
  exact (MeasureTheory.integrable_prod_iff'
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin 8)))) (ν := μIoc01)
    (hcont.aestronglyMeasurable
      (μ := ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μIoc01)))).2
    ⟨ae_integrable_permJ2Kernel_slice (w := w),
      Integrable.mono' (integrable_const ((Mψ : ℝ) * Cgauss))
        (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
          (μ := μIoc01) (ν := (volume : Measure (EuclideanSpace ℝ (Fin 8))))
          (f := fun p : ℝ × EuclideanSpace ℝ (Fin 8) => ‖permJ2Kernel w (p.2, p.1)‖) (by fun_prop))
        (hbound.mono fun t ht => by
          simpa [Real.norm_eq_abs, abs_of_nonneg
            (MeasureTheory.integral_nonneg fun x => norm_nonneg _ : (0 : ℝ) ≤ _)] using ht)⟩

private lemma integral_permJ2Kernel_x_ae (w : EuclideanSpace ℝ (Fin 8)) :
    (fun t : ℝ =>
        (∫ x : EuclideanSpace ℝ (Fin 8), permJ2Kernel w (x, t) ∂(volume : Measure _))) =ᵐ[μIoc01]
      fun t : ℝ => Ψ₁_fourier (‖w‖ ^ 2) (z₂line t) :=
  .of_forall fun t => integral_permJ2Kernel_x (w := w) (t := t)

/-- Fourier transform of `J₂` as a curve integral of `Ψ₁_fourier` along the segment
`Path.segment (-1 + I) I`. -/
public lemma fourier_J₂_eq_curveIntegral (w : EuclideanSpace ℝ (Fin 8)) :
    (𝓕 (J₂ : EuclideanSpace ℝ (Fin 8) → ℂ)) w =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + I) I,
        scalarOneForm (Ψ₁_fourier (‖w‖ ^ 2)) z) := by
  simpa using
    SpherePacking.Contour.fourier_J_eq_curveIntegral_of
      (a := (-1 : ℂ) + I) (b := I)
      (fun x => by
        simpa using (J₂_apply (x := x)))
      (fun w x => by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          phase_mul_J₂'_eq_integral_permJ2Kernel (w := w) (x := x))
      integrable_permJ2Kernel
      integral_permJ2Kernel_x_ae
      (fun w' => by
        simpa using
          (integral_muIoc01_z₂line (F := Ψ₁_fourier (‖w'‖ ^ 2))))
      w


end Integral_Permutations.PermJ12
end

end MagicFunction.b.Fourier
