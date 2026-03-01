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
  let g : ℝ → ℂ := fun t =>
    ψT' (z₂line t) * cexp ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) * (z₂line t))
  have hJ₂μ : MagicFunction.b.RealIntegrals.J₂' (‖x‖ ^ (2 : ℕ)) = ∫ t : ℝ, g t ∂μIoc01 := by
    have hJ₂' : MagicFunction.b.RealIntegrals.J₂' (‖x‖ ^ (2 : ℕ)) = ∫ t in Ioc (0 : ℝ) 1, g t := by
      refine (J₂'_eq_Ioc (r := ‖x‖ ^ (2 : ℕ))).trans ?_
      refine MeasureTheory.integral_congr_ae ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall ?_
      intro t ht
      have hz : z₂' t = z₂line t := SpherePacking.Contour.z₂'_eq_z₂line (t := t) (mem_Icc_of_Ioc ht)
      simp [g, hz]
    simpa [μIoc01] using hJ₂'
  rw [hJ₂μ]
  simpa [g, permJ2Kernel] using
    (MeasureTheory.integral_const_mul (μ := μIoc01)
      (r := cexp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I)) (f := g)).symm

lemma norm_permJ2Kernel (w x : EuclideanSpace ℝ (Fin 8)) (t : ℝ) :
    ‖permJ2Kernel w (x, t)‖ = ‖ψT' (z₂line t)‖ * rexp (-(π * ‖x‖ ^ 2)) := by
  have hz1 : (z₂line t).im = (1 : ℝ) := by simp [z₂line]
  have hgauss0 :
      ‖cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₂line t))‖ =
        rexp (-π * (‖x‖ ^ 2) * (z₂line t).im) := by
    simpa using (norm_cexp_pi_mul_I_mul_sq (z := z₂line t) (x := x))
  have hgauss :
      ‖cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₂line t))‖ =
        rexp (-(π * ‖x‖ ^ 2)) := by
    rw [hgauss0, hz1]
    have : (-π * (‖x‖ ^ 2) : ℝ) = -(π * ‖x‖ ^ 2) := by ring
    simp [this]
  dsimp [permJ2Kernel]
  rw [norm_mul]
  rw [norm_phase_eq_one (w := w) (x := x)]
  simp_all

lemma integrable_permJ2Kernel_slice (w : EuclideanSpace ℝ (Fin 8)) (t : ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 8) ↦ permJ2Kernel w (x, t))
      (volume : Measure (EuclideanSpace ℝ (Fin 8))) := by
  -- Integrability of the Gaussian factor.
  have hz : 0 < (z₂line t).im := by simp [z₂line]
  have hgauss :
      Integrable
          (fun x : EuclideanSpace ℝ (Fin 8) ↦
            cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₂line t)))
          (volume : Measure (EuclideanSpace ℝ (Fin 8))) :=
    SpherePacking.ForMathlib.integrable_gaussian_cexp_pi_mul_I_mul (z := z₂line t) hz
  have hgauss' :
      Integrable (fun x : EuclideanSpace ℝ (Fin 8) ↦
          ψT' (z₂line t) *
            cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₂line t)))
        (volume : Measure (EuclideanSpace ℝ (Fin 8))) := by
    simpa [mul_assoc] using hgauss.const_mul (ψT' (z₂line t))
  -- Multiply by the bounded phase factor.
  have hbound :
      ∀ᵐ x : EuclideanSpace ℝ (Fin 8) ∂(volume : Measure (EuclideanSpace ℝ (Fin 8))),
        ‖cexp (↑(-2 * (π * ⟪x, w⟫)) * I)‖ ≤ (1 : ℝ) :=
    ae_norm_phase_le_one (w := w)
  have h := Integrable.bdd_mul (hg := hgauss')
    (f := fun x : EuclideanSpace ℝ (Fin 8) ↦ cexp (↑(-2 * (π * ⟪x, w⟫)) * I))
    (g := fun x : EuclideanSpace ℝ (Fin 8) ↦
      ψT' (z₂line t) *
        cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₂line t)))
    (c := (1 : ℝ)) (aestronglyMeasurable_phase (w := w)) hbound
  simpa [permJ2Kernel, mul_assoc] using h

lemma ae_integrable_permJ2Kernel_slice (w : EuclideanSpace ℝ (Fin 8)) :
    ∀ᵐ t : ℝ ∂μIoc01,
      Integrable (fun x : EuclideanSpace ℝ (Fin 8) ↦ permJ2Kernel w (x, t))
        (volume : Measure (EuclideanSpace ℝ (Fin 8))) := by
  simpa using (Filter.Eventually.of_forall fun t => integrable_permJ2Kernel_slice (w := w) (t := t))

lemma integral_permJ2Kernel_x (w : EuclideanSpace ℝ (Fin 8)) (t : ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin 8), permJ2Kernel w (x, t)) =
      Ψ₁_fourier (‖w‖ ^ 2) (z₂line t) := by
  have hz : 0 < (z₂line t).im := by simp [z₂line]
  simpa [permJ2Kernel, Ψ₁_fourier, mul_assoc, mul_left_comm, mul_comm] using
    (SpherePacking.Contour.integral_const_mul_phase_gaussian_pi_mul_I_mul_even
      (k := 4) (w := w) (z := z₂line t) hz (c := ψT' (z₂line t)))

lemma integrable_permJ2Kernel (w : EuclideanSpace ℝ (Fin 8)) :
    Integrable (permJ2Kernel w)
      ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μIoc01) := by
  -- `permJ2Kernel` is continuous, hence `AEStronglyMeasurable`.
  have hcontψ : Continuous fun t : ℝ => ψT' (z₂line t) :=
    continuous_ψT'_z₂line
  have hcont : Continuous (permJ2Kernel w) := by
    have hphase :
        Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ =>
          cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I) := by
      have hinner : Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ => (⟪p.1, w⟫ : ℝ) := by
        simpa using (continuous_fst.inner continuous_const)
      have harg :
          Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ =>
              (↑(-2 * (π * ⟪p.1, w⟫)) : ℂ) * I :=
        (Complex.continuous_ofReal.comp
              (continuous_const.mul (continuous_const.mul hinner))).mul continuous_const
      simpa using harg.cexp
    have hψ : Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ => ψT' (z₂line p.2) :=
      hcontψ.comp continuous_snd
    have hgauss :
        Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ =>
          cexp ((π : ℂ) * I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₂line p.2)) := by
      have hnormsq :
          Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ => (‖p.1‖ ^ 2 : ℝ) :=
        (continuous_fst.norm.pow 2)
      have hz : Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ => z₂line p.2 :=
        continuous_z₂line.comp continuous_snd
      have harg' :
          Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ =>
            (π : ℂ) * I * (((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₂line p.2)) :=
        by
          have hmul :
              Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ =>
                ((‖p.1‖ ^ 2 : ℝ) : ℂ) * z₂line p.2 :=
            (continuous_ofReal.comp hnormsq).mul hz
          change
            Continuous
              ((fun _p : EuclideanSpace ℝ (Fin 8) × ℝ => (π : ℂ) * I) *
                fun p : EuclideanSpace ℝ (Fin 8) × ℝ =>
                  ((‖p.1‖ ^ 2 : ℝ) : ℂ) * z₂line p.2)
          exact continuous_const.mul hmul
      simpa [mul_assoc] using (Complex.continuous_exp.comp harg')
    -- Unfold `permJ2Kernel` at the level of functions to avoid commutativity rewriting.
    change Continuous (fun p : EuclideanSpace ℝ (Fin 8) × ℝ =>
      cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I) *
        (ψT' (z₂line p.2) *
          cexp ((π : ℂ) * I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₂line p.2))))
    exact hphase.mul (hψ.mul hgauss)
  have hmeas :
      AEStronglyMeasurable (permJ2Kernel w)
        ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μIoc01) :=
    hcont.aestronglyMeasurable
  -- Use the product characterization: slices are integrable (proved above), and the `x`-integral
  -- of the norm is bounded on `Ioc (0,1)`.
  have hslice :
      (∀ᵐ t : ℝ ∂μIoc01,
        Integrable (fun x : EuclideanSpace ℝ (Fin 8) => permJ2Kernel w (x, t))
          (volume : Measure (EuclideanSpace ℝ (Fin 8)))) :=
    ae_integrable_permJ2Kernel_slice (w := w)
  rcases exists_bound_norm_ψT'_z₂' with ⟨Mψ, hMψ'⟩
  let Cgauss : ℝ := ∫ x : EuclideanSpace ℝ (Fin 8), rexp (-(π * ‖x‖ ^ 2))
  have hCgauss : 0 ≤ Cgauss := by
    have : 0 ≤ (fun x : EuclideanSpace ℝ (Fin 8) => rexp (-(π * ‖x‖ ^ 2))) := by
      intro x; positivity
    simpa [Cgauss] using MeasureTheory.integral_nonneg this
  have hbound :
      ∀ᵐ t : ℝ ∂μIoc01,
        (∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ2Kernel w (x, t)‖) ≤
          (Mψ : ℝ) * Cgauss := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall ?_
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioc ht
    have hz : z₂' t = z₂line t := by
      simpa [z₂line, add_assoc, add_left_comm, add_comm] using (z₂'_eq_of_mem (t := t) htIcc)
    have hψle : ‖ψT' (z₂line t)‖ ≤ Mψ := by
      simpa [hz] using hMψ' t ht
    have hnorm_eq (x : EuclideanSpace ℝ (Fin 8)) :
        ‖permJ2Kernel w (x, t)‖ = ‖ψT' (z₂line t)‖ * rexp (-(π * ‖x‖ ^ 2)) := by
      simpa using (norm_permJ2Kernel (w := w) (x := x) (t := t))
    have hInt :
        (∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ2Kernel w (x, t)‖) =
          ‖ψT' (z₂line t)‖ * Cgauss := by
      have hfun :
          (fun x : EuclideanSpace ℝ (Fin 8) => ‖permJ2Kernel w (x, t)‖) =
            fun x : EuclideanSpace ℝ (Fin 8) =>
              ‖ψT' (z₂line t)‖ * rexp (-(π * ‖x‖ ^ 2)) := by
        funext x
        simpa using hnorm_eq (x := x)
      -- Pull out the constant.
      simpa [hfun, Cgauss, mul_assoc] using
        (MeasureTheory.integral_const_mul
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin 8))))
          (r := ‖ψT' (z₂line t)‖)
          (f := fun x : EuclideanSpace ℝ (Fin 8) => rexp (-(π * ‖x‖ ^ 2))))
    -- Apply the bound on `‖ψT'‖`.
    have : ‖ψT' (z₂line t)‖ * Cgauss ≤ (Mψ : ℝ) * Cgauss :=
      mul_le_mul_of_nonneg_right hψle hCgauss
    simpa [hInt, mul_assoc] using this
  have hmeas_norm :
      AEStronglyMeasurable
        (fun t : ℝ =>
          ∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ2Kernel w (x, t)‖) μIoc01 := by
    have hswap :
        AEStronglyMeasurable
          (fun p : ℝ × EuclideanSpace ℝ (Fin 8) => ‖permJ2Kernel w (p.2, p.1)‖)
          (μIoc01.prod (volume : Measure (EuclideanSpace ℝ (Fin 8)))) := by
      -- Continuity of the swapped kernel.
      fun_prop
    exact MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := μIoc01) (ν := (volume : Measure (EuclideanSpace ℝ (Fin 8))))
      (f := fun p : ℝ × EuclideanSpace ℝ (Fin 8) => ‖permJ2Kernel w (p.2, p.1)‖) hswap
  have hmajor :
      Integrable (fun _t : ℝ => (Mψ : ℝ) * Cgauss) μIoc01 := by
    simpa using (integrable_const (α := ℝ) (μ := μIoc01) ((Mψ : ℝ) * Cgauss))
  have hint_norm :
      Integrable
        (fun t : ℝ =>
          ∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ2Kernel w (x, t)‖) μIoc01 := by
    refine Integrable.mono' hmajor hmeas_norm ?_
    refine hbound.mono ?_
    intro t ht
    have hnonneg :
        0 ≤ (∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ2Kernel w (x, t)‖) := by
      have : 0 ≤ fun x : EuclideanSpace ℝ (Fin 8) => ‖permJ2Kernel w (x, t)‖ := by
        intro x; positivity
      simpa using MeasureTheory.integral_nonneg this
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using ht
  exact (MeasureTheory.integrable_prod_iff'
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin 8)))) (ν := μIoc01) hmeas).2
      ⟨hslice, hint_norm⟩

private lemma integral_permJ2Kernel_x_ae (w : EuclideanSpace ℝ (Fin 8)) :
    (fun t : ℝ =>
        (∫ x : EuclideanSpace ℝ (Fin 8), permJ2Kernel w (x, t) ∂(volume : Measure _))) =ᵐ[μIoc01]
      fun t : ℝ => Ψ₁_fourier (‖w‖ ^ 2) (z₂line t) := by
  simpa using (Filter.Eventually.of_forall fun t => integral_permJ2Kernel_x (w := w) (t := t))

/-- Fourier transform of `J₂` as a curve integral of `Ψ₁_fourier` along the segment
`Path.segment (-1 + I) I`. -/
public lemma fourier_J₂_eq_curveIntegral (w : EuclideanSpace ℝ (Fin 8)) :
    (𝓕 (J₂ : EuclideanSpace ℝ (Fin 8) → ℂ)) w =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + I) I,
        scalarOneForm (Ψ₁_fourier (‖w‖ ^ 2)) z) := by
  simpa using
    SpherePacking.Contour.fourier_J₂_eq_curveIntegral_of
      (fun x => by
        simpa using (J₂_apply (x := x)))
      phase_mul_J₂'_eq_integral_permJ2Kernel
      integrable_permJ2Kernel
      integral_permJ2Kernel_x_ae
      (fun w' => by
        simpa using
          (integral_muIoc01_z₂line (F := Ψ₁_fourier (‖w'‖ ^ 2))))
      w


end Integral_Permutations.PermJ12
end

end MagicFunction.b.Fourier
