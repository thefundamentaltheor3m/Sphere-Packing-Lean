module
public import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12CurveIntegrals
import SpherePacking.Integration.EndpointIntegrability
import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.ForMathlib.FourierPhase
import SpherePacking.MagicFunction.b.Schwartz.PsiExpBounds.PsiSDecay
import SpherePacking.MagicFunction.PsiTPrimeZ1Integrability


/-!
# Perm J12 Fourier J1 Kernel

This file defines the kernel used to rewrite the Fourier transform of `J₁` using Fubini.

## Main definitions
* `permJ1Kernel`

## Main statements
* `phase_mul_J₁'_eq_integral_permJ1Kernel`
* `ae_integrable_permJ1Kernel_slice`
* `integrable_integral_norm_permJ1Kernel`
-/

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology

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


/-- Rewrite `J₁'` using the explicit line parametrisation `z₁line`. -/
public lemma J₁'_eq_integral_z₁line (r : ℝ) :
    MagicFunction.b.RealIntegrals.J₁' r =
      ∫ t in Ioc (0 : ℝ) 1,
        (Complex.I : ℂ) * ψT' (z₁line t) *
          cexp ((π : ℂ) * I * (r : ℂ) * (z₁line t)) := by
  rw [J₁'_eq_Ioc (r := r)]
  refine MeasureTheory.integral_congr_ae ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall ?_
  intro t ht
  have htIcc : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioc ht
  simpa [z₁line, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using
    congrArg (fun z : ℂ => (Complex.I : ℂ) * ψT' z * cexp ((π : ℂ) * I * (r : ℂ) * z))
      (z₁'_eq_of_mem (t := t) htIcc)

/-- The `(x,t)`-kernel used in the `J₁` Fourier-transform calculation. -/
@[expose] public def permJ1Kernel (w : EuclideanSpace ℝ (Fin 8)) :
    EuclideanSpace ℝ (Fin 8) × ℝ → ℂ :=
  fun p =>
    cexp ((-2 * (π * ⟪p.1, w⟫)) * I) *
      ((Complex.I : ℂ) * ψT' (z₁line p.2) *
        cexp ((π : ℂ) * I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₁line p.2)))

/-- Move the Fourier phase inside the `t`-integral, rewriting `J₁'` using `permJ1Kernel`. -/
public lemma phase_mul_J₁'_eq_integral_permJ1Kernel (w x : EuclideanSpace ℝ (Fin 8)) :
    cexp (↑(-2 * Real.pi * ⟪x, w⟫) * Complex.I) *
        MagicFunction.b.RealIntegrals.J₁' (‖x‖ ^ (2 : ℕ)) =
      ∫ t : ℝ, permJ1Kernel w (x, t) ∂μIoc01 := by
  have hJ₁μ :
      MagicFunction.b.RealIntegrals.J₁' (‖x‖ ^ (2 : ℕ)) =
        ∫ t : ℝ,
          (Complex.I : ℂ) * ψT' (z₁line t) *
            cexp ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) * (z₁line t)) ∂μIoc01 := by
    simpa [μIoc01] using (J₁'_eq_integral_z₁line (r := (‖x‖ ^ (2 : ℕ))))
  rw [hJ₁μ]
  rw [(MeasureTheory.integral_const_mul
        (μ := μIoc01)
        (r := cexp (↑(-2 * Real.pi * ⟪x, w⟫) * Complex.I))
        (f := fun t : ℝ =>
          (Complex.I : ℂ) * ψT' (z₁line t) *
            cexp ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) * (z₁line t)))).symm]
  refine MeasureTheory.integral_congr_ae <| Filter.Eventually.of_forall fun t => ?_
  simp [permJ1Kernel, mul_assoc, mul_left_comm, mul_comm]

lemma norm_permJ1Kernel (w x : EuclideanSpace ℝ (Fin 8)) (t : ℝ) :
    ‖permJ1Kernel w (x, t)‖ = ‖ψT' (z₁line t)‖ * rexp (-(π * t * (‖x‖ ^ 2))) := by
  have hphase : ‖cexp ((-2 * (π * ⟪x, w⟫)) * I)‖ = (1 : ℝ) := by
    simpa using (Complex.norm_exp_ofReal_mul_I (-2 * (π * ⟪x, w⟫)))
  have hgauss :
      ‖cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t))‖ =
        rexp (-(π * t * (‖x‖ ^ 2))) := by
    simpa [z₁line, mul_assoc, mul_left_comm, mul_comm] using
      (norm_cexp_pi_mul_I_mul_sq (z := z₁line t) (x := x))
  calc
    ‖permJ1Kernel w (x, t)‖ =
        ‖cexp ((-2 * (π * ⟪x, w⟫)) * I)‖ *
          (‖ψT' (z₁line t)‖ *
            ‖cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t))‖) := by
          simp [permJ1Kernel, mul_assoc]
    _ = ‖ψT' (z₁line t)‖ * rexp (-(π * t * (‖x‖ ^ 2))) := by
          rw [hphase, hgauss]
          simp [mul_assoc]

lemma integral_norm_permJ1Kernel (w : EuclideanSpace ℝ (Fin 8))
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ1Kernel w (x, t)‖) =
      ‖ψT' (z₁line t)‖ * (1 / t) ^ (4 : ℕ) := by
  have ht0 : 0 < t := ht.1
  have hgauss :
      (∫ x : EuclideanSpace ℝ (Fin 8), rexp (-(π * (t * (‖x‖ ^ 2))))) = (1 / t) ^ (4 : ℕ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (integral_rexp_neg_pi_mul_sq_norm (t := t) ht0)
  calc
    (∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ1Kernel w (x, t)‖) =
        ∫ x : EuclideanSpace ℝ (Fin 8), ‖ψT' (z₁line t)‖ * rexp (-(π * (t * (‖x‖ ^ 2)))) := by
          refine MeasureTheory.integral_congr_ae <| Filter.Eventually.of_forall fun x => ?_
          simpa [mul_assoc] using (norm_permJ1Kernel (w := w) (x := x) (t := t))
    _ =
        ‖ψT' (z₁line t)‖ * (∫ x : EuclideanSpace ℝ (Fin 8), rexp (-(π * (t * (‖x‖ ^ 2))))) := by
          simpa [mul_assoc] using
            (MeasureTheory.integral_const_mul
              (μ := (volume : Measure (EuclideanSpace ℝ (Fin 8))))
              (r := ‖ψT' (z₁line t)‖)
              (f := fun x : EuclideanSpace ℝ (Fin 8) => rexp (-(π * (t * (‖x‖ ^ 2))))))
    _ = ‖ψT' (z₁line t)‖ * (1 / t) ^ (4 : ℕ) := by simp [hgauss]

lemma integrable_permJ1Kernel_slice (w : EuclideanSpace ℝ (Fin 8))
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 8) ↦ permJ1Kernel w (x, t))
      (volume : Measure (EuclideanSpace ℝ (Fin 8))) := by
  have hz : 0 < (z₁line t).im := by simpa [z₁line] using ht.1
  have hgauss :
      Integrable
          (fun x : EuclideanSpace ℝ (Fin 8) ↦
            cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t)))
          (volume : Measure (EuclideanSpace ℝ (Fin 8))) :=
    SpherePacking.ForMathlib.integrable_gaussian_cexp_pi_mul_I_mul (z := z₁line t) hz
  have hgauss' :
      Integrable
          (fun x : EuclideanSpace ℝ (Fin 8) ↦
            ((Complex.I : ℂ) * ψT' (z₁line t)) *
              cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t)))
        (volume : Measure (EuclideanSpace ℝ (Fin 8))) := by
    simpa [mul_assoc] using hgauss.const_mul ((Complex.I : ℂ) * ψT' (z₁line t))
  have h :=
    Integrable.bdd_mul (hg := hgauss')
      (f := fun x : EuclideanSpace ℝ (Fin 8) ↦ cexp (↑(-2 * (π * ⟪x, w⟫)) * I))
      (g := fun x : EuclideanSpace ℝ (Fin 8) ↦
        ((Complex.I : ℂ) * ψT' (z₁line t)) *
          cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t)))
      (c := (1 : ℝ)) (SpherePacking.ForMathlib.aestronglyMeasurable_phase (w := w))
      (SpherePacking.ForMathlib.ae_norm_phase_le_one (w := w))
  simpa [permJ1Kernel, mul_assoc] using h

/-- Almost-everywhere integrability of the `x`-slices of `permJ1Kernel` over `μIoc01`. -/
public lemma ae_integrable_permJ1Kernel_slice (w : EuclideanSpace ℝ (Fin 8)) :
    (∀ᵐ t : ℝ ∂μIoc01,
      Integrable (fun x : EuclideanSpace ℝ (Fin 8) ↦ permJ1Kernel w (x, t))
        (volume : Measure (EuclideanSpace ℝ (Fin 8)))) := by
  refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => ?_
  simpa using (integrable_permJ1Kernel_slice (w := w) (t := t) ht)

/-- Integrability of `t ↦ ∫ ‖permJ1Kernel w (x,t)‖ dx` over `μIoc01`. -/
public lemma integrable_integral_norm_permJ1Kernel (w : EuclideanSpace ℝ (Fin 8)) :
    Integrable (fun t : ℝ ↦ ∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ1Kernel w (x, t)‖) μIoc01 := by
  rcases MagicFunction.b.PsiBounds.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with
    ⟨Cψ, hCψ⟩
  let g : ℝ → ℝ := fun t => ‖ψT' (z₁line t)‖ * (1 / t) ^ (4 : ℕ)
  have hAE :
      (fun t : ℝ ↦ ∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ1Kernel w (x, t)‖) =ᵐ[μIoc01] g := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => ?_
    simpa [g] using (integral_norm_permJ1Kernel (w := w) (t := t) ht)
  have hψTbound :
      ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
        ‖ψT' (z₁line t)‖ ≤ (Cψ : ℝ) * rexp (-Real.pi / t) * t ^ (2 : ℕ) := by
    intro t ht
    simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using
      (MagicFunction.norm_modular_rewrite_Ioc_exp_bound (k := 2) (Cψ := Cψ) (ψS := ψS)
        (ψZ := ψT') (z := z₁line) (hCψ := hCψ)
        (hEq := fun s hs => ψT'_z₁line_eq (t := s) hs) (t := t) ht)
  have hg_int : Integrable g μIoc01 := by
    simpa [g] using
      (MagicFunction.integrable_norm_ψT'_z₁line_mul_one_div_pow_add_two
        (ψT' := ψT') (k := 2) (Cψ := Cψ) continuousOn_ψT'_z₁line hψTbound)
  exact hg_int.congr hAE.symm


end Integral_Permutations.PermJ12
end

end MagicFunction.b.Fourier
