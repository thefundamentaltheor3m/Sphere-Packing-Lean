module
public import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12CurveIntegrals
public import SpherePacking.MagicFunction.PsiTPrimeZ1
public import SpherePacking.Contour.Segments
public import SpherePacking.Integration.Measure
import SpherePacking.Integration.InvChangeOfVariables
import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.ForMathlib.FourierPhase
import SpherePacking.MagicFunction.b.Schwartz.PsiExpBounds.PsiSDecay

/-! # Kernel used to rewrite the Fourier transform of `J₁` using Fubini.

Also packages the endpoint-integrability argument on `μIoc01` for functions of the form
`t ↦ ‖ψT' (z₁line t)‖ * (1 / t) ^ (k + 2)` (see
`MagicFunction.integrable_norm_ψT'_z₁line_mul_one_div_pow_add_two`). -/

namespace MagicFunction

open scoped Interval Topology
open MeasureTheory Set Complex Real Filter
open SpherePacking.Integration (μIoc01)

noncomputable section

/-- Integrability on `μIoc01` of `t ↦ ‖ψT' (z₁line t)‖ * (1 / t)^(k+2)`, given the standard modular
bound by `exp(-π/t) * t^k`. -/
public lemma integrable_norm_ψT'_z₁line_mul_one_div_pow_add_two
    (ψT' : ℂ → ℂ) (k : ℕ) (Cψ : ℝ)
    (hcont : ContinuousOn (fun t : ℝ => ψT' (SpherePacking.Contour.z₁line t)) (Ioc (0 : ℝ) 1))
    (hbound :
      ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
        ‖ψT' (SpherePacking.Contour.z₁line t)‖ ≤ (Cψ : ℝ) * rexp (-Real.pi / t) * t ^ k) :
    Integrable
      (fun t : ℝ => ‖ψT' (SpherePacking.Contour.z₁line t)‖ * (1 / t) ^ (k + 2)) μIoc01 := by
  let g : ℝ → ℝ := fun t => ‖ψT' (SpherePacking.Contour.z₁line t)‖ * (1 / t) ^ (k + 2)
  have hmajor0 :
      IntegrableOn (fun t : ℝ ↦ (1 / t ^ 2) * rexp (-Real.pi / t)) (Ioc (0 : ℝ) 1) volume := by
    simpa using SpherePacking.Integration.integrableOn_one_div_sq_mul_exp_neg_div
      (c := Real.pi) (by simpa using Real.pi_pos)
  have hmajor :
      Integrable (fun t : ℝ ↦ (Cψ : ℝ) * ((1 / t ^ 2) * rexp (-Real.pi / t))) μIoc01 := by
    have h0' : Integrable (fun t : ℝ ↦ (1 / t ^ 2) * rexp (-Real.pi / t))
        ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)) :=
      by simpa [MeasureTheory.IntegrableOn] using hmajor0
    simpa [μIoc01, mul_assoc, mul_left_comm, mul_comm] using h0'.const_mul Cψ
  have hmeas_g : AEStronglyMeasurable g μIoc01 := by
    have hcont_inv : ContinuousOn (fun t : ℝ => (t : ℝ)⁻¹) (Ioc (0 : ℝ) 1) :=
      (continuousOn_inv₀ : ContinuousOn (fun t : ℝ => (t : ℝ)⁻¹) ({0}ᶜ)).mono
        (fun t ht => by simp [ne_of_gt ht.1])
    have hcont_g : ContinuousOn g (Ioc (0 : ℝ) 1) := by
      simpa [g, one_div] using hcont.norm.mul (hcont_inv.pow (k + 2))
    simpa [μIoc01] using hcont_g.aestronglyMeasurable
      (μ := (volume : Measure ℝ)) (s := Ioc (0 : ℝ) 1) measurableSet_Ioc
  have hg_bound :
      ∀ᵐ t : ℝ ∂μIoc01, ‖g t‖ ≤ (Cψ : ℝ) * ((1 / t ^ 2) * rexp (-Real.pi / t)) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall ?_
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht_ne0 : t ≠ 0 := ht0.ne'
    have hpow_nonneg : 0 ≤ (1 / t : ℝ) ^ (k + 2) := pow_nonneg (one_div_nonneg.2 ht0.le) (k + 2)
    have hgt0 : 0 ≤ g t := mul_nonneg (norm_nonneg _) hpow_nonneg
    have hnorm_g : ‖g t‖ = g t := by simp [Real.norm_eq_abs, abs_of_nonneg hgt0]
    have hpow_simp : (t ^ k) * (1 / t) ^ (k + 2) = 1 / t ^ (2 : ℕ) := by
      calc (t ^ k) * (1 / t) ^ (k + 2)
          = (t ^ k * (1 / t) ^ k) * (1 / t) ^ (2 : ℕ) := by simp [pow_add]; ac_rfl
        _ = ((t * (1 / t)) ^ k) * (1 / t) ^ (2 : ℕ) := by simp [mul_pow, mul_assoc]
        _ = 1 / t ^ (2 : ℕ) := by simp [one_div, ht_ne0]
    have : g t ≤ (Cψ : ℝ) * ((1 / t ^ 2) * rexp (-Real.pi / t)) := by
      have hmul := mul_le_mul_of_nonneg_right (hbound t ht) hpow_nonneg
      have hR :
          ((Cψ : ℝ) * rexp (-Real.pi / t) * t ^ k) * (1 / t) ^ (k + 2) =
            (Cψ : ℝ) * ((1 / t ^ 2) * rexp (-Real.pi / t)) := by
        calc ((Cψ : ℝ) * rexp (-Real.pi / t) * t ^ k) * (1 / t) ^ (k + 2)
            = (Cψ : ℝ) * (rexp (-Real.pi / t) * (t ^ k * (1 / t) ^ (k + 2))) := by ac_rfl
          _ = (Cψ : ℝ) * (rexp (-Real.pi / t) * (1 / t ^ (2 : ℕ))) := by
                simpa [mul_assoc] using
                  congrArg (fun u : ℝ => (Cψ : ℝ) * (rexp (-Real.pi / t) * u)) hpow_simp
          _ = (Cψ : ℝ) * ((1 / t ^ (2 : ℕ)) * rexp (-Real.pi / t)) := by ac_rfl
      exact hmul.trans_eq hR
    simpa [hnorm_g] using this
  exact Integrable.mono' hmajor hmeas_g hg_bound

end

end MagicFunction

namespace MagicFunction.b.Fourier

noncomputable section

open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral Filter
open SpherePacking.ForMathlib SpherePacking.Integration SpherePacking.Contour
open scoped FourierTransform RealInnerProductSpace Topology Real Interval

/-- Rewrite `J₁'` using the explicit line parametrisation `z₁line`. -/
public lemma J₁'_eq_integral_z₁line (r : ℝ) :
    MagicFunction.b.RealIntegrals.J₁' r =
      ∫ t in Ioc (0 : ℝ) 1,
        (Complex.I : ℂ) * ψT' (z₁line t) *
          cexp ((π : ℂ) * I * (r : ℂ) * (z₁line t)) := by
  rw [J₁'_eq_Ioc (r := r)]
  refine MeasureTheory.integral_congr_ae <|
    (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => by
      simpa [z₁line, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using
        congrArg (fun z : ℂ => (Complex.I : ℂ) * ψT' z * cexp ((π : ℂ) * I * (r : ℂ) * z))
          (z₁'_eq_of_mem (t := t) (mem_Icc_of_Ioc ht))

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
  rw [show MagicFunction.b.RealIntegrals.J₁' (‖x‖ ^ (2 : ℕ)) =
        ∫ t : ℝ,
          (Complex.I : ℂ) * ψT' (z₁line t) *
            cexp ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) * (z₁line t)) ∂μIoc01 from by
      simpa [μIoc01] using (J₁'_eq_integral_z₁line (r := (‖x‖ ^ (2 : ℕ)))),
    (MeasureTheory.integral_const_mul (μ := μIoc01)
      (r := cexp (↑(-2 * Real.pi * ⟪x, w⟫) * Complex.I))
      (f := fun t : ℝ => (Complex.I : ℂ) * ψT' (z₁line t) *
        cexp ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) * (z₁line t)))).symm]
  exact MeasureTheory.integral_congr_ae <| Filter.Eventually.of_forall fun t => by
    simp [permJ1Kernel, mul_assoc, mul_left_comm, mul_comm]

lemma integral_norm_permJ1Kernel (w : EuclideanSpace ℝ (Fin 8))
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ1Kernel w (x, t)‖) =
      ‖ψT' (z₁line t)‖ * (1 / t) ^ (4 : ℕ) := by
  rw [show (∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ1Kernel w (x, t)‖) =
        ∫ x : EuclideanSpace ℝ (Fin 8), ‖ψT' (z₁line t)‖ * rexp (-(π * (t * (‖x‖ ^ 2)))) from
      MeasureTheory.integral_congr_ae <| Filter.Eventually.of_forall fun x => by
        simpa [mul_assoc] using
          show ‖permJ1Kernel w (x, t)‖ = ‖ψT' (z₁line t)‖ * rexp (-(π * t * (‖x‖ ^ 2))) by
            rw [show ‖permJ1Kernel w (x, t)‖ =
                ‖cexp ((-2 * (π * ⟪x, w⟫)) * I)‖ *
                  (‖ψT' (z₁line t)‖ *
                    ‖cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t))‖) from by
              simp [permJ1Kernel, mul_assoc],
              show ‖cexp ((-2 * (π * ⟪x, w⟫)) * I)‖ = (1 : ℝ) by
                simpa using Complex.norm_exp_ofReal_mul_I (-2 * (π * ⟪x, w⟫)),
              show ‖cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t))‖ =
                  rexp (-(π * t * (‖x‖ ^ 2))) by
                simpa [z₁line, mul_assoc, mul_left_comm, mul_comm] using
                  norm_cexp_pi_mul_I_mul_sq (z := z₁line t) (x := x)]
            simp [mul_assoc],
    MeasureTheory.integral_const_mul ‖ψT' (z₁line t)‖ fun a ↦ rexp (-(π * (t * ‖a‖ ^ 2)))]
  simp [show (∫ x : EuclideanSpace ℝ (Fin 8), rexp (-(π * (t * (‖x‖ ^ 2))))) = (1 / t) ^ (4 : ℕ)
    from by simpa [mul_assoc, mul_left_comm, mul_comm] using
      (integral_rexp_neg_pi_mul_sq_norm (t := t) ht.1)]

lemma integrable_permJ1Kernel_slice (w : EuclideanSpace ℝ (Fin 8))
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 8) ↦ permJ1Kernel w (x, t))
      (volume : Measure (EuclideanSpace ℝ (Fin 8))) := by
  have hgauss' :
      Integrable
          (fun x : EuclideanSpace ℝ (Fin 8) ↦
            ((Complex.I : ℂ) * ψT' (z₁line t)) *
              cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t)))
        (volume : Measure (EuclideanSpace ℝ (Fin 8))) := by
    simpa [mul_assoc] using
      (SpherePacking.ForMathlib.integrable_gaussian_cexp_pi_mul_I_mul (z := z₁line t)
          (by simpa [z₁line] using ht.1)).const_mul ((Complex.I : ℂ) * ψT' (z₁line t))
  simpa [permJ1Kernel, mul_assoc] using
    Integrable.bdd_mul (hg := hgauss')
      (f := fun x : EuclideanSpace ℝ (Fin 8) ↦ cexp (↑(-2 * (π * ⟪x, w⟫)) * I))
      (g := fun x : EuclideanSpace ℝ (Fin 8) ↦
        ((Complex.I : ℂ) * ψT' (z₁line t)) *
          cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t)))
      (c := (1 : ℝ)) (SpherePacking.ForMathlib.aestronglyMeasurable_phase (w := w))
      (SpherePacking.ForMathlib.ae_norm_phase_le_one (w := w))

/-- Almost-everywhere integrability of the `x`-slices of `permJ1Kernel` over `μIoc01`. -/
public lemma ae_integrable_permJ1Kernel_slice (w : EuclideanSpace ℝ (Fin 8)) :
    (∀ᵐ t : ℝ ∂μIoc01,
      Integrable (fun x : EuclideanSpace ℝ (Fin 8) ↦ permJ1Kernel w (x, t))
        (volume : Measure (EuclideanSpace ℝ (Fin 8)))) :=
  (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => by
    simpa using integrable_permJ1Kernel_slice (w := w) (t := t) ht

/-- Integrability of `t ↦ ∫ ‖permJ1Kernel w (x,t)‖ dx` over `μIoc01`. -/
public lemma integrable_integral_norm_permJ1Kernel (w : EuclideanSpace ℝ (Fin 8)) :
    Integrable (fun t : ℝ ↦ ∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ1Kernel w (x, t)‖) μIoc01 := by
  rcases MagicFunction.b.PsiBounds.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with
    ⟨Cψ, hCψ⟩
  let g : ℝ → ℝ := fun t => ‖ψT' (z₁line t)‖ * (1 / t) ^ (4 : ℕ)
  have hAE :
      (fun t : ℝ ↦ ∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ1Kernel w (x, t)‖) =ᵐ[μIoc01] g :=
    (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => by
      simpa [g] using (integral_norm_permJ1Kernel (w := w) (t := t) ht)
  refine (show Integrable g μIoc01 from ?_).congr hAE.symm
  simpa [g] using
    MagicFunction.integrable_norm_ψT'_z₁line_mul_one_div_pow_add_two
      (ψT' := ψT') (k := 2) (Cψ := Cψ) continuousOn_ψT'_z₁line fun t ht => by
        simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using
          MagicFunction.norm_modular_rewrite_Ioc_exp_bound (k := 2) (Cψ := Cψ) (ψS := ψS)
            (ψZ := ψT') (z := z₁line) (hCψ := hCψ)
            (hEq := fun s hs => ψT'_z₁line_eq (t := s) hs) (t := t) ht

end

end MagicFunction.b.Fourier
