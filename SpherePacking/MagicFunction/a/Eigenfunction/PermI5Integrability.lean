module
public import SpherePacking.MagicFunction.a.Eigenfunction.PermI5Kernel
import SpherePacking.ForMathlib.GaussianFourierCommon
public import SpherePacking.ForMathlib.GaussianRexpIntegral
public import SpherePacking.ForMathlib.GaussianRexpIntegrable
public import SpherePacking.Integration.Measure
import SpherePacking.MagicFunction.a.IntegralEstimates.I3
import SpherePacking.ForMathlib.IntegrablePowMulExp
import SpherePacking.ForMathlib.IntegralProd

/-!
# Integrability for the `I₅` Fourier kernel

We prove integrability and domination bounds for `permI5Kernel`, and record the Gaussian phase
integral used to evaluate the Fourier transform of `I₅`.

## Main statements
* `integrable_perm_I₅_kernel`
* `integral_phase_gaussian`
-/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter
open SpherePacking.ForMathlib SpherePacking.Integration

section Integral_Permutations

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section PermI5

open MeasureTheory Set Complex Real

/-- Cancellation lemma for the normalization factor `s ^ (-4)` appearing in `permI5Kernel`. -/
public lemma zpow_neg_four_mul_pow_four (s : ℝ) (hs : s ≠ 0) :
    ((s : ℂ) ^ (-4 : ℤ)) * (s ^ 4 : ℂ) = 1 := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  simpa using (zpow_neg_mul_zpow_self (a := (s : ℂ)) (n := (4 : ℤ)) hsC)

lemma integrable_permI5Kernel_slice (w : ℝ⁸) (s : ℝ) (hs : 1 ≤ s) :
    Integrable (fun x : ℝ⁸ ↦ permI5Kernel w (x, s)) (volume : Measure ℝ⁸) := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hmajor :
      Integrable (fun x : ℝ⁸ ↦ ‖φ₀'' (I * (s : ℂ))‖ * rexp (-π * (‖x‖ ^ 2) / s))
        (volume : Measure ℝ⁸) := by
    simpa [mul_assoc] using
      (integrable_gaussian_rexp (s := s) hs0).const_mul ‖φ₀'' (I * (s : ℂ))‖
  have hmeas : AEStronglyMeasurable (fun x : ℝ⁸ ↦ permI5Kernel w (x, s)) (volume : Measure ℝ⁸) := by
    -- Avoid `measurability` timeouts: the integrand is continuous in `x`.
    have hphase : Continuous fun x : ℝ⁸ => permI5Phase w x := by
      have hinner : Continuous fun x : ℝ⁸ => (⟪x, w⟫ : ℝ) := by
        simpa using (continuous_id.inner continuous_const)
      have harg :
          Continuous fun x : ℝ⁸ =>
              (↑(((-2 : ℝ) * ((π : ℝ) * (⟪x, w⟫ : ℝ)))) : ℂ) * I :=
        (Complex.continuous_ofReal.comp (continuous_const.mul (continuous_const.mul hinner))).mul
          continuous_const
      simpa [permI5Phase, mul_assoc, mul_left_comm, mul_comm] using harg.cexp
    have hs_mem : s ∈ Ici (1 : ℝ) := by
      simpa [Set.mem_Ici] using hs
    have hpair_cont : Continuous fun x : ℝ⁸ => (x, s) := continuous_id.prodMk continuous_const
    have hpair_on : ContinuousOn (fun x : ℝ⁸ => (x, s)) (univ : Set ℝ⁸) :=
      hpair_cont.continuousOn
    have hmaps : MapsTo (fun x : ℝ⁸ => (x, s)) (univ : Set ℝ⁸) (univ ×ˢ Ici (1 : ℝ)) := by
      intro x hx
      refine ⟨Set.mem_univ _, hs_mem⟩
    have hg : Continuous fun x : ℝ⁸ => MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s := by
      have hg_on :
          ContinuousOn (fun x : ℝ⁸ => MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s)
            (univ : Set ℝ⁸) := by
        simpa using (continuousOn_I₅_g.comp hpair_on hmaps)
      simpa [continuousOn_univ] using hg_on
    have hcont : Continuous fun x : ℝ⁸ => permI5Kernel w (x, s) := by
      simpa [permI5Kernel] using hphase.mul hg
    exact hcont.aestronglyMeasurable
  refine Integrable.mono' hmajor hmeas ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  have hnorm :
      ‖permI5Kernel w (x, s)‖ = ‖MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s‖ := by
    simp [permI5Kernel, permI5Phase, norm_exp]
  have hbnd :
      ‖MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s‖ ≤
        ‖φ₀'' (I * (s : ℂ))‖ * rexp (-π * (‖x‖ ^ 2) / s) := by
    have hπ' : ‖cexp ((((π * (‖x‖ ^ 2)) : ℝ) : ℂ) * I)‖ = (1 : ℝ) :=
      norm_exp_ofReal_mul_I (π * (‖x‖ ^ 2))
    have hπ : ‖cexp (π * I * (‖x‖ ^ 2))‖ = (1 : ℝ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hπ'
    have hnormg :
        ‖MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s‖ =
          ‖MagicFunction.a.IntegralEstimates.I₃.g (‖x‖ ^ 2) s‖ := by
      have hI3 :
          MagicFunction.a.IntegralEstimates.I₃.g (‖x‖ ^ 2) s =
            MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s * cexp (π * I * (‖x‖ ^ 2)) := by
        simp [MagicFunction.a.IntegralEstimates.I₃.g, MagicFunction.a.IntegralEstimates.I₅.g,
          mul_assoc, mul_left_comm, mul_comm]
      -- Multiply by a unit-modulus factor.
      calc
        ‖MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s‖
            =
            ‖MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s‖ *
              ‖cexp (π * I * (‖x‖ ^ 2))‖ := by simp [hπ]
        _ =
            ‖MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s *
                cexp (π * I * (‖x‖ ^ 2))‖ := by
              simp
        _ = ‖MagicFunction.a.IntegralEstimates.I₃.g (‖x‖ ^ 2) s‖ := by
              simp [hI3]
    have hbnd3 :=
      MagicFunction.a.IntegralEstimates.I₃.I₃'_bounding_aux_1 (r := ‖x‖ ^ 2) s hs
    exact le_of_eq_of_le hnormg hbnd3
  exact hnorm.le.trans hbnd

lemma integral_norm_permI5Kernel_bound (w : ℝ⁸) (s : ℝ) (hs : 1 ≤ s) :
    (∫ x : ℝ⁸, ‖permI5Kernel w (x, s)‖) ≤ ‖φ₀'' (I * (s : ℂ))‖ * s ^ 4 := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hgauss_int : (∫ x : ℝ⁸, rexp (-π * (‖x‖ ^ 2) / s)) = s ^ 4 :=
    SpherePacking.ForMathlib.integral_gaussian_rexp (s := s) hs0
  have hf_nonneg :
      0 ≤ᵐ[(volume : Measure ℝ⁸)] fun x : ℝ⁸ ↦ ‖permI5Kernel w (x, s)‖ :=
    Filter.Eventually.of_forall (fun _ => norm_nonneg _)
  have hgi :
      Integrable (fun x : ℝ⁸ ↦ ‖φ₀'' (I * (s : ℂ))‖ * rexp (-π * (‖x‖ ^ 2) / s))
        (volume : Measure ℝ⁸) := by
    simpa [mul_assoc] using
      (integrable_gaussian_rexp (s := s) hs0).const_mul ‖φ₀'' (I * (s : ℂ))‖
  have hle :
      (fun x : ℝ⁸ ↦ ‖permI5Kernel w (x, s)‖) ≤ᵐ[volume] fun x : ℝ⁸ ↦
        ‖φ₀'' (I * (s : ℂ))‖ * rexp (-π * (‖x‖ ^ 2) / s) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hnorm :
        ‖permI5Kernel w (x, s)‖ = ‖MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s‖ := by
      simp [permI5Kernel, permI5Phase, norm_exp]
    have hbnd :
        ‖MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s‖ ≤
          ‖φ₀'' (I * (s : ℂ))‖ * rexp (-π * (‖x‖ ^ 2) / s) := by
      have hπ' : ‖cexp ((((π * (‖x‖ ^ 2)) : ℝ) : ℂ) * I)‖ = (1 : ℝ) :=
        norm_exp_ofReal_mul_I (π * (‖x‖ ^ 2))
      have hπ : ‖cexp (π * I * (‖x‖ ^ 2))‖ = (1 : ℝ) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hπ'
      have hnormg :
          ‖MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s‖ =
            ‖MagicFunction.a.IntegralEstimates.I₃.g (‖x‖ ^ 2) s‖ := by
        have hI3 :
            MagicFunction.a.IntegralEstimates.I₃.g (‖x‖ ^ 2) s =
              MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s * cexp (π * I * (‖x‖ ^ 2)) := by
          simp [MagicFunction.a.IntegralEstimates.I₃.g, MagicFunction.a.IntegralEstimates.I₅.g,
            mul_assoc, mul_left_comm, mul_comm]
        calc
          ‖MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s‖
              =
              ‖MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s‖ *
                ‖cexp (π * I * (‖x‖ ^ 2))‖ := by simp [hπ]
          _ =
              ‖MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s *
                  cexp (π * I * (‖x‖ ^ 2))‖ := by
                simp
          _ = ‖MagicFunction.a.IntegralEstimates.I₃.g (‖x‖ ^ 2) s‖ := by
                simp [hI3]
      have hbnd3 :=
        MagicFunction.a.IntegralEstimates.I₃.I₃'_bounding_aux_1 (r := ‖x‖ ^ 2) s hs
      exact le_of_eq_of_le hnormg hbnd3
    exact hnorm.le.trans hbnd
  have hmono :=
    MeasureTheory.integral_mono_of_nonneg (μ := (volume : Measure ℝ⁸)) hf_nonneg hgi hle
  calc
    (∫ x : ℝ⁸, ‖permI5Kernel w (x, s)‖)
        ≤ ∫ x : ℝ⁸, ‖φ₀'' (I * (s : ℂ))‖ * rexp (-π * (‖x‖ ^ 2) / s) := hmono
    _ = ‖φ₀'' (I * (s : ℂ))‖ * s ^ 4 := by
      -- Pull out the constant and use the Gaussian integral.
      have hexp :
          (fun x : ℝ⁸ ↦ rexp (-(π * (‖x‖ ^ 2)) / s)) =
            fun x : ℝ⁸ ↦ rexp (-π * (‖x‖ ^ 2) / s) := by
        funext x
        simp [div_eq_mul_inv, mul_left_comm, mul_comm]
      have hgauss_int' : (∫ x : ℝ⁸, rexp (-(π * (‖x‖ ^ 2)) / s)) = s ^ 4 := by
        simpa [hexp] using hgauss_int
      have :
          (∫ x : ℝ⁸, ‖φ₀'' (I * (s : ℂ))‖ * rexp (-(π * (‖x‖ ^ 2)) / s)) =
            ‖φ₀'' (I * (s : ℂ))‖ * ∫ x : ℝ⁸, rexp (-(π * (‖x‖ ^ 2)) / s) := by
        exact integral_const_mul ‖φ₀'' (I * ↑s)‖ fun a => rexp (-(π * ‖a‖ ^ 2) / s)
      simp [this, hgauss_int']

lemma ae_integrable_permI5Kernel_slice (w : ℝ⁸) :
    (∀ᵐ s : ℝ ∂μIciOne, Integrable (fun x : ℝ⁸ ↦ permI5Kernel w (x, s)) (volume : Measure ℝ⁸)) := by
  refine (ae_restrict_iff' measurableSet_Ici).2 <| Filter.Eventually.of_forall ?_
  intro s hs
  exact integrable_permI5Kernel_slice (w := w) (s := s) hs

lemma integrable_integral_norm_permI5Kernel (w : ℝ⁸) :
    Integrable (fun s : ℝ ↦ ∫ x : ℝ⁸, ‖permI5Kernel w (x, s)‖) μIciOne := by
  -- Build the dominated function `Cφ * s^4 * exp(-2π s)`.
  have hmajor :
      Integrable
        (fun s : ℝ ↦
          (MagicFunction.a.Schwartz.I1Decay.Cφ : ℝ) * s ^ 4 * rexp (-2 * π * s))
        μIciOne := by
    have hb : 0 < (2 * π) := by positivity
    have harg : ∀ s : ℝ, (-(2 * π) * s) = (-2 * π * s) := by
      intro s
      ring
    have hIci :
        IntegrableOn (fun s : ℝ ↦ s ^ 4 * rexp (-(2 * π) * s)) (Set.Ici (1 : ℝ)) volume := by
      simpa using
        (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 4) (b := (2 * π)) hb)
    have hIci' :
        IntegrableOn
          (fun s : ℝ ↦
            (MagicFunction.a.Schwartz.I1Decay.Cφ : ℝ) * s ^ 4 * rexp (-2 * π * s))
          (Set.Ici (1 : ℝ)) volume := by
      have :
          IntegrableOn
            (fun s : ℝ ↦
              (MagicFunction.a.Schwartz.I1Decay.Cφ : ℝ) *
                (s ^ 4 * rexp (-(2 * π) * s)))
            (Set.Ici (1 : ℝ)) volume := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hIci.const_mul _
      simpa [mul_assoc, mul_left_comm, mul_comm, harg] using this
    simpa [μIciOne, IntegrableOn, mul_assoc, mul_left_comm, mul_comm] using hIci'
  -- `s ↦ ∫ ‖kernel‖` is a.e. strongly measurable by Fubini-measurability.
  haveI : MeasureTheory.SFinite μIciOne := by
    dsimp [μIciOne]
    infer_instance
  have hmeas :
      AEStronglyMeasurable (fun s : ℝ ↦ ∫ x : ℝ⁸, ‖permI5Kernel w (x, s)‖) μIciOne := by
    have hker :
        AEStronglyMeasurable (permI5Kernel w) ((volume : Measure ℝ⁸).prod μIciOne) := by
      simpa [μIciOne] using (aestronglyMeasurable_perm_I₅_kernel (w := w))
    simpa using
      (SpherePacking.ForMathlib.aestronglyMeasurable_integral_norm_prod_right'
        (μ := μIciOne) (ν := (volume : Measure ℝ⁸)) (f := permI5Kernel w) hker)
  refine Integrable.mono' hmajor hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
  intro s hs
  have hkernel := integral_norm_permI5Kernel_bound (w := w) (s := s) hs
  have hφ := MagicFunction.a.Schwartz.I1Decay.norm_φ₀''_le (s := s) hs
  have hbound :
      ‖∫ x : ℝ⁸, ‖permI5Kernel w (x, s)‖‖ ≤
        (MagicFunction.a.Schwartz.I1Decay.Cφ : ℝ) * s ^ 4 * rexp (-2 * π * s) := by
    have hn0 : 0 ≤ ∫ x : ℝ⁸, ‖permI5Kernel w (x, s)‖ := by
      exact MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
    -- turn the desired estimate into one without `‖·‖`
    have habs :
        ‖∫ x : ℝ⁸, ‖permI5Kernel w (x, s)‖‖ = ∫ x : ℝ⁸, ‖permI5Kernel w (x, s)‖ := by
      simp [Real.norm_eq_abs, abs_of_nonneg hn0]
    -- combine the kernel bound with the decay of `φ₀''`
    have : ∫ x : ℝ⁸, ‖permI5Kernel w (x, s)‖ ≤
        (MagicFunction.a.Schwartz.I1Decay.Cφ : ℝ) * s ^ 4 * rexp (-2 * π * s) := by
      have : ∫ x : ℝ⁸, ‖permI5Kernel w (x, s)‖ ≤ ‖φ₀'' (I * (s : ℂ))‖ * s ^ 4 := hkernel
      have : ∫ x : ℝ⁸, ‖permI5Kernel w (x, s)‖ ≤
          ((MagicFunction.a.Schwartz.I1Decay.Cφ : ℝ) * rexp (-2 * π * s)) * s ^ 4 := by
        have hs_nonneg : 0 ≤ s ^ 4 := pow_nonneg (le_trans (by norm_num) hs) 4
        exact this.trans (mul_le_mul_of_nonneg_right hφ hs_nonneg)
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    simpa [habs] using this
  simpa using hbound

/-- Integrability of `permI5Kernel` on the product measure `volume × μIciOne`. -/
public lemma integrable_perm_I₅_kernel (w : ℝ⁸) :
    Integrable
      (permI5Kernel w)
      ((volume : Measure ℝ⁸).prod μIciOne) := by
  haveI : MeasureTheory.SFinite μIciOne := by
    dsimp [μIciOne]
    infer_instance
  have hmeas :
      AEStronglyMeasurable (permI5Kernel w) ((volume : Measure ℝ⁸).prod μIciOne) := by
    simpa [μIciOne] using (aestronglyMeasurable_perm_I₅_kernel (w := w))
  refine
    (MeasureTheory.integrable_prod_iff' (μ := (volume : Measure ℝ⁸)) (ν := μIciOne) hmeas).2 ?_
  exact ⟨ae_integrable_permI5Kernel_slice (w := w), integrable_integral_norm_permI5Kernel (w := w)⟩

/-- The phase-shifted Gaussian integral used in the computation of `𝓕 I₅`. -/
public lemma integral_phase_gaussian (w : ℝ⁸) (s : ℝ) (hs0 : 0 < s) :
  (∫ x : ℝ⁸,
        cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
          cexp (-π * (‖x‖ ^ 2) / s)) =
      (s ^ 4 : ℂ) * cexp (-π * (‖w‖ ^ 2) * s) := by
  have h :=
    _root_.SpherePacking.ForMathlib.fourier_gaussian_norm_sq_div_even (k := 4) (s := s) hs0 (w := w)
  rw [fourier_eq' (fun v : ℝ⁸ ↦ cexp (-π * (‖v‖ ^ 2) / s)) w] at h
  simpa [smul_eq_mul, mul_assoc] using h


end Integral_Permutations.PermI5
end
end MagicFunction.a.Fourier
