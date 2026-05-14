module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import SpherePacking.MagicFunction.g.CohnElkies.Defs
public import SpherePacking.MagicFunction.g.CohnElkies.LaplaceLemmas
public import SpherePacking.MagicFunction.a.Schwartz.DecayI1
public import SpherePacking.ModularForms.PhiTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import SpherePacking.MagicFunction.a.Schwartz.Basic
public import SpherePacking.MagicFunction.a.Basic
public import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.IntegralEstimates.I2
import SpherePacking.Integration.Measure
public import
  SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Cancellation.Integrability
import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
import SpherePacking.ForMathlib.ModularFormsHelpers
import SpherePacking.MagicFunction.a.SpecialValues
import SpherePacking.ModularForms.PhiTransformLemmas

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic


/-!
# Laplace-type integrals and analytic continuation for `AnotherIntegral.A`

Explicit evaluations and integrability facts for basic Laplace-type integrals on `t > 0`,
in the complex-valued form used by the "another integral" representation of `a'`. Also includes
the analytic-continuation step that extends the "another integral" identity for `a'` from `u > 2`
to all real `0 < u` with `u ≠ 2`.

This file also provides the generic analytic-continuation wrapper used by both the `a'` and `b'`
representations: the punctured right half-plane `ACDomain = {u : ℂ | 0 < re u} \ {2}` and the
theorem `analytic_continuation_of_gt2`.

Also contains the Laplace representation for `a'` (merged from `LaplaceA/LaplaceRepresentation`):
the tail-deformation lemma `I₂'_add_I₄'_add_I₆'_eq_imag_axis_tail` and the main theorem
`aRadial_eq_laplace_phi0_main`.

Includes the complex analytic extension `aPrimeC` of `a'` (merged from `APrimeExtension`):
complexified integrals `I₁'C` ... `I₆'C`, their sum `aPrimeC`, and analyticity on the right
half-plane.

## Main definitions
* `ACDomain`, `aAnotherBase`, `aAnotherIntegrandC`, `aAnotherIntegralC`, `aAnotherRHS`
* `rightHalfPlane`, `aPrimeC`

## Main statements
* `analytic_continuation_of_gt2`
* `aRadial_eq_another_integral_analytic_continuation_of_gt2`
* `I₂'_add_I₄'_add_I₆'_eq_imag_axis_tail`, `aRadial_eq_laplace_phi0_main`
* `aPrimeC_ofReal`, `aPrimeC_analyticOnNhd`
-/

namespace SpherePacking

/-- The open right half-plane `{u : ℂ | 0 < u.re}`. -/
@[expose] public def rightHalfPlane : Set ℂ := {u : ℂ | 0 < u.re}

/-- The right half-plane is an open subset of `ℂ`. -/
public lemma rightHalfPlane_isOpen : IsOpen rightHalfPlane := by
  simpa [rightHalfPlane] using (isOpen_Ioi.preimage Complex.continuous_re)

end SpherePacking

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators UpperHalfPlane Topology intervalIntegral
open MeasureTheory Real Complex Filter MagicFunction.FourierEigenfunctions
  MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrals
  MagicFunction.a.RealIntegrands MagicFunction.Parametrisations

/-! ## Laplace integrand and convergence (merged from `LaplaceA.Basic`) -/

noncomputable section LaplaceIntegrand

/-- The Laplace integrand appearing in the representation of the radial profile `a'`. -/
@[expose] public def aLaplaceIntegrand (u t : ℝ) : ℂ :=
  ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) * Real.exp (-π * u * t)

lemma continuousOn_phi0''_div_Ioi :
    ContinuousOn (fun t : ℝ => φ₀'' ((Complex.I : ℂ) / (t : ℂ))) (Set.Ioi (0 : ℝ)) :=
  MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn.comp
    (continuousOn_const.div Complex.continuous_ofReal.continuousOn fun _ ht => mod_cast ht.ne')
    fun _ ht => by simp_all

/-- Integrability of `t^2 * exp(-a * t)` on a ray `Set.Ioi A` (for `0 < a`). -/
public lemma integrableOn_sq_mul_exp_neg (A a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-a * t)) (Set.Ioi A) :=
  integrable_of_isBigO_exp_neg (a := A) (b := a / 2) (half_pos ha) (by fun_prop)
    (((isLittleO_pow_exp_pos_mul_atTop (k := 2) (half_pos ha)).isBigO.mul
      (Asymptotics.isBigO_refl _ _)).congr_right fun t => by rw [← Real.exp_add]; congr 1; ring)

/-- Convergence of the Laplace integral defining `a'` (integrability on `(0, ∞)` for `u > 2`). -/
public lemma aLaplaceIntegral_convergent {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioi (0 : ℝ)) := by
  have hMeasIoi : AEStronglyMeasurable (fun t : ℝ => aLaplaceIntegrand u t)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have ht2 : AEStronglyMeasurable (fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      ((continuous_ofReal.comp (continuous_id.pow 2)).aestronglyMeasurable
          (μ := (volume : Measure ℝ))).mono_measure Measure.restrict_le_self
    simpa [aLaplaceIntegrand, mul_assoc] using
      (ht2.mul (continuousOn_phi0''_div_Ioi.aestronglyMeasurable measurableSet_Ioi)).mul
        (by fun_prop : AEStronglyMeasurable (fun t : ℝ => (Real.exp (-π * u * t) : ℂ))
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
  have hsmall : IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioc (0 : ℝ) 1) := by
    let C₀ : ℝ := MagicFunction.a.Schwartz.I1Decay.Cφ
    refine MeasureTheory.IntegrableOn.of_bound (by simp : (MeasureTheory.volume : Measure ℝ)
      (Set.Ioc (0 : ℝ) 1) < ⊤)
      (hMeasIoi.mono_measure <| Measure.restrict_mono_set (MeasureTheory.volume : Measure ℝ)
        fun t ht => ht.1) C₀ ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => ?_
    have ht0 : 0 < t := ht.1
    have hC₀ : 0 ≤ C₀ := MagicFunction.a.Schwartz.I1Decay.Cφ_pos.le
    have hφ₀'' : ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ ≤ C₀ :=
      (show ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ ≤ C₀ * rexp (-2 * π * t⁻¹) by
        simpa [div_eq_mul_inv, Complex.ofReal_inv, C₀] using
          MagicFunction.a.Schwartz.I1Decay.norm_φ₀''_le (s := t⁻¹)
            (one_le_inv_iff₀.2 ⟨ht0, ht.2⟩)).trans <| by
        simpa using mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, inv_nonneg.2 ht0.le])) hC₀
    have ht2_le : ‖((t ^ (2 : ℕ) : ℝ) : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real] using
        pow_le_one₀ (n := 2) (abs_nonneg t) (by simpa [abs_of_pos ht0] using ht.2)
    have hexp_le : ‖(Real.exp (-π * u * t) : ℂ)‖ ≤ 1 := by
      rw [show ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-π * u * t) by
        simpa [Complex.ofReal_exp] using Complex.norm_exp (-(π * u * t : ℂ))]
      exact Real.exp_le_one_iff.2
        (by linarith [mul_nonneg (mul_nonneg Real.pi_pos.le (lt_trans two_pos hu).le) ht0.le])
    calc ‖aLaplaceIntegrand u t‖
          ≤ ‖((t ^ (2 : ℕ) : ℝ) : ℂ)‖ *
            ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ *
              ‖(Real.exp (-π * u * t) : ℂ)‖ := by simp [aLaplaceIntegrand, mul_assoc]
      _ ≤ 1 * C₀ * 1 := by gcongr
      _ = C₀ := by ring
  have htail : IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioi (1 : ℝ)) := by
    rcases (UpperHalfPlane.isBoundedAtImInfty_iff).1 E₂_isBoundedAtImInfty with ⟨B2, A2, hB2⟩
    rcases (UpperHalfPlane.isBoundedAtImInfty_iff).1 (ModularFormClass.bdd_at_infty E₄) with
      ⟨B4, A4, hB4⟩
    rcases (UpperHalfPlane.isBoundedAtImInfty_iff).1 (ModularFormClass.bdd_at_infty E₆) with
      ⟨B6, A6, hB6⟩
    obtain ⟨CΔ, AΔ, hCΔpos, hΔinv⟩ := exists_inv_Delta_bound_exp
    let A : ℝ := max (1 : ℝ) (max AΔ (max A2 (max A4 A6)))
    have hA1 : (1 : ℝ) ≤ A := le_max_left _ _
    have hmid : IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioc (1 : ℝ) A) :=
      (((show ContinuousOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioi (0 : ℝ)) by
          simpa [aLaplaceIntegrand, mul_assoc] using
            (((by fun_prop : Continuous fun t : ℝ ↦ ((t ^ (2 : ℕ) : ℝ) : ℂ)
              ).continuousOn.mul continuousOn_phi0''_div_Ioi).mul
              (by fun_prop : Continuous fun t : ℝ ↦ (Real.exp (-π * u * t) : ℂ)).continuousOn)
        ).mono fun _ ht => lt_of_lt_of_le one_pos ht.1).integrableOn_Icc
        (μ := MeasureTheory.volume)).mono_set Set.Ioc_subset_Icc_self
    have hbig : IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioi A) := by
      let a : ℝ := π * (u - 2)
      have ha : 0 < a := mul_pos Real.pi_pos (sub_pos.2 hu)
      let BA : ℝ := B2 * B4 + B6
      let C2 : ℝ := ‖(12 * Complex.I : ℂ) / (π : ℂ)‖
      let C4 : ℝ := ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))‖
      let Cφ : ℝ := (BA ^ (2 : ℕ) + C2 * (B4 * BA) + C4 * (B4 ^ (2 : ℕ))) * CΔ
      have hdomReal : Integrable (fun t : ℝ => Cφ * (t ^ (2 : ℕ) * Real.exp (-a * t)))
            (MeasureTheory.volume.restrict (Set.Ioi A)) :=
        (integrableOn_sq_mul_exp_neg A a ha).const_mul Cφ
      have hdom :
          ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi A)),
            ‖aLaplaceIntegrand u t‖ ≤ Cφ * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by
        refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
        intro t ht
        have ht1 : (1 : ℝ) ≤ t := hA1.trans ht.le
        have ht0 : 0 < t := zero_lt_one.trans_le ht1
        let zH : ℍ := ⟨(Complex.I : ℂ) * (t : ℂ), by simpa using ht0⟩
        have hz_im : zH.im = t := by simp [zH, UpperHalfPlane.im]
        have htAim : A ≤ zH.im := hz_im ▸ ht.le
        have hAle : AΔ ≤ A ∧ A2 ≤ A ∧ A4 ≤ A ∧ A6 ≤ A := by dsimp [A]; simp
        have hE4 : ‖E₄ zH‖ ≤ B4 := hB4 zH (hAle.2.2.1.trans htAim)
        have hΔ : ‖(Δ zH)⁻¹‖ ≤ CΔ * Real.exp (2 * π * t) := by
          simpa [hz_im] using hΔinv zH (hAle.1.trans htAim)
        have hAterm : ‖E₂ zH * E₄ zH - E₆ zH‖ ≤ BA :=
          norm_sub_le_of_le (norm_mul_le_of_le (hB2 zH (hAle.2.1.trans htAim)) hE4)
            (hB6 zH (hAle.2.2.2.trans htAim))
        have hBA_nonneg : 0 ≤ BA := le_trans (norm_nonneg _) hAterm
        have hB4_nonneg : 0 ≤ B4 := le_trans (norm_nonneg _) hE4
        have hφ0 : ‖φ₀ zH‖ ≤ (BA ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t)) := by
          rw [show ‖φ₀ zH‖ = ‖(E₂ zH * E₄ zH - E₆ zH) ^ (2 : ℕ)‖ * ‖(Δ zH)⁻¹‖ by
            simp [φ₀, div_eq_mul_inv]]
          refine mul_le_mul ?_ hΔ (norm_nonneg _) (pow_nonneg hBA_nonneg _)
          simpa [norm_pow, pow_two] using mul_le_mul hAterm hAterm (norm_nonneg _) hBA_nonneg
        have hφ2 : ‖φ₂' zH‖ ≤ (B4 * BA) * (CΔ * Real.exp (2 * π * t)) := by
          rw [show ‖φ₂' zH‖ = (‖E₄ zH‖ * ‖E₂ zH * E₄ zH - E₆ zH‖) * ‖(Δ zH)⁻¹‖ by
            simp [φ₂', div_eq_mul_inv, mul_assoc]]
          exact mul_le_mul (mul_le_mul hE4 hAterm (norm_nonneg _) hB4_nonneg) hΔ
            (norm_nonneg _) (mul_nonneg hB4_nonneg hBA_nonneg)
        have hφ4 : ‖φ₄' zH‖ ≤ (B4 ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t)) := by
          rw [show ‖φ₄' zH‖ = ‖(E₄ zH) ^ (2 : ℕ)‖ * ‖(Δ zH)⁻¹‖ by simp [φ₄', div_eq_mul_inv]]
          refine mul_le_mul ?_ hΔ (norm_nonneg _) (pow_nonneg hB4_nonneg _)
          simpa [norm_pow, pow_two] using mul_le_mul hE4 hE4 (norm_nonneg _) hB4_nonneg
        have hphiS : φ₀'' ((Complex.I : ℂ) / (t : ℂ)) = φ₀ (ModularGroup.S • zH) :=
          (congrArg φ₀'' ((ModularGroup.coe_S_smul (z := zH)).trans
            (by simp [zH, div_eq_mul_inv, mul_inv_rev, mul_comm])).symm).trans
            (φ₀''_coe_upperHalfPlane (z := ModularGroup.S • zH))
        have hz_norm : ‖(zH : ℂ)‖ = t := by simp [zH, abs_of_pos ht0]
        have hz_inv : ‖(zH : ℂ)⁻¹‖ ≤ 1 := by
          simpa [norm_inv] using inv_le_one_of_one_le₀ (by simpa [hz_norm] using ht1)
        have hz2_inv : ‖((zH : ℂ) ^ (2 : ℕ))⁻¹‖ ≤ 1 := by
          simpa [norm_inv] using inv_le_one_of_one_le₀
            (by simpa [norm_pow, hz_norm] using (one_le_pow₀ ht1 : (1 : ℝ) ≤ t ^ (2 : ℕ)))
        have hcoeff2 : ‖(12 * Complex.I : ℂ) / (π * (zH : ℂ))‖ ≤ C2 :=
          calc ‖(12 * Complex.I : ℂ) / (π * (zH : ℂ))‖
                = ‖(12 * Complex.I : ℂ) / (π : ℂ)‖ * ‖(zH : ℂ)⁻¹‖ := by
                  simp [show (12 * Complex.I : ℂ) / (π * (zH : ℂ)) =
                    ((12 * Complex.I : ℂ) / (π : ℂ)) * (zH : ℂ)⁻¹ from by
                    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, mul_inv_rev]]
            _ ≤ C2 * 1 := by gcongr
            _ = C2 := by simp
        have hcoeff4 : ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ))‖ ≤ C4 :=
          calc ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ))‖
                = ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))‖ * ‖((zH : ℂ) ^ (2 : ℕ))⁻¹‖ := by
                  simp [show (36 : ℂ) / ((π : ℂ) ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) =
                    ((36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * ((zH : ℂ) ^ (2 : ℕ))⁻¹ from by
                    simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_inv_rev]]
            _ ≤ C4 * 1 := by gcongr
            _ = C4 := by simp
        have hphi_bound : ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ ≤ Cφ * Real.exp (2 * π * t) := by
          have htri : ‖φ₀ (ModularGroup.S • zH)‖ ≤
              ‖φ₀ zH‖ + ‖(12 * Complex.I) / (π * (zH : ℂ)) * φ₂' zH‖ +
                ‖36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH‖ := by
            rw [show φ₀ (ModularGroup.S • zH) = φ₀ zH - (12 * Complex.I) / (π * zH) * φ₂' zH
                - 36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH by simpa using φ₀_S_transform zH]
            exact (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
          have h2 := norm_mul_le_of_le hcoeff2 hφ2
          have h4 := norm_mul_le_of_le hcoeff4 hφ4
          grind only
        have hExpRew : Real.exp (2 * π * t) * Real.exp (-π * u * t) = Real.exp (-a * t) := by
          simpa [a, mul_assoc, mul_left_comm, mul_comm] using
            exp_two_pi_mul_mul_exp_neg_pi_mul (u := u) (t := t)
        calc ‖aLaplaceIntegrand u t‖
              ≤ ‖((t ^ (2 : ℕ) : ℝ) : ℂ)‖ *
                ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ *
                  ‖(Real.exp (-π * u * t) : ℂ)‖ := by simp [aLaplaceIntegrand, mul_assoc]
          _ ≤ (t ^ (2 : ℕ)) * (Cφ * Real.exp (2 * π * t)) * Real.exp (-π * u * t) := by
                rw [show ‖((t ^ (2 : ℕ) : ℝ) : ℂ)‖ = t ^ (2 : ℕ) from by simp [Complex.norm_real],
                  show ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-π * u * t) from by
                    simp [Complex.ofReal_exp, Complex.norm_exp, mul_assoc]]
                gcongr
          _ = Cφ * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by rw [← hExpRew]; ring
      exact MeasureTheory.Integrable.mono' (μ := MeasureTheory.volume.restrict (Set.Ioi A))
        hdomReal (hMeasIoi.mono_measure <| Measure.restrict_mono_set _
          fun _ ht => zero_lt_one.trans_le (hA1.trans ht.le)) hdom
    rw [← Set.Ioc_union_Ioi_eq_Ioi hA1]; exact hmid.union hbig
  rw [← Set.Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one]; exact hsmall.union htail

end LaplaceIntegrand

/-! ## Finite-difference identities (merged from `LaplaceA.FiniteDifference`) -/

/-- Shift `Φ₁'` by `-1` and rewrite it in terms of `Φ₅'` at the point `it`. -/
public lemma Φ₁'_shift_left (u t : ℝ) :
    Φ₁' u ((-1 : ℂ) + (t : ℂ) * Complex.I) =
      Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) * Φ₅' u ((t : ℂ) * Complex.I) := by
  simp [Φ₁', Φ₅', mul_add, div_eq_mul_inv, Complex.exp_add, mul_assoc, mul_left_comm, mul_comm]

/-- Shift `Φ₃'` by `+1` and rewrite it in terms of `Φ₅'` at the point `it`. -/
public lemma Φ₃'_shift_right (u t : ℝ) :
    Φ₃' u ((1 : ℂ) + (t : ℂ) * Complex.I) =
      Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) * Φ₅' u ((t : ℂ) * Complex.I) := by
  simp [Φ₃', Φ₅', mul_add, add_assoc, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg,
    div_eq_mul_inv, Complex.exp_add]

/-- Identify `Φ₅'` on the imaginary axis with `-aLaplaceIntegrand`. -/
public lemma Φ₅'_imag_axis_eq_neg_aLaplaceIntegrand (u t : ℝ) :
    Φ₅' u ((t : ℂ) * Complex.I) = -aLaplaceIntegrand u t := by
  have harg : (-1 : ℂ) / ((t : ℂ) * Complex.I) = (Complex.I : ℂ) / (t : ℂ) := by
    simp [div_eq_mul_inv]
  have hpow : ((t : ℂ) * Complex.I) ^ (2 : ℕ) = -((t ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [mul_pow]; simp [pow_two, Complex.I_mul_I]
  dsimp [MagicFunction.a.ComplexIntegrands.Φ₅', aLaplaceIntegrand]
  rw [harg, hpow, show Complex.exp (Real.pi * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) =
    (Real.exp (-Real.pi * u * t) : ℂ) by
    simp [show (Real.pi : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I) = (-Real.pi * u * t : ℂ)
      from by ring_nf; simp [Complex.I_sq]]]
  ring_nf

/-- Imaginary-axis specialization of the finite-difference identity for `φ₀`. -/
public lemma Φ_finite_difference_imag_axis {u t : ℝ} (ht : 0 < t) :
    Φ₂' u ((t : ℂ) * Complex.I) - 2 * Φ₅' u ((t : ℂ) * Complex.I) + Φ₄' u ((t : ℂ) * Complex.I) =
      2 * Φ₆' u ((t : ℂ) * Complex.I) := by
  let zH : ℍ := UpperHalfPlane.mk (Complex.I * t) (by simp [ht])
  have hfd := MagicFunction.a.SpecialValues.φ₀_finite_difference (z := zH)
  have hcore :
      φ₀'' ((-1 : ℂ) / (((1 : ℝ) +ᵥ zH : ℍ) : ℂ)) * (((1 : ℝ) +ᵥ zH : ℍ) : ℂ) ^ (2 : ℕ)
          - 2 * (φ₀'' ((-1 : ℂ) / (zH : ℂ)) * ((zH : ℂ) ^ (2 : ℕ)))
          + φ₀'' ((-1 : ℂ) / (((-1 : ℝ) +ᵥ zH : ℍ) : ℂ)) * (((-1 : ℝ) +ᵥ zH : ℍ) : ℂ) ^ (2 : ℕ)
        = (2 : ℂ) * φ₀'' (zH : ℂ) := by
    have hS (w : ℍ) : φ₀ (ModularGroup.S • w) = φ₀'' ((-1 : ℂ) / (w : ℂ)) := by
      have hcoe : ((ModularGroup.S • w : ℍ) : ℂ) = (-1 : ℂ) / (w : ℂ) := by
        simpa using ModularGroup.coe_S_smul (z := w)
      calc φ₀ (ModularGroup.S • w) = φ₀'' ((ModularGroup.S • w : ℍ) : ℂ) :=
            (φ₀''_coe_upperHalfPlane (z := ModularGroup.S • w)).symm
        _ = φ₀'' ((-1 : ℂ) / (w : ℂ)) := by rw [hcoe]
    rw [hS ((1 : ℝ) +ᵥ zH), hS zH, hS ((-1 : ℝ) +ᵥ zH),
      show φ₀ zH = φ₀'' (zH : ℂ) from (φ₀''_coe_upperHalfPlane (z := zH)).symm] at hfd
    simpa [mul_assoc] using hfd
  have hzH : (zH : ℂ) = (t : ℂ) * Complex.I := by simp [zH, mul_comm]
  set e : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I * (u : ℂ) * (zH : ℂ))
  set core : ℂ :=
      φ₀'' ((-1 : ℂ) / (((1 : ℝ) +ᵥ zH : ℍ) : ℂ)) * (((1 : ℝ) +ᵥ zH : ℍ) : ℂ) ^ (2 : ℕ)
          - 2 * (φ₀'' ((-1 : ℂ) / (zH : ℂ)) * ((zH : ℂ) ^ (2 : ℕ)))
          + φ₀'' ((-1 : ℂ) / (((-1 : ℝ) +ᵥ zH : ℍ) : ℂ)) * (((-1 : ℝ) +ᵥ zH : ℍ) : ℂ) ^ (2 : ℕ)
    with hcore_def
  have hcore_eq : core = (2 : ℂ) * φ₀'' (zH : ℂ) := by simpa [core, hcore_def] using hcore
  have hL :
      Φ₂' u ((t : ℂ) * Complex.I) - 2 * Φ₅' u ((t : ℂ) * Complex.I) + Φ₄' u ((t : ℂ) * Complex.I) =
        core * e := by
    rw [hcore_def]
    simp [MagicFunction.a.ComplexIntegrands.Φ₂', MagicFunction.a.ComplexIntegrands.Φ₁',
      MagicFunction.a.ComplexIntegrands.Φ₄', MagicFunction.a.ComplexIntegrands.Φ₃',
      MagicFunction.a.ComplexIntegrands.Φ₅', hzH, e, sub_eq_add_neg]
    ring_nf
  have hR : 2 * Φ₆' u ((t : ℂ) * Complex.I) = ((2 : ℂ) * φ₀'' (zH : ℂ)) * e := by
    simp [MagicFunction.a.ComplexIntegrands.Φ₆', hzH, e, mul_assoc, mul_left_comm, mul_comm]
  simpa [hL, hR] using congrArg (fun w : ℂ => w * e) hcore_eq

/-! ## Strip bounds -/

local notation "c12π" => ‖(12 * (I : ℂ)) / (π : ℂ)‖
local notation "c36π2" => ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))‖

/-- `IsBoundedAtImInfty` as an explicit uniform bound with positive constant. -/
lemma exists_bound_of_isBoundedAtImInfty {f : ℍ → ℂ}
    (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) :
    ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im → ‖f z‖ ≤ C :=
  let ⟨C, A, hC⟩ := UpperHalfPlane.isBoundedAtImInfty_iff.mp hbdd
  ⟨max 1 C, A, by positivity, fun z hz ↦ (hC z hz).trans (le_max_right _ _)⟩

/-- Exponential growth bounds for `φ₂'` and `φ₄'` on vertical rays in the upper half-plane. -/
public lemma exists_phi2'_phi4'_bound_exp :
    ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im →
      ‖φ₂' z‖ ≤ C * Real.exp (2 * π * z.im) ∧
        ‖φ₄' z‖ ≤ C * Real.exp (2 * π * z.im) := by
  obtain ⟨CE2, AE2, _, hE2⟩ := exists_bound_of_isBoundedAtImInfty E₂_isBoundedAtImInfty
  obtain ⟨CE4, AE4, _, hE4⟩ := exists_bound_of_isBoundedAtImInfty (f := fun z : ℍ => E₄ z)
    (by simpa using ModularFormClass.bdd_at_infty E₄)
  obtain ⟨CE6, AE6, _, hE6⟩ := exists_bound_of_isBoundedAtImInfty (f := fun z : ℍ => E₆ z)
    (by simpa using ModularFormClass.bdd_at_infty E₆)
  obtain ⟨CΔ, AΔ, _, hΔ⟩ := exists_inv_Delta_bound_exp
  refine ⟨max 1 (max (CE4 ^ 2 * CΔ) (CE4 * (CE2 * CE4 + CE6) * CΔ)),
    max AΔ (max AE2 (max AE4 AE6)), by positivity, fun z hzA => ?_⟩
  have hzE2 : AE2 ≤ z.im := by simp_all
  have hzE4 : AE4 ≤ z.im := by simp_all
  have hzE6 : AE6 ≤ z.im := by simp_all
  have hΔz : ‖(Δ z)⁻¹‖ ≤ CΔ * Real.exp (2 * π * z.im) := hΔ z ((le_max_left _ _).trans hzA)
  have hcore : ‖(E₂ z) * (E₄ z) - (E₆ z)‖ ≤ CE2 * CE4 + CE6 :=
    (by simpa [norm_mul] using norm_sub_le (E₂ z * E₄ z) (E₆ z) :
      ‖E₂ z * E₄ z - E₆ z‖ ≤ ‖E₂ z‖ * ‖E₄ z‖ + ‖E₆ z‖).trans <| by
      gcongr <;> [exact hE2 z hzE2; exact hE4 z hzE4; exact hE6 z hzE6]
  have hφ2 : ‖φ₂' z‖ ≤ (CE4 * (CE2 * CE4 + CE6) * CΔ) * Real.exp (2 * π * z.im) := calc
    ‖φ₂' z‖ = ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) * (Δ z)⁻¹‖ := by
      simp [φ₂', div_eq_mul_inv, mul_assoc]
    _ ≤ ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z))‖ * ‖(Δ z)⁻¹‖ := norm_mul_le _ _
    _ ≤ (CE4 * (CE2 * CE4 + CE6)) * (CΔ * Real.exp (2 * π * z.im)) :=
        mul_le_mul (norm_mul_le_of_le (hE4 z hzE4) hcore) hΔz (norm_nonneg _) (by positivity)
    _ = _ := by ring
  have hφ4 : ‖φ₄' z‖ ≤ (CE4 ^ 2 * CΔ) * Real.exp (2 * π * z.im) := calc
    ‖φ₄' z‖ = ‖E₄ z‖ ^ 2 * ‖(Δ z)⁻¹‖ := by simp [φ₄', div_eq_mul_inv, pow_two]
    _ ≤ CE4 ^ 2 * (CΔ * Real.exp (2 * π * z.im)) := by gcongr; exact hE4 z hzE4
    _ = _ := by ring
  exact ⟨hφ2.trans <| mul_le_mul_of_nonneg_right (by simp_all) (Real.exp_pos _).le,
    hφ4.trans <| mul_le_mul_of_nonneg_right (by simp_all) (Real.exp_pos _).le⟩

/-- Integrability of `Φ₆'` on the imaginary axis tail `t > 1`. -/
lemma integrableOn_Φ₆'_imag_axis {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₆' u ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume := by
  obtain ⟨C₀, _, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  set b : ℝ := π * (u + 2) with hb_def
  refine MeasureTheory.Integrable.mono'
    (by simpa [IntegrableOn, mul_assoc] using
      ((exp_neg_integrableOn_Ioi 1 (hb_def ▸ mul_pos Real.pi_pos (by linarith))).const_mul C₀ :
        IntegrableOn (fun t : ℝ => C₀ * Real.exp (-b * t)) (Set.Ioi (1 : ℝ)) volume))
    (((Φ₆'_contDiffOn_ℂ (r := u)).continuousOn.comp (by fun_prop)
      (fun t ht => by simpa using lt_trans zero_lt_one ht :
        Set.MapsTo (fun t : ℝ => ((t : ℂ) * Complex.I : ℂ)) (Set.Ioi (1 : ℝ))
          {z : ℂ | 0 < z.im})).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 <| .of_forall fun t ht => ?_
  let zH : ℍ := ⟨(t : ℂ) * Complex.I, by simpa using lt_trans zero_lt_one ht⟩
  refine (show ‖Φ₆' u ((t : ℂ) * Complex.I)‖ ≤
      (C₀ * Real.exp (-2 * π * t)) * Real.exp (-π * u * t) by
    rw [show Φ₆' u ((t : ℂ) * Complex.I) = φ₀'' ((t : ℂ) * Complex.I) *
        cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) by simp [Φ₆']]
    have hz_im : zH.im = t := by simp [zH, UpperHalfPlane.im]
    refine norm_mul_le_of_le (show ‖φ₀'' (zH : ℂ)‖ ≤ C₀ * Real.exp (-2 * π * t) by
      simpa [φ₀''_coe_upperHalfPlane, hz_im] using
        hC₀ zH (by simpa [hz_im] using lt_trans (by norm_num : (1/2:ℝ) < 1) ht)) ?_
    rw [show cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) =
        (Real.exp (-π * u * t) : ℂ) by ring_nf; simp [Complex.ofReal_exp],
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]).trans ?_
  rw [mul_assoc, ← Real.exp_add, show -2 * π * t + -π * u * t = -(b * t) by dsimp [b]; ring]

/-- Integrability of `Φ₅'` on the imaginary-axis tail `t > 1`. -/
public lemma integrableOn_Φ₅'_imag_axis {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume :=
  IntegrableOn.congr_fun (((aLaplaceIntegral_convergent (u := u) hu).mono_set
    fun _ ht => lt_trans (by norm_num : (0:ℝ) < 1) ht).neg)
    (fun t _ => by simpa using (Φ₅'_imag_axis_eq_neg_aLaplaceIntegrand (u := u) (t := t)).symm)
    measurableSet_Ioi

/-- Modular-growth bound for `‖φ₀(S•w)‖‖w‖^2` depending only on `t = Im w`. -/
public lemma norm_phi0S_mul_sq_le {t : ℝ} (wH : ℍ) (hw_im : wH.im = t)
    {Cφ Aφ C₀ : ℝ} (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd : ∀ z : ℍ, Aφ ≤ z.im → ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
      ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
  (ht1 : (1 : ℝ) ≤ t) (htAφ : Aφ ≤ t) (hw_norm : ‖(wH : ℂ)‖ ≤ 2 * t) :
    ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
      (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
        (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
  obtain ⟨hφ2, hφ4⟩ : ‖φ₂' wH‖ ≤ Cφ * Real.exp (2 * π * t) ∧
      ‖φ₄' wH‖ ≤ Cφ * Real.exp (2 * π * t) := by
    simpa [hw_im] using hφbd wH (by simpa [hw_im] using htAφ)
  have hCφ_nonneg : 0 ≤ Cφ :=
    le_of_mul_le_mul_right (by simpa using (norm_nonneg _).trans hφ2) (Real.exp_pos _)
  have htri : ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
      ‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ))‖ + ‖(12 * Complex.I) / π * (wH : ℂ) * φ₂' wH‖ +
        ‖(36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH‖ := by
    rw [show φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ)) =
        φ₀ wH * ((wH : ℂ) ^ (2 : ℕ)) - (12 * Complex.I) / π * (wH : ℂ) * φ₂' wH -
          (36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH by simpa using _root_.φ₀_S_transform_mul_sq wH]
    exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
  have hA : ‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
      (4 * C₀) * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
    have h1 : ‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ))‖ ≤ C₀ * (2 * t) ^ 2 := (norm_mul_le _ _).trans
      (mul_le_mul ((hC₀ wH (by rw [hw_im]; linarith)).trans
          (mul_le_of_le_one_right hC₀_pos.le (Real.exp_le_one_iff.2 <| by
            nlinarith [Real.pi_pos, wH.im_pos])))
        (by simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hw_norm 2)
        (norm_nonneg _) hC₀_pos.le)
    nlinarith [h1, sq_nonneg t, Real.one_le_exp_iff.2 (by positivity : (0:ℝ) ≤ 2*π*t),
      mul_nonneg (by positivity : (0:ℝ) ≤ 4 * C₀) (sq_nonneg t)]
  have hB : ‖(12 * Complex.I) / π * (wH : ℂ) * φ₂' wH‖ ≤
      (2 * c12π * Cφ) * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
    refine norm_mul₃_le.trans <| (mul_le_mul (mul_le_mul_of_nonneg_left hw_norm (norm_nonneg _))
      hφ2 (norm_nonneg _) (by positivity)).trans ?_
    rw [show (c12π * (2 * t)) * (Cφ * Real.exp (2 * π * t)) =
      (2 * c12π * Cφ) * (t * Real.exp (2 * π * t)) by ring]
    gcongr; nlinarith
  have hC : ‖(36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH‖ ≤
      c36π2 * Cφ * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
    refine ((norm_mul_le _ _).trans <| mul_le_mul_of_nonneg_left hφ4 (norm_nonneg _)).trans ?_
    rw [show c36π2 * (Cφ * Real.exp (2 * π * t)) = c36π2 * Cφ * (1 * Real.exp (2 * π * t)) by ring]
    gcongr; exact one_le_pow₀ ht1
  linarith [htri, hA, hB, hC]

/-- Pointwise bound for `‖Φ₂' u (tI)‖` on the tail `t ≥ 1`. -/
lemma norm_Φ₂'_imag_axis_le {u t : ℝ} {Cφ Aφ C₀ : ℝ} (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd : ∀ z : ℍ, Aφ ≤ z.im → ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
      ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
    (ht1 : (1 : ℝ) ≤ t) (htAφ : Aφ ≤ t) :
    ‖Φ₂' u ((t : ℂ) * I)‖ ≤
      (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
        (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
  set K : ℝ := 4 * C₀ + (2 * c12π + c36π2) * Cφ
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht1
  let wH : ℍ := ⟨(t : ℂ) * I + 1, by simpa using ht0⟩
  have hw_norm : ‖(wH : ℂ)‖ ≤ 2 * t := (norm_add_le (_ : ℂ) _).trans <| by
    simpa [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le] using by linarith
  calc ‖Φ₂' u ((t : ℂ) * I)‖
      = ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ * Real.exp (-π * u * t) := by
        rw [show Φ₂' u ((t : ℂ) * I) = (φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))) *
            cexp ((π : ℂ) * I * (u : ℂ) * ((t : ℂ) * I)) by
            rw [show Φ₂' u ((t : ℂ) * I) =
                  (φ₀'' ((-1 : ℂ) / (((t : ℂ) * I) + 1)) * (((t : ℂ) * I + 1) ^ (2 : ℕ))) *
                    cexp ((π : ℂ) * I * (u : ℂ) * ((t : ℂ) * I)) by simp [Φ₂', Φ₁', mul_assoc],
              show ((t : ℂ) * I + 1) = (wH : ℂ) from rfl, show φ₀ (ModularGroup.S • wH) =
                φ₀'' ((ModularGroup.S • wH : ℍ) : ℂ) by simp,
              show ((ModularGroup.S • wH : ℍ) : ℂ) = (-1 : ℂ) / (wH : ℂ) by
                simpa using ModularGroup.coe_S_smul (z := wH)],
          norm_mul, show ‖cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I))‖ =
              Real.exp (-π * u * t) by
            rw [show cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) =
              (Real.exp (-π * u * t) : ℂ) by ring_nf; simp [Complex.ofReal_exp],
              Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]]
    _ ≤ (K * (t ^ (2 : ℕ) * Real.exp (2 * π * t))) * Real.exp (-π * u * t) :=
        mul_le_mul_of_nonneg_right (norm_phi0S_mul_sq_le wH (by simp [wH, UpperHalfPlane.im])
          hC₀_pos hC₀ hφbd ht1 htAφ hw_norm) (Real.exp_pos _).le
    _ = K * (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
        rw [mul_assoc, mul_assoc, ← MagicFunction.g.CohnElkies.exp_two_pi_mul_mul_exp_neg_pi_mul]

/-- Integrability of `Φ₂'` on the tail `(A,∞)` via modular bounds. -/
lemma integrableOn_Φ₂'_imag_axis_Ioi {u : ℝ} (hu : 2 < u) {Cφ Aφ C₀ A : ℝ} (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd : ∀ z : ℍ, Aφ ≤ z.im → ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
      ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
    (hA1 : (1 : ℝ) ≤ A) (hAA : Aφ ≤ A) :
    IntegrableOn (fun t : ℝ => Φ₂' u ((t : ℂ) * I)) (Set.Ioi A) volume := by
  refine MeasureTheory.Integrable.mono' (μ := volume.restrict (Set.Ioi A)) (by
      simpa [IntegrableOn, mul_assoc] using ((integrableOn_sq_mul_exp_neg A (π * (u - 2))
        (mul_pos Real.pi_pos (sub_pos.mpr hu))).const_mul
        (4 * C₀ + (2 * c12π + c36π2) * Cφ) :
        IntegrableOn (fun t : ℝ => (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
          (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t))) (Set.Ioi A) volume))
    (((Φ₁'_contDiffOn_ℂ (r := u)).continuousOn.comp (by fun_prop)
      (fun t ht ↦ by simpa using lt_trans (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hA1) ht :
        Set.MapsTo (fun t : ℝ => ((t : ℂ) * Complex.I : ℂ)) (Set.Ioi A)
          {z : ℂ | 0 < z.im})).aestronglyMeasurable measurableSet_Ioi)
    ((ae_restrict_iff' measurableSet_Ioi).2 <| .of_forall fun t ht =>
      norm_Φ₂'_imag_axis_le (u := u) hC₀_pos hC₀ hφbd (le_trans hA1 ht.le) (le_trans hAA ht.le))

/-- Integrability of `Φ₂'` on the imaginary-axis tail `t > 1`. -/
public lemma integrableOn_Φ₂'_imag_axis {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₂' u ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume := by
  obtain ⟨Cφ, Aφ, _, hφbd⟩ := exists_phi2'_phi4'_bound_exp
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  let A : ℝ := max 1 Aφ
  simpa [(Set.Ioc_union_Ioi_eq_Ioi (a := (1 : ℝ)) (b := A) (le_max_left _ _)).symm] using
    ((((Φ₁'_contDiffOn_ℂ (r := u)).continuousOn.comp (by fun_prop)
        (fun t ht => by simpa using lt_of_lt_of_le zero_lt_one ht.1 :
          Set.MapsTo (fun t : ℝ => ((t : ℂ) * Complex.I : ℂ)) (Set.Icc (1 : ℝ) A)
            {z : ℂ | 0 < z.im})).integrableOn_compact isCompact_Icc).mono_set
            Set.Ioc_subset_Icc_self).union
      (integrableOn_Φ₂'_imag_axis_Ioi (u := u) hu (Cφ := Cφ) (Aφ := Aφ) (C₀ := C₀) (A := A)
        hC₀_pos hC₀ hφbd (le_max_left _ _) (le_max_right _ _))

/-- Integrability of `Φ₄'` on the imaginary-axis tail `t > 1` via finite differences. -/
public lemma integrableOn_Φ₄'_imag_axis {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₄' u ((t : ℂ) * I)) (Set.Ioi (1 : ℝ)) volume := by
  have hcomb : IntegrableOn
      (fun t : ℝ => (2 : ℂ) * Φ₆' u ((t : ℂ) * I) - Φ₂' u ((t : ℂ) * I) +
        (2 : ℂ) * Φ₅' u ((t : ℂ) * I)) (Set.Ioi (1 : ℝ)) volume :=
    ((show IntegrableOn (fun t : ℝ => (2 : ℂ) * Φ₆' u ((t : ℂ) * I)) (Set.Ioi (1:ℝ)) volume by
        simpa [mul_assoc] using (integrableOn_Φ₆'_imag_axis (u := u) hu).const_mul (2:ℂ)).sub
      (integrableOn_Φ₂'_imag_axis (u := u) hu)).add <| by
        simpa [mul_assoc] using (integrableOn_Φ₅'_imag_axis (u := u) hu).const_mul (2:ℂ)
  refine hcomb.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have hfd := Φ_finite_difference_imag_axis (u := u) (t := t) (lt_trans zero_lt_one ht)
  grind only

/-- Rewrite `I₁' + I₃' + I₅'` as the imaginary-axis segment integral of `Φ₅'`. -/
public lemma I₁'_add_I₃'_add_I₅'_eq_imag_axis (u : ℝ) :
    I₁' u + I₃' u + I₅' u =
      (I : ℂ) *
        ((Complex.exp (((π * u : ℝ) : ℂ) * I) +
              Complex.exp (-(((π * u : ℝ) : ℂ) * I)) - (2 : ℂ)) *
            (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * I))) := by
  let V0 : ℂ := ∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * I)
  have hmem : ∀ {t : ℝ}, t ∈ Set.uIcc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 := fun ht ↦ by
    simpa [Set.uIcc_of_le zero_le_one] using ht
  have hIshift : ∀ (sign : ℂ) (zp : ℝ → ℂ) (Φⱼ : ℝ → ℂ → ℂ)
      (_ : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → zp t = sign + (t : ℂ) * I)
      (_ : ∀ t : ℝ, Φⱼ u (sign + (t : ℂ) * I) =
        Complex.exp (sign * (((π * u : ℝ) : ℂ) * I)) * Φ₅' u ((t : ℂ) * I)),
      (∫ t in (0 : ℝ)..1, (I : ℂ) * Φⱼ u (zp t)) =
        (I : ℂ) * Complex.exp (sign * (((π * u : ℝ) : ℂ) * I)) * V0 := fun sign zp Φⱼ hzp hΦ ↦ by
    rw [intervalIntegral.integral_congr (g := fun t ↦ (I : ℂ) *
      (Complex.exp (sign * (((π * u : ℝ) : ℂ) * I)) * Φ₅' u ((t : ℂ) * I)))
      fun t ht ↦ by simp [hzp (hmem ht), hΦ, mul_assoc]]
    simp [V0, mul_assoc]
  rw [show I₁' u = (I : ℂ) * Complex.exp (-(((π * u : ℝ) : ℂ) * I)) * V0 from by
        simpa [I₁', Φ₁, mul_assoc, neg_mul, one_mul] using hIshift (-1 : ℂ) z₁' Φ₁'
          (fun ht ↦ by simpa [mul_comm] using z₁'_eq_of_mem ht)
          (fun t ↦ by simpa [neg_mul, one_mul, mul_comm] using Φ₁'_shift_left (u := u) (t := t)),
      show I₃' u = (I : ℂ) * Complex.exp (((π * u : ℝ) : ℂ) * I) * V0 from by
        simpa [I₃', Φ₃, mul_assoc, one_mul] using hIshift (1 : ℂ) z₃' Φ₃'
          (fun ht ↦ by simpa [mul_comm] using z₃'_eq_of_mem ht)
          (fun t ↦ by simpa [one_mul, mul_comm] using Φ₃'_shift_right (u := u) (t := t)),
      show I₅' u = (-2 : ℂ) * (I : ℂ) * V0 from by
        simpa [I₅', Φ₅, mul_assoc] using congrArg (fun z : ℂ ↦ (-2 : ℂ) * z) (by
          rw [intervalIntegral.integral_congr (g := fun t ↦ (I : ℂ) * Φ₅' u ((t : ℂ) * I))
            fun t ht ↦ by simp [z₅'_eq_of_mem (hmem ht), mul_comm]]; simp [V0] :
          (∫ t in (0 : ℝ)..1, (I : ℂ) * Φ₅' u (z₅' t)) = (I : ℂ) * V0)]
  ring

end MagicFunction.g.CohnElkies.IntegralReps
namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators Topology Interval UpperHalfPlane

open MeasureTheory Real Complex Filter
open SpherePacking intervalIntegral
open MagicFunction.a.RealIntegrals

/-- Differentiability of a parameter-dependent interval integral with an exponential factor. -/
public lemma differentiableAt_intervalIntegral_mul_exp
    {base k : ℝ → ℂ} (u0 : ℂ) (Cbase K : ℝ)
    (hbase : ContinuousOn base (Ι (0 : ℝ) 1))
    (hk : ContinuousOn k (Ι (0 : ℝ) 1))
    (hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Cbase)
    (hk_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k t‖ ≤ K) :
    DifferentiableAt ℂ
      (fun u : ℂ => ∫ t in (0 : ℝ)..1, base t * Complex.exp (u * k t)) u0 := by
  have hCbase : 0 ≤ Cbase := (norm_nonneg (base 1)).trans (hbase_bound 1 (by simp))
  have hK : 0 ≤ K := (norm_nonneg (k 1)).trans (hk_bound 1 (by simp))
  let F : ℂ → ℝ → ℂ := fun u t => base t * Complex.exp (u * k t)
  let F' : ℂ → ℝ → ℂ := fun u t => base t * (k t) * Complex.exp (u * k t)
  have hexp (u : ℂ) : ContinuousOn (fun t : ℝ => Complex.exp (u * k t)) (Ι (0 : ℝ) 1) := by
    fun_prop
  have hF_meas : ∀ᶠ u in 𝓝 u0, AEStronglyMeasurable (F u) (volume.restrict (Ι (0 : ℝ) 1)) :=
    Filter.Eventually.of_forall fun u => (hbase.mul (hexp u)).aestronglyMeasurable
      (μ := (volume : Measure ℝ)) measurableSet_uIoc
  have hF'_meas : AEStronglyMeasurable (F' u0) (volume.restrict (Ι (0 : ℝ) 1)) := by
    simpa [F', mul_assoc] using (hbase.mul (hk.mul (hexp u0))).aestronglyMeasurable
      (μ := (volume : Measure ℝ)) measurableSet_uIoc
  have hF_int : IntervalIntegrable (F u0) volume (0 : ℝ) 1 := by
    refine intervalIntegrable_iff.2 ?_
    refine MeasureTheory.IntegrableOn.of_bound (by simp : (volume : Measure ℝ) (Ι (0 : ℝ) 1) < ⊤)
      hF_meas.self_of_nhds (Cbase * Real.exp (‖u0‖ * K)) <|
      (ae_restrict_iff' measurableSet_uIoc).2 <| .of_forall fun t ht => ?_
    refine norm_mul_le_of_le (hbase_bound t ht) ?_
    exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2
      ((norm_mul_le u0 (k t)).trans (by gcongr; exact hk_bound t ht)))
  let E : ℝ := Real.exp ((‖u0‖ + 1) * K)
  let bound : ℝ → ℝ := fun _ => Cbase * (K * E)
  have h_bound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι (0 : ℝ) 1 →
      ∀ u ∈ Metric.ball u0 (1 : ℝ), ‖F' u t‖ ≤ bound t := by
    refine Filter.Eventually.of_forall (fun t ht u hu => ?_)
    have hk' : ‖k t‖ ≤ K := hk_bound t ht
    have hu' : ‖u‖ ≤ ‖u0‖ + 1 := by
      have hle : ‖u - u0‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hu
      have h2 : ‖u‖ ≤ ‖u0‖ + ‖u - u0‖ := by
        simpa [sub_eq_add_neg, add_assoc] using norm_add_le u0 (u - u0)
      linarith
    have hstep1 : ‖F' u t‖ ≤ ‖base t‖ * (‖k t‖ * E) := by
      calc
        ‖F' u t‖ = ‖base t‖ * (‖k t‖ * ‖Complex.exp (u * k t)‖) := by
          simp [F', mul_left_comm, mul_comm]
        _ ≤ ‖base t‖ * (‖k t‖ * E) := by
          gcongr
          exact (Complex.norm_exp_le_exp_norm _).trans
            (Real.exp_le_exp.2 (norm_mul_le_of_le hu' hk'))
    simpa [bound, E, mul_assoc] using hstep1.trans (by gcongr; exact hbase_bound t ht)
  have h_diff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι (0 : ℝ) 1 →
      ∀ u ∈ Metric.ball u0 (1 : ℝ), HasDerivAt (fun u : ℂ => F u t) (F' u t) u :=
    Filter.Eventually.of_forall fun t _ u _ => by
      simpa [F, F', mul_assoc, mul_left_comm, mul_comm] using
        ((Complex.hasDerivAt_exp (u * k t)).comp u
          (hasDerivAt_mul_const (k t) (x := u))).const_mul (base t)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ))
    (F := F) (F' := F') (x₀ := u0) (s := Metric.ball u0 (1 : ℝ)) (bound := bound)
    (Metric.ball_mem_nhds u0 (by norm_num)) (hF_meas := hF_meas) (hF_int := hF_int)
    (hF'_meas := hF'_meas) (h_bound := h_bound)
    (bound_integrable := by simp [bound]) (h_diff := h_diff)).2.differentiableAt

noncomputable section

def I₁'C (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (-Complex.I) * φ₀'' (-1 / ((Complex.I : ℂ) * (t : ℂ))) * (t ^ (2 : ℕ) : ℝ) *
      Complex.exp (-π * (Complex.I : ℂ) * u) * Complex.exp (-π * u * (t : ℂ))

def I₂'C (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / ((t : ℂ) + (Complex.I : ℂ))) * (((t : ℂ) + (Complex.I : ℂ)) ^ (2 : ℕ)) *
      Complex.exp (-π * (Complex.I : ℂ) * u) *
      Complex.exp (π * (Complex.I : ℂ) * u * (t : ℂ)) *
      Complex.exp (-π * u)

def I₃'C (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (-Complex.I) * φ₀'' (-1 / ((Complex.I : ℂ) * (t : ℂ))) * (t ^ (2 : ℕ) : ℝ) *
      Complex.exp (π * (Complex.I : ℂ) * u) * Complex.exp (-π * u * (t : ℂ))

def I₄'C (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (-1 : ℂ) * φ₀'' (-1 / (-(t : ℂ) + (Complex.I : ℂ))) *
      ((-(t : ℂ) + (Complex.I : ℂ)) ^ (2 : ℕ)) *
      Complex.exp (π * (Complex.I : ℂ) * u) *
      Complex.exp (-π * (Complex.I : ℂ) * u * (t : ℂ)) *
      Complex.exp (-π * u)

def I₅'C (u : ℂ) : ℂ :=
  -2 * ∫ t in (0 : ℝ)..1,
    (-Complex.I) * φ₀'' (-1 / ((Complex.I : ℂ) * (t : ℂ))) * (t ^ (2 : ℕ) : ℝ) *
      Complex.exp (-π * u * (t : ℂ))

def I₆'C (u : ℂ) : ℂ :=
  2 * ∫ t in Set.Ici (1 : ℝ),
    (Complex.I : ℂ) * φ₀'' ((Complex.I : ℂ) * (t : ℂ)) * Complex.exp (-π * u * (t : ℂ))

/-- Complex-parameter extension of `a'`, defined as the sum of the complexified integral pieces.

This is analytic on the right half-plane and restricts to `a'` on `ℝ`. -/
public def aPrimeC (u : ℂ) : ℂ :=
  I₁'C u + I₂'C u + I₃'C u + I₄'C u + I₅'C u + I₆'C u

@[simp] lemma I₁'C_ofReal (u : ℝ) : I₁'C (u : ℂ) = I₁' u := by
  simp [I₁'C, MagicFunction.a.RadialFunctions.I₁'_eq]
@[simp] lemma I₂'C_ofReal (u : ℝ) : I₂'C (u : ℂ) = I₂' u := by
  simp [I₂'C, MagicFunction.a.RadialFunctions.I₂'_eq]
@[simp] lemma I₃'C_ofReal (u : ℝ) : I₃'C (u : ℂ) = I₃' u := by
  simp [I₃'C, MagicFunction.a.RadialFunctions.I₃'_eq]
@[simp] lemma I₄'C_ofReal (u : ℝ) : I₄'C (u : ℂ) = I₄' u := by
  simp [I₄'C, MagicFunction.a.RadialFunctions.I₄'_eq]
@[simp] lemma I₅'C_ofReal (u : ℝ) : I₅'C (u : ℂ) = I₅' u := by
  simp [I₅'C, MagicFunction.a.RadialFunctions.I₅'_eq]
@[simp] lemma I₆'C_ofReal (u : ℝ) : I₆'C (u : ℂ) = I₆' u := by
  simp [I₆'C, MagicFunction.a.RadialFunctions.I₆'_eq]

/-- Restriction of `aPrimeC` to real parameters recovers `a'`. -/
public lemma aPrimeC_ofReal (u : ℝ) : aPrimeC (u : ℂ) = a' u := by
  simp [aPrimeC, MagicFunction.a.RealIntegrals.a']

lemma norm_φ₀''_le_of_half_lt {C₀ : ℝ}
    (hC₀_nonneg : 0 ≤ C₀)
    (hC₀ : ∀ z : ℍ, 1 / 2 < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    {z : ℂ} (hzpos : 0 < z.im) (hzhalf : 1 / 2 < z.im) :
    ‖φ₀'' z‖ ≤ C₀ := by
  refine (show ‖φ₀'' z‖ ≤ C₀ * Real.exp (-2 * π * z.im) from ?_).trans
    (mul_le_of_le_one_right hC₀_nonneg <| Real.exp_le_one_iff.2
      (by nlinarith [Real.pi_pos, hzpos.le]))
  simpa [φ₀''_def hzpos] using hC₀ ⟨z, hzpos⟩ (by simpa [UpperHalfPlane.im] using hzhalf)

def arg₁ (t : ℝ) : ℂ := (Complex.I : ℂ) / (t : ℂ)

lemma neg_one_div_I_mul_eq_arg₁ (t : ℝ) :
    (-1 : ℂ) / ((Complex.I : ℂ) * (t : ℂ)) = arg₁ t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [arg₁]
  · simp only [arg₁]
    field_simp [show (t : ℂ) ≠ 0 by exact_mod_cast ht, Complex.I_ne_zero]
    simp [Complex.I_sq]

def base₁ (t : ℝ) : ℂ := (-Complex.I) * φ₀'' (arg₁ t) * (t ^ (2 : ℕ) : ℝ)
def k₁ (t : ℝ) : ℂ := (-π * (Complex.I : ℂ)) + (-π * (t : ℂ))
def k₃ (t : ℝ) : ℂ := (π * (Complex.I : ℂ)) + (-π * (t : ℂ))
def k₅ (t : ℝ) : ℂ := (-π * (t : ℂ))

lemma I₁'C_eq (u : ℂ) :
    I₁'C u = ∫ t in (0 : ℝ)..1, base₁ t * Complex.exp (u * k₁ t) :=
  intervalIntegral.integral_congr fun t _ => by
    simp [base₁, k₁, neg_one_div_I_mul_eq_arg₁, mul_add, Complex.exp_add,
      mul_assoc, mul_left_comm, mul_comm]

lemma I₃'C_eq (u : ℂ) :
    I₃'C u = ∫ t in (0 : ℝ)..1, base₁ t * Complex.exp (u * k₃ t) :=
  intervalIntegral.integral_congr fun t _ => by
    simp [base₁, k₃, neg_one_div_I_mul_eq_arg₁, mul_add, Complex.exp_add,
      mul_assoc, mul_left_comm, mul_comm]

lemma I₅'C_eq (u : ℂ) :
    I₅'C u = -2 * ∫ t in (0 : ℝ)..1, base₁ t * Complex.exp (u * k₅ t) :=
  congrArg (fun x : ℂ => -2 * x) <| intervalIntegral.integral_congr fun t _ => by
    simp [base₁, k₅, neg_one_div_I_mul_eq_arg₁, mul_left_comm, mul_comm]

lemma base₁_continuousOn : ContinuousOn base₁ (Ι (0 : ℝ) 1) :=
  (continuousOn_const.mul
    ((MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn).comp
      (continuousOn_const.div (by fun_prop) fun t ht => by
        exact_mod_cast (by simpa using ht.1 : (0 : ℝ) < t).ne')
      fun t ht => by
        simpa [UpperHalfPlane.upperHalfPlaneSet, arg₁] using
          inv_pos.2 (by simpa using ht.1 : (0:ℝ) < t))).mul (by fun_prop)

lemma base₁_bound :
    ∃ C₀ > 0, ∀ t ∈ Ι (0 : ℝ) 1, ‖base₁ t‖ ≤ C₀ := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  refine ⟨C₀, hC₀_pos, fun t ht => ?_⟩
  have ht0 : 0 < t := by simpa using ht.1
  have ht1 : t ≤ 1 := by simpa using ht.2
  have hzhalf : (1 / 2 : ℝ) < (arg₁ t).im := by
    simpa [arg₁] using lt_of_lt_of_le (by norm_num : (1/2:ℝ) < 1) (one_le_inv_iff₀.2 ⟨ht0, ht1⟩)
  have ht2 : ‖(t ^ (2 : ℕ) : ℝ)‖ ≤ 1 := by
    have : |t| ^ (2 : ℕ) ≤ (1 : ℝ) :=
      pow_le_one₀ (abs_nonneg t) (by simpa [abs_of_nonneg ht0.le] using ht1)
    simpa [Real.norm_eq_abs, abs_pow] using this
  calc ‖base₁ t‖
      = ‖φ₀'' (arg₁ t)‖ * ‖(t ^ (2 : ℕ) : ℝ)‖ := by simp [base₁]
    _ ≤ C₀ * 1 := mul_le_mul (norm_φ₀''_le_of_half_lt hC₀_pos.le hC₀
          (by simpa [arg₁] using inv_pos.2 ht0) hzhalf) ht2 (norm_nonneg _) hC₀_pos.le
    _ = C₀ := mul_one _

private lemma norm_of_mem_uIoc_le_one {t : ℝ} (ht : t ∈ Ι (0 : ℝ) 1) : ‖(t : ℂ)‖ ≤ 1 := by
  simpa [Complex.norm_real, abs_of_nonneg (by simpa using ht.1 : (0:ℝ) < t).le] using ht.2

private lemma norm_neg_pi_mul_t_le {t : ℝ} (ht : t ∈ Ι (0 : ℝ) 1) :
    ‖(-π : ℂ) * (t : ℂ)‖ ≤ Real.pi := by
  have : ‖(-π : ℂ) * (t : ℂ)‖ = Real.pi * ‖(t : ℂ)‖ := by
    simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le]
  nlinarith [Real.pi_pos, norm_of_mem_uIoc_le_one ht]

private lemma norm_sign_pi_I_eq_pi {s : ℝ} (hs : |s| = 1) :
    ‖(s * π : ℂ) * (Complex.I : ℂ)‖ = Real.pi := by
  simp [Complex.norm_real, hs, abs_of_nonneg Real.pi_pos.le]

/-- Shared bound for `k₁` and `k₃`: `‖±π * I + (-π * t)‖ ≤ 2π`. -/
private lemma k_bound_two_pi {s : ℝ} (hs : |s| = 1) (t : ℝ) (ht : t ∈ Ι (0 : ℝ) 1) :
    ‖(s * π : ℂ) * (Complex.I : ℂ) + (-π * (t : ℂ))‖ ≤ (2 * Real.pi) := by
  linarith [(norm_add_le ((s * π : ℂ) * (Complex.I : ℂ)) (-π * (t : ℂ))).trans
    (add_le_add (norm_sign_pi_I_eq_pi hs).le (norm_neg_pi_mul_t_le ht))]

/-- Shared wrapper: `u ↦ ∫ t in 0..1, base₁ t * exp (u * k t)` is differentiable at `u0`. -/
private lemma base₁_integral_differentiableAt {k : ℝ → ℂ} (u0 : ℂ) (K : ℝ)
    (hk : ContinuousOn k (Ι (0 : ℝ) 1)) (hk_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k t‖ ≤ K) :
    DifferentiableAt ℂ
      (fun u : ℂ => ∫ t in (0 : ℝ)..1, base₁ t * Complex.exp (u * k t)) u0 :=
  let ⟨Cbase, _, hbase_bound⟩ := base₁_bound
  differentiableAt_intervalIntegral_mul_exp u0 Cbase K
    base₁_continuousOn hk hbase_bound hk_bound

lemma I₁'C_differentiableOn : DifferentiableOn ℂ I₁'C rightHalfPlane := fun u _ => by
  refine DifferentiableAt.differentiableWithinAt ?_
  simpa [funext I₁'C_eq] using
    base₁_integral_differentiableAt u (2 * Real.pi) (by unfold k₁; fun_prop)
      (fun t ht => by
        simpa [k₁, show ((-1 : ℝ) * Real.pi : ℂ) = (-π : ℂ) by push_cast; ring] using
          k_bound_two_pi (s := -1) (by norm_num) t ht)

lemma I₃'C_differentiableOn : DifferentiableOn ℂ I₃'C rightHalfPlane := fun u _ => by
  refine DifferentiableAt.differentiableWithinAt ?_
  simpa [funext I₃'C_eq] using
    base₁_integral_differentiableAt u (2 * Real.pi) (by unfold k₃; fun_prop)
      (fun t ht => by
        simpa [k₃, show ((1 : ℝ) * Real.pi : ℂ) = (π : ℂ) by push_cast; ring] using
          k_bound_two_pi (s := 1) (by norm_num) t ht)

lemma I₅'C_differentiableOn : DifferentiableOn ℂ I₅'C rightHalfPlane := fun u _ => by
  refine DifferentiableAt.differentiableWithinAt ?_
  simpa [funext fun u => by simpa [mul_assoc] using I₅'C_eq u, mul_assoc] using
    (base₁_integral_differentiableAt u Real.pi (by unfold k₅; fun_prop)
      (fun t ht => by simpa [k₅] using norm_neg_pi_mul_t_le ht)).const_mul (-2 : ℂ)

def arg₂ (t : ℝ) : ℂ := (-1 : ℂ) / ((t : ℂ) + (Complex.I : ℂ))
def base₂ (t : ℝ) : ℂ := φ₀'' (arg₂ t) * (((t : ℂ) + (Complex.I : ℂ)) ^ (2 : ℕ))
def k₂ (t : ℝ) : ℂ := (-π * (Complex.I : ℂ)) + (π * (Complex.I : ℂ) * (t : ℂ)) + (-π)
def arg₄ (t : ℝ) : ℂ := (-1 : ℂ) / (-(t : ℂ) + (Complex.I : ℂ))
def base₄ (t : ℝ) : ℂ := (-1 : ℂ) * φ₀'' (arg₄ t) * ((-(t : ℂ) + (Complex.I : ℂ)) ^ (2 : ℕ))
def k₄ (t : ℝ) : ℂ := (π * (Complex.I : ℂ)) + (-π * (Complex.I : ℂ) * (t : ℂ)) + (-π)

lemma I₂'C_eq (u : ℂ) :
    I₂'C u = ∫ t in (0 : ℝ)..1, base₂ t * Complex.exp (u * k₂ t) :=
  intervalIntegral.integral_congr fun t _ => by
    simp [base₂, arg₂, k₂, mul_add, Complex.exp_add, add_assoc,
      mul_assoc, mul_left_comm, mul_comm]

lemma I₄'C_eq (u : ℂ) :
    I₄'C u = ∫ t in (0 : ℝ)..1, base₄ t * Complex.exp (u * k₄ t) :=
  intervalIntegral.integral_congr fun t _ => by
    simp [base₄, arg₄, k₄, mul_add, Complex.exp_add, add_assoc,
      mul_assoc, mul_left_comm, mul_comm]

/-- Shared continuity argument for `base₂` and `base₄`: if `d : ℝ → ℂ` is continuous with
imaginary part `1` (so nonzero), then `t ↦ φ₀'' (-1 / d t) * d t ^ 2` is continuous. -/
private lemma phi_div_pow_continuousOn {d : ℝ → ℂ} (hd : Continuous d)
    (hd_im : ∀ t, (d t).im = 1) :
    ContinuousOn (fun t : ℝ => φ₀'' (-1 / d t) * (d t) ^ (2 : ℕ)) (Ι (0 : ℝ) 1) := by
  have hden0 : ∀ t : ℝ, d t ≠ 0 := fun t ht0 =>
    (one_ne_zero : (1 : ℝ) ≠ 0) (by simpa [hd_im] using congrArg Complex.im ht0)
  exact ((MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn).comp
    (continuousOn_const.div hd.continuousOn fun t _ => hden0 t) (fun t _ => by
      have him : ((-1 : ℂ) / d t).im = 1 / Complex.normSq (d t) := by
        rw [show ((-1 : ℂ) / d t).im = -(d t)⁻¹.im from by simp [div_eq_mul_inv],
          Complex.inv_im, hd_im]; field_simp
      simpa [UpperHalfPlane.upperHalfPlaneSet, him] using
        one_div_pos.2 (Complex.normSq_pos.2 (hden0 t)))).mul (by fun_prop)

/-- Shared bound for `k₂` and `k₄`: `‖±π * I + ∓π * I * t + (-π)‖ ≤ 3π`. -/
private lemma k_bound_three_pi {s₁ s₂ : ℝ} (hs₁ : |s₁| = 1) (hs₂ : |s₂| = 1)
    (t : ℝ) (ht : t ∈ Ι (0 : ℝ) 1) :
    ‖(s₁ * π : ℂ) * (Complex.I : ℂ) + (s₂ * π : ℂ) * (Complex.I : ℂ) * (t : ℂ) + (-π)‖ ≤
      (3 * Real.pi) := by
  have hpi : ‖(-π : ℂ)‖ = Real.pi := by simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le]
  have h_t_le : ‖(s₂ * π : ℂ) * (Complex.I : ℂ) * (t : ℂ)‖ ≤ Real.pi := by
    have h : ‖(s₂ * π : ℂ) * (Complex.I : ℂ) * (t : ℂ)‖ = Real.pi * ‖(t : ℂ)‖ := by
      simpa [mul_assoc] using congrArg (· * ‖(t : ℂ)‖) (norm_sign_pi_I_eq_pi hs₂)
    nlinarith [Real.pi_pos, norm_of_mem_uIoc_le_one ht]
  linarith [(norm_add_le _ (-π : ℂ)).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (norm_sign_pi_I_eq_pi hs₁).le h_t_le)) hpi.le)]

/-- Shared differentiability wrapper for I₂/I₄. -/
private lemma base_pow_diffAt_of
    {base k : ℝ → ℂ} (arg d : ℝ → ℂ) (u0 : ℂ)
    (hbase_eq : ∀ t : ℝ, ‖base t‖ = ‖φ₀'' (arg t)‖ * ‖(d t) ^ (2 : ℕ)‖)
    (hbase_cont : ContinuousOn base (Ι (0 : ℝ) 1))
    (hd_norm : ∀ t : ℝ, ‖d t‖ ≤ ‖(t : ℂ)‖ + 1)
    (him : ∀ t ∈ Set.Ioo (0 : ℝ) 1, (1 / 2 : ℝ) < (arg t).im)
    (hk_cont : ContinuousOn k (Ι (0 : ℝ) 1))
    (hk_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k t‖ ≤ (3 * Real.pi)) :
    DifferentiableAt ℂ (fun u : ℂ =>
      ∫ t in (0 : ℝ)..1, base t * Complex.exp (u * k t)) u0 := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  set Cφ : ℝ := max C₀ ‖φ₀'' (arg 1)‖
  refine differentiableAt_intervalIntegral_mul_exp u0 (4 * Cφ) (3 * Real.pi)
    hbase_cont hk_cont (fun t ht => (hbase_eq t).le.trans ?_) hk_bound
  have hphi : ‖φ₀'' (arg t)‖ ≤ Cφ := by
    by_cases ht1 : t = 1
    · exact ht1 ▸ le_max_right _ _
    · have hh := him t ⟨by simpa using ht.1, lt_of_le_of_ne (by simpa using ht.2) ht1⟩
      exact (norm_φ₀''_le_of_half_lt hC₀_pos.le hC₀ (one_half_pos.trans hh) hh).trans
        (le_max_left _ _)
  have hpow : ‖(d t) ^ (2 : ℕ)‖ ≤ 4 := by
    have hnorm : ‖d t‖ ≤ 2 := (hd_norm t).trans (by linarith [norm_of_mem_uIoc_le_one ht])
    calc ‖(d t) ^ (2 : ℕ)‖ = ‖d t‖ ^ (2 : ℕ) := by simp
      _ ≤ (2 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = 4 := by norm_num
  calc ‖φ₀'' (arg t)‖ * ‖(d t) ^ (2 : ℕ)‖
      ≤ Cφ * 4 := mul_le_mul hphi hpow (norm_nonneg _) (by positivity)
    _ = 4 * Cφ := by ring

lemma I₂'C_differentiableOn : DifferentiableOn ℂ I₂'C rightHalfPlane := fun u _ => by
  refine DifferentiableAt.differentiableWithinAt ?_
  simpa [funext I₂'C_eq] using
    base_pow_diffAt_of arg₂ (fun t => (t : ℂ) + (Complex.I : ℂ)) u
      (fun t => by simp [base₂])
      (by unfold base₂ arg₂; exact phi_div_pow_continuousOn (by fun_prop) (fun _ => by simp))
      (fun t => by simpa using (norm_add_le (t : ℂ) (Complex.I : ℂ)))
      (fun t htIoo => by
        simpa [arg₂] using MagicFunction.a.IntegralEstimates.I₂.im_parametrisation_lower t htIoo)
      (by unfold k₂; fun_prop) fun t ht => by
        simpa [k₂, show ((-1 : ℝ) * Real.pi : ℂ) = (-π : ℂ) by push_cast; ring,
          show ((1 : ℝ) * Real.pi : ℂ) = (π : ℂ) by push_cast; ring] using
          k_bound_three_pi (s₁ := -1) (s₂ := 1) (by norm_num) (by norm_num) t ht

lemma I₄'C_differentiableOn : DifferentiableOn ℂ I₄'C rightHalfPlane := fun u _ => by
  refine DifferentiableAt.differentiableWithinAt ?_
  simpa [funext I₄'C_eq] using
    base_pow_diffAt_of arg₄ (fun t => -(t : ℂ) + (Complex.I : ℂ)) u
      (fun t => by simp [base₄])
      ((show (fun t : ℝ => (-1 : ℂ) * (φ₀'' (arg₄ t) * (-(t:ℂ) + (Complex.I:ℂ)) ^ (2:ℕ))) = base₄
        from funext fun _ => by simp [base₄, arg₄]) ▸
        continuousOn_const.mul (phi_div_pow_continuousOn
          (d := fun t : ℝ => -(t : ℂ) + (Complex.I : ℂ)) (by fun_prop) (fun _ => by simp)))
      (fun t => (norm_add_le _ _).trans (by simp))
      (fun t htIoo => by
        simpa [arg₄] using MagicFunction.a.IntegralEstimates.I₄.im_parametrisation_lower t htIoo)
      (by unfold k₄; fun_prop) fun t ht => by
        simpa [k₄, show ((-1 : ℝ) * Real.pi : ℂ) = (-π : ℂ) by push_cast; ring,
          show ((1 : ℝ) * Real.pi : ℂ) = (π : ℂ) by push_cast; ring] using
          k_bound_three_pi (s₁ := 1) (s₂ := -1) (by norm_num) (by norm_num) t ht

def base₆ (t : ℝ) : ℂ := (Complex.I : ℂ) * φ₀'' ((t : ℂ) * (Complex.I : ℂ))

def I₆IntegrandC (u : ℂ) (t : ℝ) : ℂ := base₆ t * Complex.exp (-(π : ℂ) * u * (t : ℂ))
def I₆IntegrandC_deriv (u : ℂ) (t : ℝ) : ℂ := (-(π : ℂ) * (t : ℂ)) * I₆IntegrandC u t

lemma base₆_continuousOn : ContinuousOn base₆ (Set.Ici (1 : ℝ)) := by
  simpa [base₆, mul_assoc] using continuousOn_const.mul
    (MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn.comp
      (by fun_prop : Continuous fun t : ℝ => (t : ℂ) * (Complex.I : ℂ)).continuousOn
      fun t ht => by
        simpa [UpperHalfPlane.upperHalfPlaneSet, mul_assoc] using lt_of_lt_of_le (by norm_num) ht)

lemma I₆'C_differentiableAt (u0 : ℂ) (hu0 : u0 ∈ rightHalfPlane) :
    DifferentiableAt ℂ I₆'C u0 := by
  have hu0re : 0 < u0.re := by simpa [rightHalfPlane] using hu0
  set ε : ℝ := u0.re / 2 with hε_def
  have hε : 0 < ε := by positivity
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ici (1 : ℝ))
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  have hbase_bound : ∀ t ∈ Set.Ici (1 : ℝ), ‖base₆ t‖ ≤ C₀ := fun t ht => by
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    simpa [base₆, norm_mul] using norm_φ₀''_le_of_half_lt hC₀_pos.le hC₀
      (z := (t : ℂ) * (Complex.I : ℂ)) (by simpa [mul_assoc] using ht0)
      (by simpa [mul_assoc] using lt_of_lt_of_le (by norm_num : (1/2:ℝ) < 1) ht)
  have hIntegrand_le : ∀ z : ℂ, ∀ t ∈ Set.Ici (1 : ℝ),
      ‖I₆IntegrandC z t‖ ≤ C₀ * Real.exp (-Real.pi * z.re * t) := fun z t ht => by
    have hExp : ‖Complex.exp (-(π : ℂ) * z * (t : ℂ))‖ ≤ Real.exp (-Real.pi * z.re * t) := by
      simp [Complex.norm_exp, mul_assoc, Complex.mul_re, sub_eq_add_neg, add_comm]
    calc ‖I₆IntegrandC z t‖
        = ‖base₆ t‖ * ‖Complex.exp (-(π : ℂ) * z * (t : ℂ))‖ := by simp [I₆IntegrandC]
      _ ≤ C₀ * Real.exp (-Real.pi * z.re * t) :=
        mul_le_mul (hbase_bound t ht) hExp (norm_nonneg _) (by positivity)
  have hIntegrandC_continuousOn : ∀ z : ℂ,
      ContinuousOn (fun t : ℝ => I₆IntegrandC z t) (Set.Ici (1 : ℝ)) := fun z => by
    simpa [I₆IntegrandC] using base₆_continuousOn.mul
      (by fun_prop : Continuous fun t : ℝ => Complex.exp (-(π : ℂ) * z * (t : ℂ))).continuousOn
  have hF_meas : ∀ z : ℂ, MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => I₆IntegrandC z t) μ := fun z =>
    (hIntegrandC_continuousOn z).aestronglyMeasurable measurableSet_Ici
  have hF_int : MeasureTheory.Integrable (fun t : ℝ => I₆IntegrandC u0 t) μ := by
    have hExp : MeasureTheory.Integrable (fun t : ℝ => Real.exp (-((Real.pi * u0.re) * t)))
        (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
      simpa [mul_assoc] using
        exp_neg_integrableOn_Ioi (a := (1 : ℝ)) (b := (Real.pi * u0.re)) (by positivity)
    refine MeasureTheory.Integrable.mono' (μ := μ) (by
      simpa [MeasureTheory.IntegrableOn, μ] using
        (integrableOn_Ici_iff_integrableOn_Ioi (μ := (MeasureTheory.volume : Measure ℝ))
          (f := fun t : ℝ => C₀ * Real.exp (-(Real.pi * u0.re) * t)) (b := (1 : ℝ))
          (by finiteness)).2
            (by simpa [MeasureTheory.IntegrableOn, mul_assoc] using hExp.const_mul C₀))
      (hF_meas u0) (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun t ht => ?_)
    simpa [← mul_assoc] using hIntegrand_le u0 t ht
  have hF'_meas : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => I₆IntegrandC_deriv u0 t) μ :=
    (((by fun_prop : Continuous fun t : ℝ => (-(π : ℂ) * (t : ℂ))).continuousOn.mul
      (hIntegrandC_continuousOn u0)).congr fun t _ => by
      simp [I₆IntegrandC_deriv, mul_assoc]).aestronglyMeasurable measurableSet_Ici
  let bound : ℝ → ℝ := fun t => (C₀ * Real.pi) * t * Real.exp (-(Real.pi * ε) * t)
  have hbound :
      ∀ᵐ (t : ℝ) ∂μ, ∀ z ∈ Metric.ball u0 ε, ‖I₆IntegrandC_deriv z t‖ ≤ bound t := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun t ht z hz => ?_
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht
    have hzRe : ε ≤ z.re := by
      have habs := (abs_lt.mp (lt_of_le_of_lt
        (by simpa using abs_re_le_norm (z - u0) : |z.re - u0.re| ≤ ‖z - u0‖)
        (by simpa [Metric.mem_ball, dist_eq_norm] using hz : ‖z - u0‖ < ε))).1
      simp only [hε_def]; linarith
    have hnorm_int : ‖I₆IntegrandC z t‖ ≤ C₀ * Real.exp (-π * ε * t) :=
      (hIntegrand_le z t ht).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg Real.pi_pos.le ht0, hzRe])) hC₀_pos.le)
    calc ‖I₆IntegrandC_deriv z t‖
        = ‖(-(π : ℂ) * (t : ℂ))‖ * ‖I₆IntegrandC z t‖ := by
          simp [I₆IntegrandC_deriv, mul_assoc]
      _ ≤ (Real.pi * t) * (C₀ * Real.exp (-π * ε * t)) := by
          gcongr; simp [Complex.norm_real, abs_of_nonneg ht0, abs_of_nonneg Real.pi_pos.le]
      _ = bound t := by simp [bound]; ring
  have hbound_int : MeasureTheory.Integrable bound μ := by
    have hb : 0 < Real.pi * ε := by positivity
    have hIoi1 : MeasureTheory.IntegrableOn
        (fun t : ℝ => t * Real.exp (-(Real.pi * ε) * t)) (Set.Ioi (1 : ℝ)) MeasureTheory.volume :=
      ((by simpa [Real.rpow_one] using
        (integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ))
          (hs := by linarith) (hp := le_rfl) (b := Real.pi * ε) hb) :
        MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-(Real.pi * ε) * t))
          (Set.Ioi (0:ℝ)) MeasureTheory.volume)).mono_set (Set.Ioi_subset_Ioi (by norm_num))
    simpa [bound, μ, MeasureTheory.IntegrableOn, mul_assoc] using
      (integrableOn_Ici_iff_integrableOn_Ioi
        (f := fun t : ℝ => (C₀ * Real.pi) * t * Real.exp (-(Real.pi * ε) * t))
        (b := (1 : ℝ)) (by finiteness)).2 (by simpa [mul_assoc] using hIoi1.const_mul (C₀ * Real.pi))
  have hdiff :
      ∀ᵐ (t : ℝ) ∂μ, ∀ z ∈ Metric.ball u0 ε,
        HasDerivAt (fun w : ℂ => I₆IntegrandC w t) (I₆IntegrandC_deriv z t) z :=
    Filter.Eventually.of_forall fun t z _ => by
      have hlin : HasDerivAt (fun w : ℂ => (-(π : ℂ) * w * (t : ℂ))) (-(π : ℂ) * (t : ℂ)) z := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          ((hasDerivAt_id z).const_mul (-(π : ℂ) * (t : ℂ)))
      simpa [I₆IntegrandC_deriv, I₆IntegrandC, mul_assoc, mul_left_comm, mul_comm] using
        (by simpa using hlin.cexp : HasDerivAt (fun w : ℂ => Complex.exp (-(π : ℂ) * w * (t : ℂ)))
          (Complex.exp (-(π : ℂ) * z * (t : ℂ)) * (-(π : ℂ) * (t : ℂ))) z).const_mul (base₆ t)
  have hμ : (fun z : ℂ => ∫ t, I₆IntegrandC z t ∂μ) =
      fun z : ℂ => ∫ t in Set.Ici (1 : ℝ), I₆IntegrandC z t := funext fun _ => by simp [μ]
  exact (show HasDerivAt I₆'C (2 * ∫ t, I₆IntegrandC_deriv u0 t ∂μ) u0 by
    simpa [funext fun u => show I₆'C u = 2 * ∫ t in Set.Ici (1 : ℝ), I₆IntegrandC u t by
        simp [I₆'C, I₆IntegrandC, base₆, mul_assoc, mul_left_comm, mul_comm], mul_assoc] using
      (hμ ▸ (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := u0)
        (F := I₆IntegrandC) (F' := I₆IntegrandC_deriv) (bound := bound)
        (hs := Metric.ball_mem_nhds u0 hε) (hF_meas := Filter.Eventually.of_forall hF_meas)
        (hF_int := hF_int) (hF'_meas := hF'_meas)
        (h_bound := hbound) (bound_integrable := hbound_int) (h_diff := hdiff)).2).const_mul
      (2 : ℂ)).differentiableAt

/-- `aPrimeC` is analytic on the right half-plane. -/
public lemma aPrimeC_analyticOnNhd : AnalyticOnNhd ℂ aPrimeC rightHalfPlane :=
  (show DifferentiableOn ℂ aPrimeC rightHalfPlane by
    simpa [aPrimeC] using ((((I₁'C_differentiableOn.add I₂'C_differentiableOn).add
      I₃'C_differentiableOn).add I₄'C_differentiableOn).add
      I₅'C_differentiableOn).add (fun u hu =>
        (I₆'C_differentiableAt u hu).differentiableWithinAt)).analyticOnNhd rightHalfPlane_isOpen
end

end MagicFunction.g.CohnElkies.IntegralReps

namespace MagicFunction.g.CohnElkies

/--
For `u ≥ 0`, the radial profile `a'` from `MagicFunction.FourierEigenfunctions` agrees with the
real-integral definition `MagicFunction.a.RealIntegrals.a'`.

The prime `'` is part of the standard notation for this radial profile (it is not a derivative).
-/
public lemma a'_eq_realIntegrals_a' {u : ℝ} (hu : 0 ≤ u) :
    (MagicFunction.FourierEigenfunctions.a' : ℝ → ℂ) u = MagicFunction.a.RealIntegrals.a' u := by
  simp [MagicFunction.FourierEigenfunctions.a', MagicFunction.a.RealIntegrals.a',
    MagicFunction.a.SchwartzIntegrals.I₁'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₂'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₃'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₄'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₅'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₆'_apply_of_nonneg, hu]

end MagicFunction.g.CohnElkies

namespace MagicFunction.g.CohnElkies.IntegralReps

section LaplaceRepresentation

open scoped BigOperators UpperHalfPlane Topology intervalIntegral
open MeasureTheory Real Complex Filter
open UpperHalfPlane
open MagicFunction.FourierEigenfunctions
open MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrals MagicFunction.a.RealIntegrands
  MagicFunction.Parametrisations

local notation "c12π" => ‖(12 * (Complex.I : ℂ)) / (π : ℂ)‖
local notation "c36π2" => ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))‖

/-! ## Tail deformation -/

/-- Strip-bound core: bound `‖F (x + tI)‖` by the standard envelope when
`F (x + tI) = (φ₀''(-1/w) * w²) * exp(πIu(x + tI))` with `w = s + tI`, `|s| ≤ 1`. -/
private lemma norm_strip_le_of_hdef {u s t x : ℝ} {F : ℂ → ℂ} {Cφ Aφ C₀ : ℝ} (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd : ∀ z : ℍ, Aφ ≤ z.im → ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
      ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
    (hs : |s| ≤ (1 : ℝ)) (ht1 : (1 : ℝ) ≤ t) (htAφ : Aφ ≤ t)
    (hdef : F ((x : ℂ) + (t : ℂ) * Complex.I) =
      (φ₀'' ((-1 : ℂ) / (((s : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
        ((((s : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ (2 : ℕ))) *
          cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I))) :
    ‖F ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
        (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
  set K : ℝ := 4 * C₀ + (2 * c12π + c36π2) * Cφ
  let wH : ℍ := ⟨((s : ℝ) : ℂ) + (t : ℂ) * Complex.I, by simpa using by linarith⟩
  have hw_im : (wH : ℂ).im = t := by simp [wH]
  calc ‖F ((x : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ * Real.exp (-π * u * t) := by
          rw [hdef, show φ₀'' ((-1 : ℂ) / (wH : ℂ)) * ((wH : ℂ) ^ 2) =
              φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ)) by
            rw [show φ₀ (ModularGroup.S • wH) = φ₀'' ((ModularGroup.S • wH : ℍ) : ℂ) by simp,
              show ((ModularGroup.S • wH : ℍ) : ℂ) = (-1 : ℂ) / (wH : ℂ) by
                simpa using ModularGroup.coe_S_smul (z := wH)], norm_mul,
            show ‖cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I))‖ =
                Real.exp (-π * u * t) by
              rw [show ((π : ℂ) * Complex.I * (u : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I)) =
                  ((π * u * x : ℝ) : ℂ) * Complex.I - ((π * u * t : ℝ) : ℂ) by
                push_cast; ring_nf; simp [mul_left_comm, mul_comm, sub_eq_add_neg],
                Complex.norm_exp]
              simp [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]]
    _ ≤ (K * (t ^ (2 : ℕ) * Real.exp (2 * π * t))) * Real.exp (-π * u * t) :=
          mul_le_mul_of_nonneg_right (norm_phi0S_mul_sq_le wH hw_im hC₀_pos hC₀ hφbd ht1 htAφ <| by
            simp only [wH]
            linarith [norm_add_le ((s : ℝ) : ℂ) ((t : ℂ) * Complex.I),
              (by simpa [Complex.norm_real] using hs : ‖((s : ℝ) : ℂ)‖ ≤ (1 : ℝ)),
              (by simp [abs_of_nonneg (by linarith : (0:ℝ) ≤ t)] :
                ‖(t : ℂ) * Complex.I‖ = t)]) (Real.exp_pos _).le
    _ = K * (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
          rw [mul_assoc, mul_assoc, ← MagicFunction.g.CohnElkies.exp_two_pi_mul_mul_exp_neg_pi_mul]

/-- Top-edge decay: reduce `tendsto` of an interval integral to a pointwise strip bound. -/
private lemma tendsto_intervalIntegral_top_of_strip_bound {u : ℝ} (hu : 2 < u) {F : ℂ → ℂ}
    {x₁ x₂ : ℝ} (hlen : |x₂ - x₁| ≤ 1)
    (hF : ∀ Cφ Aφ C₀ x t : ℝ, 0 < C₀ →
      (∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im)) →
      (∀ z : ℍ, Aφ ≤ z.im → ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
        ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im)) →
      x ∈ Set.uIoc x₁ x₂ → (1 : ℝ) ≤ t → Aφ ≤ t →
      ‖F ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
          (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t))) :
    Tendsto (fun m : ℝ => ∫ x in x₁..x₂, F ((x : ℂ) + (m : ℂ) * Complex.I)) atTop (𝓝 0) := by
  obtain ⟨Cφ, Aφ, _, hφbd⟩ := exists_phi2'_phi4'_bound_exp
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  set K : ℝ := 4 * C₀ + (2 * c12π + c36π2) * Cφ
  set a : ℝ := π * (u - 2)
  have ha : 0 < a := mul_pos Real.pi_pos (sub_pos.2 hu)
  refine squeeze_zero_norm' (Filter.eventually_atTop.2 ⟨max 1 Aφ, fun m hm => ?_⟩) (by
    simpa [mul_zero] using tendsto_const_nhds.mul
      (by simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (2 : ℝ)) (b := a) ha :
        Tendsto (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-a * t)) atTop (𝓝 0)) :
      Tendsto (fun m : ℝ => K * (m ^ (2 : ℕ) * Real.exp (-a * m))) atTop (𝓝 0))
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (a := x₁) (b := x₂)
    (C := K * (m ^ (2 : ℕ) * Real.exp (-a * m)))
    (fun x hx => hF Cφ Aφ C₀ x m hC₀_pos hC₀ hφbd hx ((le_max_left _ _).trans hm)
      ((le_max_right _ _).trans hm))).trans ?_
  nlinarith [hlen, show 0 ≤ K * (m ^ (2 : ℕ) * Real.exp (-a * m)) by positivity]

private lemma tendsto_intervalIntegral_Φ₂'_top {u : ℝ} (hu : 2 < u) :
    Tendsto (fun m : ℝ => ∫ x in (-1 : ℝ)..0, Φ₂' u ((x : ℂ) + (m : ℂ) * Complex.I))
      atTop (𝓝 0) :=
  tendsto_intervalIntegral_top_of_strip_bound hu (x₁ := -1) (x₂ := 0) (by norm_num)
    fun _ _ _ x t h1 h2 h3 hx h4 h5 =>
      have hx' : x ∈ Set.Ioc (-1 : ℝ) 0 := Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 0) ▸ hx
      norm_strip_le_of_hdef (s := x + 1) (F := Φ₂' u) h1 h2 h3
        (by rw [abs_of_nonneg (by linarith [hx'.1.le] : (0:ℝ) ≤ x + 1)]; linarith [hx'.2])
        h4 h5 <| by
        simp [MagicFunction.a.ComplexIntegrands.Φ₂', MagicFunction.a.ComplexIntegrands.Φ₁',
          show (x : ℂ) + (t : ℂ) * Complex.I + 1 = ((x + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I by
            push_cast; ring, mul_assoc]

private lemma tendsto_intervalIntegral_Φ₄'_top {u : ℝ} (hu : 2 < u) :
    Tendsto (fun m : ℝ => ∫ x in (1 : ℝ)..0, Φ₄' u ((x : ℂ) + (m : ℂ) * Complex.I))
      atTop (𝓝 0) :=
  tendsto_intervalIntegral_top_of_strip_bound hu (x₁ := 1) (x₂ := 0) (by norm_num)
    fun _ _ _ x t h1 h2 h3 hx h4 h5 =>
      have hx' : x ∈ Set.Ioc (0 : ℝ) 1 := Set.uIoc_of_ge (by norm_num : (0:ℝ) ≤ 1) ▸ hx
      norm_strip_le_of_hdef (s := x - 1) (F := Φ₄' u) h1 h2 h3
        (by rw [abs_sub_comm, abs_of_nonneg (by linarith [hx'.2] : (0:ℝ) ≤ 1 - x)]
            linarith [hx'.1.le]) h4 h5 <| by
        simp [MagicFunction.a.ComplexIntegrands.Φ₄', MagicFunction.a.ComplexIntegrands.Φ₃',
          show (x : ℂ) + (t : ℂ) * Complex.I - 1 = ((x - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I by
            push_cast; ring, mul_assoc]

private lemma bottom_eq_I_smul_sub_of_rect_deform {f : ℂ → ℂ} {x₁ x₂ : ℝ}
    (hcontU : ContinuousOn f {z : ℂ | 0 < z.im})
    (hdiffU : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hint₁ : IntegrableOn (fun t : ℝ => f ((x₁ : ℂ) + (t : ℂ) * Complex.I))
      (Set.Ioi (1 : ℝ)) volume)
    (hint₂ : IntegrableOn (fun t : ℝ => f ((x₂ : ℂ) + (t : ℂ) * Complex.I))
      (Set.Ioi (1 : ℝ)) volume)
    (htop : Tendsto (fun m : ℝ => ∫ x in x₁..x₂, f ((x : ℂ) + (m : ℂ) * Complex.I))
      atTop (𝓝 0)) :
    (∫ x in x₁..x₂, f ((x : ℂ) + Complex.I)) =
      (Complex.I : ℂ) •
        ((∫ t in Set.Ioi (1 : ℝ), f ((x₁ : ℂ) + (t : ℂ) * Complex.I)) -
          ∫ t in Set.Ioi (1 : ℝ), f ((x₂ : ℂ) + (t : ℂ) * Complex.I)) := by
  simpa [smul_eq_mul, mul_sub, one_mul] using eq_sub_of_add_eq (by
    simpa [one_mul] using sub_eq_zero.mp <| Complex.rect_deform_of_tendsto_top (f := f)
      (x₁ := x₁) (x₂ := x₂) (y := (1 : ℝ))
      (hcontU.mono fun z hz => show 0 < z.im from lt_of_lt_of_le zero_lt_one
        (by simpa [mem_reProdIm] using hz : _ ∧ z.im ∈ Set.Ici (1 : ℝ)).2)
      (fun z hz =>
        have hz0 : 0 < z.im :=
          lt_trans zero_lt_one (by simpa [mem_reProdIm] using hz : _ ∧ z.im ∈ Set.Ioi (1 : ℝ)).2
        (hdiffU z hz0).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hz0))
      hint₁ hint₂ htop)

lemma I₂'_eq_deform_imag_axis {u : ℝ} (hu : 2 < u) :
    I₂' u = (Complex.I : ℂ) •
        ((∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) -
          ∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((t : ℂ) * Complex.I)) := by
  let g : ℝ → ℂ := fun x : ℝ => Φ₂' u ((x : ℂ) + Complex.I)
  have hΦ₁' := Φ₁'_contDiffOn_ℂ (r := u)
  rw [show I₂' u = ∫ x in (-1 : ℝ)..0, g x by
    dsimp [I₂', Φ₂]
    rw [show (∫ t in (0 : ℝ)..1, Φ₂' u (z₂' t)) =
        ∫ t in (0 : ℝ)..1, g (t + (-1 : ℝ)) from intervalIntegral.integral_congr fun t ht => by
          simp [g, show z₂' t = (-1 : ℂ) + (t : ℂ) + (Complex.I : ℂ) by
            simpa using z₂'_eq_of_mem (by simpa [Set.uIcc_of_le zero_le_one] using ht), add_comm],
      show (∫ t in (0 : ℝ)..1, g (t + (-1 : ℝ))) = ∫ x in (-1 : ℝ)..0, g x by norm_num]]
  simpa [zero_add] using bottom_eq_I_smul_sub_of_rect_deform (f := Φ₂' u)
    (x₁ := (-1 : ℝ)) (x₂ := (0 : ℝ)) hΦ₁'.continuousOn (hΦ₁'.differentiableOn (by simp))
    (by simpa [show (fun t : ℝ => Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) =
        fun t : ℝ => Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) * Φ₅' u ((t : ℂ) * Complex.I)
        from funext fun t => Φ₁'_shift_left (u := u) (t := t)]
      using (integrableOn_Φ₅'_imag_axis hu).const_mul _)
    (by simpa using integrableOn_Φ₂'_imag_axis hu) (tendsto_intervalIntegral_Φ₂'_top hu)

lemma I₄'_eq_deform_imag_axis {u : ℝ} (hu : 2 < u) :
    I₄' u = (Complex.I : ℂ) •
        ((∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) -
          ∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((t : ℂ) * Complex.I)) := by
  let g : ℝ → ℂ := fun x : ℝ => Φ₄' u ((x : ℂ) + Complex.I)
  have hΦ₃' := Φ₃'_contDiffOn_ℂ (r := u)
  rw [show I₄' u = ∫ x in (1 : ℝ)..0, g x by
    dsimp [I₄', Φ₄]
    rw [show (∫ t in (0 : ℝ)..1, (-1 : ℂ) * Φ₄' u (z₄' t)) =
        ∫ t in (0 : ℝ)..1, (-1 : ℂ) * g (1 - t) from
      intervalIntegral.integral_congr fun t ht => by
        simp [g, sub_eq_add_neg, show z₄' t = (1 : ℂ) - (t : ℂ) + (Complex.I : ℂ) by
          simpa using z₄'_eq_of_mem (t := t) (by simpa [Set.uIcc_of_le zero_le_one] using ht)],
      intervalIntegral.integral_const_mul,
      show (∫ t in (0 : ℝ)..1, g (1 - t)) = ∫ t in (0 : ℝ)..1, g t by norm_num]
    simpa using (intervalIntegral.integral_symm (a := (0 : ℝ)) (b := (1 : ℝ)) (f := g)).symm]
  simpa [zero_add] using bottom_eq_I_smul_sub_of_rect_deform (f := Φ₄' u)
    (x₁ := (1 : ℝ)) (x₂ := (0 : ℝ)) hΦ₃'.continuousOn (hΦ₃'.differentiableOn (by simp))
    (by simpa [show (fun t : ℝ => Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) =
        fun t : ℝ => Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) * Φ₅' u ((t : ℂ) * Complex.I)
        from funext fun t => Φ₃'_shift_right (u := u) (t := t)]
      using (integrableOn_Φ₅'_imag_axis hu).const_mul _)
    (by simpa using integrableOn_Φ₄'_imag_axis hu) (tendsto_intervalIntegral_Φ₄'_top hu)

lemma I₆'_eq_deform_imag_axis {u : ℝ} (hu : 2 < u) :
    I₆' u = (Complex.I : ℂ) *
        ((∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((t : ℂ) * Complex.I)) -
            2 * (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) +
              ∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((t : ℂ) * Complex.I)) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi (1 : ℝ))
  let f2 : ℝ → ℂ := fun t => Φ₂' u ((t : ℂ) * Complex.I)
  let f5 : ℝ → ℂ := fun t => Φ₅' u ((t : ℂ) * Complex.I)
  let f4 : ℝ → ℂ := fun t => Φ₄' u ((t : ℂ) * Complex.I)
  have hf2 : Integrable f2 μ := integrableOn_Φ₂'_imag_axis hu
  have hf5 : Integrable f5 μ := integrableOn_Φ₅'_imag_axis hu
  have hf4 : Integrable f4 μ := integrableOn_Φ₄'_imag_axis hu
  dsimp [I₆', Φ₆]
  rw [show (∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * Φ₆' u (z₆' t))
        = ∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I) from
      setIntegral_congr_fun measurableSet_Ici fun t ht => by
        simp [show z₆' t = (Complex.I : ℂ) * (t : ℂ) by
          simpa [mul_assoc, mul_comm, mul_left_comm] using z₆'_eq_of_mem ht, mul_comm],
    integral_Ici_eq_integral_Ioi,
    (integral_const_mul (μ := μ) (r := (2 : ℂ))
      (f := fun t : ℝ => (Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I))).symm,
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
      simpa [f2, f5, f4, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg]
        using (congrArg (fun z : ℂ => (Complex.I : ℂ) * z)
        (Φ_finite_difference_imag_axis (lt_trans zero_lt_one ht))).symm :
      ∀ t ∈ Set.Ioi (1 : ℝ), (2 : ℂ) * ((Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I)) =
        (Complex.I : ℂ) * (f2 t - 2 * f5 t + f4 t)),
    integral_const_mul (μ := μ) (r := (Complex.I : ℂ)) (f := fun t => f2 t - 2 * f5 t + f4 t)]
  calc (Complex.I : ℂ) * (∫ t, (f2 t - 2 * f5 t + f4 t) ∂μ)
      = (Complex.I : ℂ) * ((∫ t, f2 t - 2 * f5 t ∂μ) + ∫ t, f4 t ∂μ) := by
        simpa using congrArg ((Complex.I : ℂ) * ·)
          (integral_add (μ := μ) (hf2.sub (hf5.const_mul 2)) hf4)
    _ = (Complex.I : ℂ) * ((∫ t, f2 t ∂μ) - 2 * (∫ t, f5 t ∂μ) + ∫ t, f4 t ∂μ) := by
        rw [integral_sub (μ := μ) hf2 (hf5.const_mul 2),
          integral_const_mul (μ := μ) (r := (2 : ℂ)) (f := f5)]

/-- If `G t = E * Φ₅' u (tI)` for `t > 1`, then `∫ G = E * ∫ central` over `Ioi 1`. -/
private lemma ray_integral_eq_const_mul_central {u : ℝ} {G : ℝ → ℂ} {E : ℂ}
    (hG : ∀ t, 1 < t → G t = E * Φ₅' u ((t : ℂ) * Complex.I)) :
    (∫ t in Set.Ioi (1 : ℝ), G t) = E * (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) := by
  rw [setIntegral_congr_fun measurableSet_Ioi hG, integral_const_mul]

/-- Rewrite `I₂' + I₄' + I₆'` as an imaginary-axis integral of `Φ₅'` over `t ≥ 1`. -/
public lemma I₂'_add_I₄'_add_I₆'_eq_imag_axis_tail {u : ℝ} (hu : 2 < u) :
    I₂' u + I₄' u + I₆' u =
      (Complex.I : ℂ) *
        ((Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) +
              Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ)) *
          (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I))) := by
  rw [I₂'_eq_deform_imag_axis hu, I₄'_eq_deform_imag_axis hu, I₆'_eq_deform_imag_axis hu,
    ray_integral_eq_const_mul_central (G := fun t => Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I))
      (E := Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)))
      (fun t _ => by simpa [mul_assoc] using Φ₁'_shift_left (u := u) (t := t)),
    ray_integral_eq_const_mul_central (G := fun t => Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I))
      (E := Complex.exp (((π * u : ℝ) : ℂ) * Complex.I))
      (fun t _ => by simpa [mul_assoc] using Φ₃'_shift_right (u := u) (t := t))]
  simp [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm]; ring

/-! ## Main Laplace representation -/

/-- Main lemma for blueprint proposition `prop:a-double-zeros`. -/
public theorem aRadial_eq_laplace_phi0_main {u : ℝ} (hu : 2 < u) :
    MagicFunction.FourierEigenfunctions.a' u =
      (4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          (∫ t in Set.Ioi (0 : ℝ),
            ((t ^ (2 : ℕ) : ℝ) : ℂ) *
              φ₀'' ((Complex.I : ℂ) / (t : ℂ)) *
                Real.exp (-π * u * t)) := by
  have hu0 : 0 ≤ u := (lt_trans (by norm_num : (0 : ℝ) < 2) hu).le
  have ha : MagicFunction.FourierEigenfunctions.a' u = MagicFunction.a.RealIntegrals.a' u := by
    simpa using (MagicFunction.g.CohnElkies.a'_eq_realIntegrals_a' (u := u) hu0)
  rw [ha]
  dsimp [MagicFunction.a.RealIntegrals.a']
  have hsplit :
      MagicFunction.a.RealIntegrals.I₁' u + MagicFunction.a.RealIntegrals.I₂' u +
            MagicFunction.a.RealIntegrals.I₃' u + MagicFunction.a.RealIntegrals.I₄' u +
              MagicFunction.a.RealIntegrals.I₅' u + MagicFunction.a.RealIntegrals.I₆' u =
          (MagicFunction.a.RealIntegrals.I₁' u + MagicFunction.a.RealIntegrals.I₃' u +
              MagicFunction.a.RealIntegrals.I₅' u) +
            (MagicFunction.a.RealIntegrals.I₂' u + MagicFunction.a.RealIntegrals.I₄' u +
              MagicFunction.a.RealIntegrals.I₆' u) := by ring
  rw [hsplit, I₁'_add_I₃'_add_I₅'_eq_imag_axis (u := u),
    I₂'_add_I₄'_add_I₆'_eq_imag_axis_tail (u := u) hu]
  have hseg : (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * Complex.I)) =
      ∫ t in Set.Ioc (0 : ℝ) 1, Φ₅' u ((t : ℂ) * Complex.I) := by
    simp [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  rw [hseg]
  have hIoi :
      (∫ t in Set.Ioc (0 : ℝ) 1, Φ₅' u ((t : ℂ) * Complex.I)) +
          (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) =
        ∫ t in Set.Ioi (0 : ℝ), Φ₅' u ((t : ℂ) * Complex.I) := by
    have h5Ioi0 : IntegrableOn (fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)) (Set.Ioi (0 : ℝ)) volume :=
      by simpa [IntegrableOn, Φ₅'_imag_axis_eq_neg_aLaplaceIntegrand] using
        (aLaplaceIntegral_convergent hu).neg'
    have h5Ioc := h5Ioi0.mono_set (fun t (ht : t ∈ Set.Ioc (0 : ℝ) 1) => ht.1)
    rw [show (Set.Ioi (0 : ℝ)) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) by
      simp [Set.Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one]]
    simpa [add_comm, add_left_comm, add_assoc] using
      (MeasureTheory.setIntegral_union (μ := volume)
        (f := fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I))
        (s := Set.Ioc (0 : ℝ) 1) (t := Set.Ioi (1 : ℝ))
        (hst := Set.Ioc_disjoint_Ioi_same)
        (ht := measurableSet_Ioi) h5Ioc (integrableOn_Φ₅'_imag_axis (u := u) hu)).symm
  set coeff : ℂ :=
    (Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) +
        Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ))
  have hcomb :
      (Complex.I : ℂ) * (coeff * (∫ t in Set.Ioc (0 : ℝ) 1, Φ₅' u ((t : ℂ) * Complex.I))) +
          (Complex.I : ℂ) * (coeff * (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I))) =
        (Complex.I : ℂ) * (coeff * (∫ t in Set.Ioi (0 : ℝ), Φ₅' u ((t : ℂ) * Complex.I))) := by
    rw [← hIoi]; ring
  rw [hcomb]
  have hcoeff : coeff = -((4 * (Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) := by
    have hrew : coeff = -((2 : ℂ) - Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) -
        Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I))) := by simp [coeff]; ring
    have htrig := MagicFunction.g.CohnElkies.Trig.two_sub_exp_pi_mul_I_sub_exp_neg_pi_mul_I u
    have hhalf := MagicFunction.g.CohnElkies.Trig.two_sub_two_cos_eq_four_sin_sq u
    grind only
  have hΦ5 : (∫ t in Set.Ioi (0 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) =
      - (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t) := by
    rw [MeasureTheory.setIntegral_congr_fun (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
      (g := fun t => -aLaplaceIntegrand u t)
      (fun t _ => by simpa using (Φ₅'_imag_axis_eq_neg_aLaplaceIntegrand (u := u) (t := t)))]
    simp [integral_neg]
  rw [hcoeff, hΦ5]
  simp [aLaplaceIntegrand, mul_assoc, mul_left_comm, mul_comm]

end LaplaceRepresentation

open scoped BigOperators Topology UpperHalfPlane

open MeasureTheory Real Complex UpperHalfPlane Filter
open SpherePacking
open SpherePacking.Integration (μIoi0)
open MagicFunction.FourierEigenfunctions

/-- The analytic continuation domain `U = {u : ℂ | 0 < re u} \ {2}`. -/
@[expose] public def ACDomain : Set ℂ := rightHalfPlane \ {2}

/-- The analytic continuation domain `ACDomain` is preconnected. -/
public lemma ACDomain_isPreconnected : IsPreconnected ACDomain := by
  -- We use a homeomorphism `ℂ ≃ₜ {u : ℂ // 0 < u.re}` to reduce to connectedness of the
  -- complement of a singleton in `ℂ`.
  let z2 : {u : ℂ // 0 < u.re} := ⟨(2 : ℂ), by simp⟩
  let h₃ : (Set.Ioi (0 : ℝ) × ℝ) ≃ₜ {u : ℂ // 0 < u.re} :=
    { toEquiv :=
        { toFun := fun p =>
            ⟨(p.1 : ℝ) + p.2 * Complex.I, by
              have hp : (0 : ℝ) < (p.1 : ℝ) := p.1.2
              simpa using hp⟩
          invFun := fun z => (⟨z.1.re, z.2⟩, z.1.im)
          left_inv := by
            rintro ⟨x, y⟩
            ext <;> simp
          right_inv := by
            rintro ⟨z, hz⟩
            apply Subtype.ext
            simp [Complex.re_add_im] }
      continuous_toFun := by
        refine
            (show Continuous (fun p : Set.Ioi (0 : ℝ) × ℝ => (p.1 : ℝ) + p.2 * Complex.I) by
              fun_prop).subtype_mk fun p => by
            have hp : (0 : ℝ) < (p.1 : ℝ) := p.1.2
            simpa using hp
      continuous_invFun := by
        fun_prop }
  let h : ℂ ≃ₜ {u : ℂ // 0 < u.re} :=
    (Complex.equivRealProdCLM.toHomeomorph.trans
          ((Real.expOrderIso.toHomeomorph).prodCongr (Homeomorph.refl ℝ))).trans h₃
  have hpre : IsPreconnected ({z2}ᶜ : Set {u : ℂ // 0 < u.re}) := by
    have hconn : IsConnected ({h.symm z2}ᶜ : Set ℂ) :=
      isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) (h.symm z2)
    have himage :
        h '' ({h.symm z2}ᶜ : Set ℂ) = ({z2}ᶜ : Set {u : ℂ // 0 < u.re}) := by
      ext z
      refine ⟨?_, fun hz => ⟨h.symm z, by simpa, by simp⟩⟩
      rintro ⟨x, hx, rfl⟩
      have hx' : x ≠ h.symm z2 := by simpa using hx
      simpa using fun hz => hx' (by simpa using congrArg h.symm hz)
    simpa [himage] using hconn.isPreconnected.image h h.continuous.continuousOn
  have hval :
      ((Subtype.val : {u : ℂ // 0 < u.re} → ℂ) '' ({z2}ᶜ :
          Set {u : ℂ // 0 < u.re})) = ACDomain := by
    ext u
    refine ⟨?_, ?_⟩
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ≠ z2 := by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
      exact ⟨z.2, by simpa using fun hEq => hz' (Subtype.ext hEq)⟩
    · rintro hu
      have hu_re : 0 < u.re := by simpa [rightHalfPlane] using hu.1
      refine ⟨⟨u, hu_re⟩, ?_, rfl⟩
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using fun hEq =>
        (by simpa using hu.2 : u ≠ (2 : ℂ)) (congrArg Subtype.val hEq)
  simpa [hval] using
    hpre.image (Subtype.val : {u : ℂ // 0 < u.re} → ℂ) continuous_subtype_val.continuousOn

/-- Generic analytic continuation on `ACDomain = {Re u > 0} \ {2}`. -/
public theorem analytic_continuation_of_gt2
    {value : ℝ → ℂ} {rhsC : ℂ → ℂ} {rhsR : ℝ → ℂ}
    (h_extension : ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f ACDomain ∧
      ∀ u : ℝ, 0 < u → u ≠ 2 → f (u : ℂ) = value u)
    (h_rhs_analytic : AnalyticOnNhd ℂ rhsC ACDomain)
    (h_rhs_ofReal : ∀ u : ℝ, rhsC (u : ℂ) = rhsR u)
    (h_gt2 : ∀ r : ℝ, 2 < r → value r = rhsR r)
    {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    value u = rhsR u := by
  rcases h_extension with ⟨f, hf_analytic, hf_ofReal⟩
  have hf_gt2 : ∀ r : ℝ, 2 < r → f (r : ℂ) = rhsC (r : ℂ) := fun r hr =>
    (hf_ofReal r (lt_trans (by norm_num) hr) (by linarith)).trans
      ((h_gt2 r hr).trans (h_rhs_ofReal r).symm)
  have hFreq : (∃ᶠ z in 𝓝[≠] (3 : ℂ), f z = rhsC z) := Filter.frequently_iff.2 <| by
    intro U hU
    obtain ⟨V, hVnhds, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hU
    obtain ⟨ε, hεpos, hball⟩ := Metric.mem_nhds_iff.1 hVnhds
    refine ⟨((3 + ε / 2 : ℝ) : ℂ), hVsub ⟨hball ?_, ?_⟩, by
      simpa using hf_gt2 (3 + ε / 2) (by nlinarith [hεpos])⟩
    · simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε / 2),
        abs_of_nonneg hεpos.le] using half_lt_self hεpos
    · simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (show ((3 + ε / 2 : ℝ) : ℂ) ≠ 3 by exact_mod_cast
          (by nlinarith [hεpos.ne'] : (3 + ε / 2 : ℝ) ≠ 3))
  have hEqOn : Set.EqOn f rhsC ACDomain :=
    AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf_analytic h_rhs_analytic
      ACDomain_isPreconnected (by simp [ACDomain, rightHalfPlane]) hFreq
  have hu_mem : (u : ℂ) ∈ ACDomain :=
    ⟨by simpa [rightHalfPlane] using hu,
      by simpa [ACDomain, Set.mem_singleton_iff] using (show (u : ℂ) ≠ 2 by exact_mod_cast hu2)⟩
  exact (hf_ofReal u hu hu2).symm.trans ((hEqOn hu_mem).trans (h_rhs_ofReal u))

/-- If `inner` is analytic on `ACDomain`, then so is
`u ↦ sign * (sin (π u / 2))^2 * inner u` for any constant `sign : ℂ`. -/
public lemma analyticOnNhd_sinSq_prefactor_mul
    (sign : ℂ) {inner : ℂ → ℂ} (hinner : AnalyticOnNhd ℂ inner ACDomain) :
    AnalyticOnNhd ℂ
      (fun u : ℂ => sign * (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ) * inner u) ACDomain :=
  (analyticOnNhd_const.mul (by
    have hsin : AnalyticOnNhd ℂ (fun u : ℂ => Complex.sin ((π : ℂ) * u / 2)) ACDomain := by
      simpa [Function.comp] using ((by simpa using (analyticOnNhd_sin (s := (Set.univ : Set ℂ)))) :
          AnalyticOnNhd ℂ (fun z : ℂ => Complex.sin z) (Set.univ : Set ℂ)).comp
        (AnalyticOnNhd.div_const (analyticOnNhd_const.mul analyticOnNhd_id) :
          AnalyticOnNhd ℂ (fun u : ℂ => (π : ℂ) * u / 2) ACDomain) (by intro _ _; simp)
    exact hsin.pow 2)).mul hinner

noncomputable section

/-- The `u`-independent bracket in the "another integral" integrand for `a'`. -/
@[expose] public def aAnotherBase (t : ℝ) : ℂ :=
  (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
    ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
    ((8640 / π : ℝ) : ℂ) * t - ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))

/-- Complex-parameter integrand for the "another integral" representation of `a'`. -/
@[expose] public def aAnotherIntegrandC (u : ℂ) (t : ℝ) : ℂ :=
  aAnotherBase t * Complex.exp (-(π : ℂ) * u * (t : ℂ))

/-- Complex-parameter "another integral" for `a'`. -/
@[expose] public def aAnotherIntegralC (u : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrandC u t

private lemma norm_exp_le_of_re_ge {z : ℂ} {t c : ℝ} (ht0 : 0 ≤ t) (hcz : c ≤ z.re) :
    ‖Complex.exp (-(π : ℂ) * z * (t : ℂ))‖ ≤ Real.exp (-π * c * t) := by
  simpa [Complex.norm_exp, show (-(π : ℂ) * z * (t : ℂ)).re = -π * z.re * t by
    simp [mul_assoc, Complex.mul_re, sub_eq_add_neg, add_comm]] using
    Real.exp_le_exp.mpr <| by simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonpos_left hcz (by nlinarith [Real.pi_pos, ht0] : (-π * t : ℝ) ≤ 0)

/-- Analyticity of `u ↦ ∫ t ∈ (0, ∞), base(t) * Complex.exp(-π u t)` on the right half-plane. -/
public theorem analyticOnNhd_integral_base_exp
    {base : ℝ → ℂ}
    (hbase_cont : ContinuousOn base (Set.Ioi (0 : ℝ)))
    (hbase_int : ∀ u : ℝ, 0 < u →
      IntegrableOn (fun t : ℝ => base t * (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ))) :
    AnalyticOnNhd ℂ
      (fun u : ℂ => ∫ t in Set.Ioi (0 : ℝ), base t * Complex.exp (-(π : ℂ) * u * (t : ℂ)))
      rightHalfPlane := by
  have hDiff :
      DifferentiableOn ℂ
        (fun u : ℂ => ∫ t in Set.Ioi (0 : ℝ), base t * Complex.exp (-(π : ℂ) * u * (t : ℂ)))
        rightHalfPlane := by
    intro u hu
    have hu0 : 0 < u.re := by simpa [rightHalfPlane] using hu
    set ε : ℝ := u.re / 2
    have hε : 0 < ε := by positivity
    let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
    let F : ℂ → ℝ → ℂ := fun z t => base t * Complex.exp (-(π : ℂ) * z * (t : ℂ))
    let F' : ℂ → ℝ → ℂ := fun z t => (-(π : ℂ) * (t : ℂ)) * F z t
    have hF_meas : ∀ z : ℂ, AEStronglyMeasurable (F z) μ := fun z =>
      (hbase_cont.aestronglyMeasurable measurableSet_Ioi).mul
        ((by fun_prop : Continuous fun t : ℝ =>
          Complex.exp (-(π : ℂ) * z * (t : ℂ))).aestronglyMeasurable)
    have hBase_ε2 :
        Integrable (fun t : ℝ => base t * (Real.exp (-π * (ε / 2) * t) : ℂ)) μ := by
      simpa [μ, IntegrableOn] using (hbase_int (ε / 2) (by positivity))
    have hmem_Ioi : ∀ᵐ t ∂μ, t ∈ Set.Ioi (0 : ℝ) := by
      simpa [μ] using ae_restrict_mem (μ := (volume : Measure ℝ))
        (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
    have hF_int : Integrable (F u) μ := by
      refine Integrable.mono' (g := fun t : ℝ => ‖base t * (Real.exp (-π * (ε / 2) * t) : ℂ)‖)
        hBase_ε2.norm (hF_meas u) ?_
      filter_upwards [hmem_Ioi] with t ht
      calc ‖F u t‖ = ‖base t‖ * ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ := by simp [F]
        _ ≤ ‖base t‖ * Real.exp (-π * (ε / 2) * t) := mul_le_mul_of_nonneg_left
            (norm_exp_le_of_re_ge ht.le (by dsimp [ε]; linarith : (ε / 2 : ℝ) ≤ u.re))
            (norm_nonneg _)
        _ = ‖base t * (Real.exp (-π * (ε / 2) * t) : ℂ)‖ := by
          rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
    let bound : ℝ → ℝ := fun t => (2 / ε) * ‖base t * (Real.exp (-π * (ε / 2) * t) : ℂ)‖
    have hbound_int : Integrable bound μ := by
      simpa [bound] using hBase_ε2.norm.const_mul (2 / ε)
    have hbound : ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball u ε, ‖F' z t‖ ≤ bound t := by
      filter_upwards [hmem_Ioi] with t ht z hz
      have htpos : (0 : ℝ) < t := ht
      have hzre : ε ≤ z.re := by
        have hlt : |z.re - u.re| < ε := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            lt_of_le_of_lt (abs_re_le_norm (z - u))
              (by simpa [Metric.mem_ball] using hz : ‖z - u‖ < ε)
        dsimp [ε] at hlt ⊢; nlinarith [(abs_lt.mp hlt).1]
      have hExpTrade :
          (π * t) * Real.exp (-π * ε * t) ≤ (2 / ε) * Real.exp (-π * (ε / 2) * t) := by
        have hπε : (0 : ℝ) < π * ε := by positivity
        have hc2 : (0 : ℝ) ≤ 2 / (π * ε) := (div_pos (by norm_num) hπε).le
        have ht_le : t ≤ (2 / (π * ε)) * Real.exp ((π * ε / 2) * t) := by
          simpa [mul_assoc, show (2 / (π * ε)) * ((π * ε / 2) * t) = t by field_simp [hπε.ne']]
            using mul_le_mul_of_nonneg_left
              (by linarith [Real.add_one_le_exp ((π * ε / 2) * t)] :
                (π * ε / 2) * t ≤ Real.exp ((π * ε / 2) * t)) hc2
        have hbase : t * Real.exp (-(π * ε) * t) ≤ (2 / (π * ε)) * Real.exp (-(π * ε / 2) * t) := by
          refine (mul_le_mul_of_nonneg_right ht_le (Real.exp_nonneg (-(π * ε) * t))).trans_eq ?_
          rw [mul_assoc, ← Real.exp_add]; ring_nf
        simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv, Real.pi_ne_zero,
          ne_of_gt hε] using mul_le_mul_of_nonneg_left hbase Real.pi_pos.le
      have hnorm_integ : ‖F z t‖ ≤ ‖base t‖ * Real.exp (-π * ε * t) := by
        simpa [F, norm_mul, mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left (norm_exp_le_of_re_ge htpos.le hzre) (norm_nonneg _)
      have hnorm_base_exp : ‖base t * (Real.exp (-π * (ε / 2) * t) : ℂ)‖ =
          ‖base t‖ * Real.exp (-π * (ε / 2) * t) := by
        rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
      calc ‖F' z t‖ = ‖(-(π : ℂ) * (t : ℂ))‖ * ‖F z t‖ := by simp [F']
        _ ≤ (π * t) * ‖F z t‖ := by rw [show ‖(-(π : ℂ) * (t : ℂ))‖ = π * t from by
              simp [abs_of_pos htpos, Real.pi_pos.le]]
        _ ≤ (π * t) * (‖base t‖ * Real.exp (-π * ε * t)) :=
          mul_le_mul_of_nonneg_left hnorm_integ (by nlinarith [Real.pi_pos, htpos.le])
        _ ≤ (2 / ε) * (‖base t‖ * Real.exp (-π * (ε / 2) * t)) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_left hExpTrade (norm_nonneg (base t))
        _ = bound t := by rw [← hnorm_base_exp]
    have hdiff : ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball u ε,
        HasDerivAt (fun w : ℂ => F w t) (F' z t) z :=
      Filter.Eventually.of_forall fun t z _hz => by
        simpa [F, F', mul_assoc, mul_left_comm, mul_comm] using
          (show HasDerivAt (fun w : ℂ => Complex.exp (-(π : ℂ) * w * (t : ℂ)))
              (Complex.exp (-(π : ℂ) * z * (t : ℂ)) * (-(π : ℂ) * (t : ℂ))) z from
            (show HasDerivAt (fun w : ℂ => (-(π : ℂ) * w * (t : ℂ))) (-(π : ℂ) * (t : ℂ)) z by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                ((hasDerivAt_id z).const_mul (-(π : ℂ) * (t : ℂ)))).cexp).const_mul (base t)
    have hDeriv : HasDerivAt (fun z : ℂ => ∫ t, F z t ∂μ) (∫ t, F' u t ∂μ) u :=
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
        (s := Metric.ball u ε) (Metric.ball_mem_nhds u hε) (x₀ := u)
        (F := F) (F' := F') (bound := bound)
        (hF_meas := Filter.Eventually.of_forall hF_meas) (hF_int := hF_int)
        (hF'_meas := ((by fun_prop : Continuous fun t : ℝ =>
            (-(π : ℂ) * (t : ℂ))).aestronglyMeasurable).mul (hF_meas u))
        (h_bound := hbound) (bound_integrable := hbound_int) (h_diff := hdiff)).2
    exact hDeriv.differentiableAt.differentiableWithinAt
  exact hDiff.analyticOnNhd rightHalfPlane_isOpen

/-- `aAnotherIntegralC` is analytic on the right half-plane. -/
public lemma aAnotherIntegralC_analyticOnNhd :
    AnalyticOnNhd ℂ aAnotherIntegralC rightHalfPlane := by
  have hcontIdiv : ContinuousOn (fun t : ℝ => (Complex.I : ℂ) / (t : ℂ)) (Set.Ioi (0 : ℝ)) :=
    continuous_const.continuousOn.div continuous_ofReal.continuousOn fun t ht => by
      exact_mod_cast ne_of_gt ht
  have hφcomp : ContinuousOn (fun t : ℝ => φ₀'' ((Complex.I : ℂ) / (t : ℂ))) (Set.Ioi (0 : ℝ)) :=
    (by simpa using MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn :
      ContinuousOn (fun z : ℂ => φ₀'' z) upperHalfPlaneSet).comp hcontIdiv fun t ht => by
        change 0 < (((Complex.I : ℂ) / (t : ℂ)) : ℂ).im
        rw [imag_I_div t]; exact inv_pos.2 (by simpa using ht)
  have hbase : ContinuousOn aAnotherBase (Set.Ioi (0 : ℝ)) :=
    ((((by fun_prop : Continuous fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ)).continuousOn.mul
      hφcomp).sub (continuousOn_const.mul (by fun_prop : Continuous fun t : ℝ =>
      ((Real.exp (2 * π * t)) : ℂ)).continuousOn)).add
      (continuousOn_const.mul continuous_ofReal.continuousOn)).sub continuousOn_const
  convert analyticOnNhd_integral_base_exp (base := aAnotherBase)
    hbase (fun u hu => (aAnotherIntegrand_integrable_of_pos hu).congr <|
      Filter.Eventually.of_forall fun t => by
        simp [aAnotherIntegrand, aAnotherBase, mul_assoc]) using 1

/-!
## Analytic RHS function on `ℂ`

This is the complex-analytic function whose restriction to the real axis is the blueprint RHS.
-/

def aAnotherRHS (u : ℂ) : ℂ :=
  (4 * Complex.I) * (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ) *
    ((36 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * (u - 2)) -
      (8640 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u ^ (2 : ℕ)) +
      (18144 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u) + aAnotherIntegralC u)

lemma aAnotherRHS_analyticOnNhd :
    AnalyticOnNhd ℂ aAnotherRHS ACDomain := by
  have hπ : (π : ℂ) ≠ 0 := mod_cast Real.pi_ne_zero
  have hu_ne0 : ∀ u ∈ ACDomain, u ≠ 0 := fun u hu h0 =>
    absurd (by simpa [rightHalfPlane] using hu.1) (by simp [h0])
  have hterm1 :
      AnalyticOnNhd ℂ (fun u : ℂ => (36 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * (u - 2))) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const))
      fun u hu => mul_ne_zero (pow_ne_zero _ hπ) (sub_ne_zero.2 (by simpa using hu.2))
  have hterm2 :
      AnalyticOnNhd ℂ (fun u : ℂ => (8640 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u ^ (2 : ℕ))) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul (analyticOnNhd_id.pow 2))
      fun u hu => mul_ne_zero (pow_ne_zero _ hπ) (pow_ne_zero _ (hu_ne0 u hu))
  have hterm3 :
      AnalyticOnNhd ℂ (fun u : ℂ => (18144 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u)) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul analyticOnNhd_id)
      fun u hu => mul_ne_zero (pow_ne_zero _ hπ) (hu_ne0 u hu)
  have hinner :
      AnalyticOnNhd ℂ
        (fun u : ℂ =>
          (36 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * (u - 2)) -
              (8640 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u ^ (2 : ℕ)) +
            (18144 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u) + aAnotherIntegralC u)
        ACDomain := by
    simpa [sub_eq_add_neg, add_assoc] using (hterm1.sub hterm2).add
      (hterm3.add (aAnotherIntegralC_analyticOnNhd.mono fun u hu => hu.1))
  simpa [aAnotherRHS] using
    analyticOnNhd_sinSq_prefactor_mul (sign := 4 * Complex.I) hinner

/-- Analytic-continuation step: extend the "another integral" identity for `a'` from `u > 2`
to all real `0 < u` with `u ≠ 2`. -/
public theorem aRadial_eq_another_integral_analytic_continuation_of_gt2
  (h_gt2 :
      ∀ r : ℝ, 2 < r →
        a' r =
          (4 * Complex.I) * (Real.sin (π * r / 2)) ^ (2 : ℕ) *
            ((36 : ℂ) / (π ^ (3 : ℕ) * (r - 2)) -
              (8640 : ℂ) / (π ^ (3 : ℕ) * r ^ (2 : ℕ)) +
              (18144 : ℂ) / (π ^ (3 : ℕ) * r) +
                ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand r t))
    {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    a' u =
      (4 * Complex.I) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
        ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
          (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * u) +
            ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t) := by
  refine analytic_continuation_of_gt2
    ⟨aPrimeC, aPrimeC_analyticOnNhd.mono (fun u hu => hu.1), fun u hu _ => by
      simpa [show MagicFunction.a.RealIntegrals.a' u = a' u by
        simpa using (MagicFunction.g.CohnElkies.a'_eq_realIntegrals_a' (u := u) (hu := hu.le)).symm]
        using aPrimeC_ofReal u⟩
    aAnotherRHS_analyticOnNhd
    (rhsR := fun r : ℝ =>
      (4 * Complex.I) * (Real.sin (π * r / 2)) ^ (2 : ℕ) *
        ((36 : ℂ) / (π ^ (3 : ℕ) * (r - 2)) -
          (8640 : ℂ) / (π ^ (3 : ℕ) * r ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * r) +
            ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand r t))
    (fun r => by
      simp only [aAnotherRHS, show (Complex.sin ((π : ℂ) * (r : ℂ) / 2)) ^ (2 : ℕ) =
        ((Real.sin (π * r / 2)) ^ (2 : ℕ) : ℂ) by simp,
        show aAnotherIntegralC (r : ℂ) = ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand r t from
          MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
            measurableSet_Ioi (fun t _ => by
              simp [aAnotherIntegrandC, aAnotherBase, aAnotherIntegrand])])
    h_gt2 hu hu2

/-- Integral of a triple sum is the sum of the integrals, under integrability assumptions. -/
public lemma integral_add_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h : α → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, ((f x + g x) + h x) ∂ μ) =
      (∫ x, f x ∂ μ) + (∫ x, g x ∂ μ) + (∫ x, h x ∂ μ) := by
  simpa [add_assoc, MeasureTheory.integral_add (μ := μ) hf hg] using
    MeasureTheory.integral_add (μ := μ) (hf.add hg) hh

/-- `∫_{t > 0} exp (-π u t) dt = 1 / (π u)` as a complex-valued integral, for `u > 0`. -/
public lemma integral_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * u) : ℝ) : ℂ) := by
  change (∫ t : ℝ, (Real.exp (-π * u * t) : ℂ) ∂μIoi0) = ((1 / (π * u) : ℝ) : ℂ)
  rw [← MagicFunction.g.CohnElkies.integral_exp_neg_pi_mul_Ioi (u := u) hu]
  exact integral_ofReal (μ := μIoi0) (𝕜 := ℂ)

/-- `∫_{t > 0} t * exp (-π u t) dt = 1 / (π u)^2` as a complex-valued integral, for `u > 0`. -/
public lemma integral_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), (t * Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) := by
  change (∫ t : ℝ, (t * Real.exp (-π * u * t) : ℂ) ∂μIoi0) =
      ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ)
  rw [← MagicFunction.g.CohnElkies.integral_mul_exp_neg_pi_mul_Ioi (u := u) hu]
  simpa [Complex.ofReal_mul] using
    integral_ofReal (μ := μIoi0) (𝕜 := ℂ) (f := fun t : ℝ => t * Real.exp (-π * u * t))

/-- `∫_{t > 0} exp (2π t) * exp (-π u t) dt = 1 / (π (u - 2))` as a complex-valued integral,
for `u > 2`. -/
public lemma integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 2 < u) :
    (∫ t in Set.Ioi (0 : ℝ), (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * (u - 2)) : ℝ) : ℂ) := by
  change (∫ t : ℝ, (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ) ∂μIoi0) =
      ((1 / (π * (u - 2)) : ℝ) : ℂ)
  rw [← MagicFunction.g.CohnElkies.integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi (u := u) hu]
  simpa [Complex.ofReal_mul] using integral_ofReal (μ := μIoi0) (𝕜 := ℂ)
    (f := fun t : ℝ => Real.exp (2 * π * t) * Real.exp (-π * u * t))

/-- Integrability of `t ↦ exp (-π u t)` on `t > 0` as a complex-valued function, for `u > 0`. -/
public lemma integrableOn_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) := by
  have hne : (∫ t : ℝ, (Real.exp (-π * u * t) : ℂ) ∂μIoi0) ≠ 0 := by
    rw [show (∫ t : ℝ, (Real.exp (-π * u * t) : ℂ) ∂μIoi0) = ((1 / (π * u) : ℝ) : ℂ) from by
      simpa [μIoi0] using integral_exp_neg_pi_mul_Ioi_complex (u := u) hu]
    exact_mod_cast one_div_ne_zero (mul_ne_zero Real.pi_ne_zero hu.ne')
  simpa [MeasureTheory.IntegrableOn, μIoi0] using
    MeasureTheory.Integrable.of_integral_ne_zero (μ := μIoi0) hne

/-- Integrability of `t ↦ t * exp (-π u t)` on `t > 0` as a complex-valued function, for
`u > 0`. -/
public lemma integrableOn_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => (t * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) := by
  have hne : (∫ t : ℝ, (t * Real.exp (-π * u * t) : ℂ) ∂μIoi0) ≠ 0 := by
    rw [show (∫ t : ℝ, (t * Real.exp (-π * u * t) : ℂ) ∂μIoi0) =
        ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) from by
      simpa [μIoi0] using integral_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu]
    exact_mod_cast one_div_ne_zero (pow_ne_zero 2 (mul_ne_zero Real.pi_ne_zero hu.ne'))
  simpa [MeasureTheory.IntegrableOn, μIoi0] using
    MeasureTheory.Integrable.of_integral_ne_zero (μ := μIoi0) hne

/-- Integrability of `t ↦ exp (2π t) * exp (-π u t)` on `t > 0` as a complex-valued function, for
`u > 2`. -/
public lemma integrableOn_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  have hne :
      (∫ t : ℝ, (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ) ∂μIoi0) ≠ 0 := by
    rw [show (∫ t : ℝ, (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ) ∂μIoi0) =
        ((1 / (π * (u - 2)) : ℝ) : ℂ) from by
      simpa [μIoi0] using integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu]
    exact_mod_cast one_div_ne_zero (mul_ne_zero Real.pi_ne_zero (sub_pos.2 hu).ne')
  simpa [MeasureTheory.IntegrableOn, μIoi0] using
    MeasureTheory.Integrable.of_integral_ne_zero (μ := μIoi0) hne

end

end MagicFunction.g.CohnElkies.IntegralReps
