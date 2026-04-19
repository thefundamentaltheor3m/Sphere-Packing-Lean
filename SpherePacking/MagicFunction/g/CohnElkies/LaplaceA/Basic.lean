module
public import SpherePacking.MagicFunction.g.CohnElkies.Defs
import SpherePacking.MagicFunction.g.CohnElkies.IntegralPieces
public import SpherePacking.MagicFunction.g.CohnElkies.LaplaceLemmas
public import SpherePacking.MagicFunction.g.CohnElkies.IntegralReductions
public import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.Schwartz.DecayI1
public import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
public import SpherePacking.MagicFunction.g.CohnElkies.DeltaBounds
public import SpherePacking.ModularForms.PhiTransform
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import SpherePacking.ForMathlib.ModularFormsHelpers

/-!
# Laplace integral for `a'`

This file defines the Laplace integrand `aLaplaceIntegrand` and proves the basic
measurability/integrability lemmas needed for the blueprint proposition `prop:a-double-zeros`
(the main statement is `aRadial_eq_laplace_phi0_main` in the `IntegralReps` namespace).

## Main definitions
* `MagicFunction.g.CohnElkies.IntegralReps.aLaplaceIntegrand`

## Main statements
* `MagicFunction.g.CohnElkies.IntegralReps.aLaplaceIntegral_convergent`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

noncomputable section

open scoped BigOperators UpperHalfPlane
open MeasureTheory Real Complex Filter
open UpperHalfPlane
open MagicFunction.FourierEigenfunctions

/-- The Laplace integrand appearing in the representation of the radial profile `a'`. -/
@[expose] public def aLaplaceIntegrand (u t : ℝ) : ℂ :=
  ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) * Real.exp (-π * u * t)

lemma continuousOn_phi0''_div_Ioi :
    ContinuousOn (fun t : ℝ => φ₀'' ((Complex.I : ℂ) / (t : ℂ))) (Set.Ioi (0 : ℝ)) :=
  MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn.comp
    (continuousOn_const.div Complex.continuous_ofReal.continuousOn
      fun _ ht => by exact_mod_cast (ne_of_gt ht))
    fun _ ht => by simp_all

lemma aestronglyMeasurable_phi0''_div_Ioi :
    AEStronglyMeasurable (fun t : ℝ => φ₀'' ((Complex.I : ℂ) / (t : ℂ)))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
  (continuousOn_phi0''_div_Ioi).aestronglyMeasurable measurableSet_Ioi

/-- Integrability of `t^2 * exp(-a * t)` on a ray `Set.Ioi A` (for `0 < a`). -/
public lemma integrableOn_sq_mul_exp_neg (A a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-a * t)) (Set.Ioi A) := by
  have hb : 0 < a / 2 := half_pos ha
  have hcont : ContinuousOn (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-a * t)) (Set.Ici A) := by
    fun_prop
  have hmul : (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-a * t)) =O[atTop]
        fun t : ℝ => Real.exp ((a / 2) * t) * Real.exp (-a * t) :=
    (isLittleO_pow_exp_pos_mul_atTop (k := 2) hb).isBigO.mul (Asymptotics.isBigO_refl _ _)
  refine integrable_of_isBigO_exp_neg (a := A) (b := a / 2) hb hcont
    (hmul.congr_right fun t => ?_)
  rw [← Real.exp_add]; congr 1; ring

lemma aestronglyMeasurable_aLaplaceIntegrand_Ioi (u : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => aLaplaceIntegrand u t)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have ht2 : AEStronglyMeasurable (fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    ((continuous_ofReal.comp (continuous_id.pow 2)).aestronglyMeasurable
        (μ := (volume : Measure ℝ))).mono_measure Measure.restrict_le_self
  have hexp : AEStronglyMeasurable (fun t : ℝ => (Real.exp (-π * u * t) : ℂ))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by fun_prop
  simpa [aLaplaceIntegrand, mul_assoc] using (ht2.mul aestronglyMeasurable_phi0''_div_Ioi).mul hexp

/-- Convergence of the Laplace integral defining `a'` (integrability on `(0, ∞)` for `u > 2`). -/
public lemma aLaplaceIntegral_convergent {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioi (0 : ℝ)) := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have hMeasIoi := aestronglyMeasurable_aLaplaceIntegrand_Ioi (u := u)
  have hIoi_split : (Set.Ioi (0 : ℝ)) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
    simp [Set.Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one]
  have hsmall : IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioc (0 : ℝ) 1) := by
    let C₀ : ℝ := MagicFunction.a.Schwartz.I1Decay.Cφ
    refine MeasureTheory.IntegrableOn.of_bound (by simp : (MeasureTheory.volume : Measure ℝ)
      (Set.Ioc (0 : ℝ) 1) < ⊤)
      (hMeasIoi.mono_measure <| Measure.restrict_mono_set (MeasureTheory.volume : Measure ℝ)
        fun t ht => ht.1) C₀ ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => ?_
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hC₀ : 0 ≤ C₀ := MagicFunction.a.Schwartz.I1Decay.Cφ_pos.le
    have hφ₀'' : ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ ≤ C₀ := by
      have hsinv : (1 : ℝ) ≤ t⁻¹ := one_le_inv_iff₀.2 ⟨ht0, ht1⟩
      have hexp : rexp (-2 * π * t⁻¹) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, inv_nonneg.2 (le_of_lt ht0)])
      have hdecay' : ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ ≤ C₀ * rexp (-2 * π * t⁻¹) := by
        simpa [div_eq_mul_inv, Complex.ofReal_inv, C₀] using
          MagicFunction.a.Schwartz.I1Decay.norm_φ₀''_le (s := t⁻¹) hsinv
      exact hdecay'.trans ((mul_le_mul_of_nonneg_left hexp hC₀).trans_eq (by simp))
    have ht2_le : ‖((t ^ (2 : ℕ) : ℝ) : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real] using
        pow_le_one₀ (n := 2) (abs_nonneg t) (by simpa [abs_of_pos ht0] using ht1)
    have hexp_le : ‖(Real.exp (-π * u * t) : ℂ)‖ ≤ 1 := by
      have harg : (-π * u * t) ≤ 0 := by
        have : 0 ≤ π * u * t := by positivity [Real.pi_pos.le, hu0.le, ht0.le]
        linarith
      have hn : ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-π * u * t) := by
        simpa [Complex.ofReal_exp] using Complex.norm_exp (-(π * u * t : ℂ))
      rw [hn]; exact Real.exp_le_one_iff.2 harg
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
    have hmid : IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioc (1 : ℝ) A) := by
      have hcontIoi : ContinuousOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioi (0 : ℝ)) := by
        have ht2 : Continuous fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ) := by fun_prop
        have hexp : Continuous fun t : ℝ => (Real.exp (-π * u * t) : ℂ) := by fun_prop
        simpa [aLaplaceIntegrand, mul_assoc] using
          (ht2.continuousOn.mul continuousOn_phi0''_div_Ioi).mul hexp.continuousOn
      exact ((hcontIoi.mono fun t ht => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
        ht.1).integrableOn_Icc (μ := MeasureTheory.volume)).mono_set Set.Ioc_subset_Icc_self
    have hbig : IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioi A) := by
      let a : ℝ := π * (u - 2)
      have ha : 0 < a := mul_pos Real.pi_pos (sub_pos.2 hu)
      let BA : ℝ := B2 * B4 + B6
      let C2 : ℝ := ‖(12 * Complex.I : ℂ) / (π : ℂ)‖
      let C4 : ℝ := ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))‖
      let Cφ : ℝ := (BA ^ (2 : ℕ) + C2 * (B4 * BA) + C4 * (B4 ^ (2 : ℕ))) * CΔ
      have hMeasA : AEStronglyMeasurable (fun t : ℝ => aLaplaceIntegrand u t)
            (MeasureTheory.volume.restrict (Set.Ioi A)) :=
        hMeasIoi.mono_measure <| Measure.restrict_mono_set (MeasureTheory.volume : Measure ℝ)
          fun t ht => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_trans hA1 (le_of_lt ht))
      have hdomReal : Integrable (fun t : ℝ => Cφ * (t ^ (2 : ℕ) * Real.exp (-a * t)))
            (MeasureTheory.volume.restrict (Set.Ioi A)) :=
        (by simpa [IntegrableOn] using integrableOn_sq_mul_exp_neg A a ha
          : Integrable (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-a * t))
              (MeasureTheory.volume.restrict (Set.Ioi A))).const_mul Cφ
      have hdom :
          ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi A)),
            ‖aLaplaceIntegrand u t‖ ≤ Cφ * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by
        refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
        intro t ht
        have htA : A ≤ t := le_of_lt ht
        have ht1 : (1 : ℝ) ≤ t := le_trans hA1 htA
        have ht0 : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht1
        have hzpos : 0 < (((Complex.I : ℂ) * (t : ℂ)) : ℂ).im := by simpa using ht0
        let zH : ℍ := ⟨(Complex.I : ℂ) * (t : ℂ), hzpos⟩
        have hz_im : zH.im = t := by simp [zH, UpperHalfPlane.im]
        have hAΔ : AΔ ≤ A := by dsimp [A]; exact le_max_of_le_right (le_max_left _ _)
        have hA2 : A2 ≤ A := by
          dsimp [A]; exact le_max_of_le_right <| le_max_of_le_right (le_max_left _ _)
        have hA4 : A4 ≤ A := by
          dsimp [A]; exact le_max_of_le_right <| le_max_of_le_right <|
            le_max_of_le_right (le_max_left _ _)
        have hA6 : A6 ≤ A := by
          dsimp [A]; exact le_max_of_le_right <| le_max_of_le_right <|
            le_max_of_le_right (le_max_right _ _)
        have htAim : A ≤ zH.im := by simpa [hz_im] using htA
        have hE4 : ‖E₄ zH‖ ≤ B4 := hB4 zH (hA4.trans htAim)
        have hΔ : ‖(Δ zH)⁻¹‖ ≤ CΔ * Real.exp (2 * π * t) := by
          simpa [hz_im] using hΔinv zH (hAΔ.trans htAim)
        have hAterm : ‖E₂ zH * E₄ zH - E₆ zH‖ ≤ BA :=
          norm_sub_le_of_le (norm_mul_le_of_le (hB2 zH (hA2.trans htAim)) hE4)
            (hB6 zH (hA6.trans htAim))
        have hBA_nonneg : 0 ≤ BA := le_trans (norm_nonneg _) hAterm
        have hB4_nonneg : 0 ≤ B4 := le_trans (norm_nonneg _) hE4
        have hφ0 : ‖φ₀ zH‖ ≤ (BA ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t)) :=
          calc ‖φ₀ zH‖ = ‖(E₂ zH * E₄ zH - E₆ zH) ^ (2 : ℕ)‖ * ‖(Δ zH)⁻¹‖ := by
                simp [φ₀, div_eq_mul_inv]
            _ ≤ (BA ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t)) := by
                refine mul_le_mul ?_ hΔ (norm_nonneg _) (pow_nonneg hBA_nonneg _)
                simpa [norm_pow, pow_two] using
                  mul_le_mul hAterm hAterm (norm_nonneg _) hBA_nonneg
        have hφ2 : ‖φ₂' zH‖ ≤ (B4 * BA) * (CΔ * Real.exp (2 * π * t)) :=
          calc ‖φ₂' zH‖ = (‖E₄ zH‖ * ‖E₂ zH * E₄ zH - E₆ zH‖) * ‖(Δ zH)⁻¹‖ := by
                simp [φ₂', div_eq_mul_inv, mul_assoc]
            _ ≤ (B4 * BA) * (CΔ * Real.exp (2 * π * t)) :=
                mul_le_mul (mul_le_mul hE4 hAterm (norm_nonneg _) hB4_nonneg) hΔ
                  (norm_nonneg _) (mul_nonneg hB4_nonneg hBA_nonneg)
        have hφ4 : ‖φ₄' zH‖ ≤ (B4 ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t)) :=
          calc ‖φ₄' zH‖ = ‖(E₄ zH) ^ (2 : ℕ)‖ * ‖(Δ zH)⁻¹‖ := by
                simp [φ₄', div_eq_mul_inv]
            _ ≤ (B4 ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t)) := by
                refine mul_le_mul ?_ hΔ (norm_nonneg _) (pow_nonneg hB4_nonneg _)
                simpa [norm_pow, pow_two] using mul_le_mul hE4 hE4 (norm_nonneg _) hB4_nonneg
        have hScoe : ((ModularGroup.S • zH : ℍ) : ℂ) = (Complex.I : ℂ) / (t : ℂ) :=
          (ModularGroup.coe_S_smul (z := zH)).trans (by
            simp [zH, div_eq_mul_inv, mul_inv_rev, mul_comm])
        have hphiS : φ₀'' ((Complex.I : ℂ) / (t : ℂ)) = φ₀ (ModularGroup.S • zH) :=
          (congrArg φ₀'' hScoe.symm).trans (φ₀''_coe_upperHalfPlane (z := ModularGroup.S • zH))
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
          have htri :
              ‖φ₀ (ModularGroup.S • zH)‖ ≤
                ‖φ₀ zH‖ + ‖(12 * Complex.I) / (π * (zH : ℂ)) * φ₂' zH‖ +
                  ‖36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH‖ := by
            have hEq : φ₀ (ModularGroup.S • zH) =
                  φ₀ zH - (12 * Complex.I) / (π * zH) * φ₂' zH
                    - 36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH := by
              simpa using φ₀_S_transform zH
            rw [hEq]
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
          _ = Cφ * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by
                rw [show (t ^ (2 : ℕ)) * (Cφ * Real.exp (2 * π * t)) * Real.exp (-π * u * t) =
                  Cφ * ((t ^ (2 : ℕ)) * (Real.exp (2 * π * t) * Real.exp (-π * u * t))) from by
                    ring, hExpRew]
      simpa [IntegrableOn] using
        MeasureTheory.Integrable.mono' (μ := MeasureTheory.volume.restrict (Set.Ioi A))
          hdomReal hMeasA hdom
    have hIoi1_split : Set.Ioi (1 : ℝ) = Set.Ioc (1 : ℝ) A ∪ Set.Ioi A := by
      simpa using (Set.Ioc_union_Ioi_eq_Ioi (a := (1 : ℝ)) (b := A) hA1).symm
    rw [hIoi1_split]; exact hmid.union hbig
  rw [hIoi_split]; exact hsmall.union htail

end

end MagicFunction.g.CohnElkies.IntegralReps
