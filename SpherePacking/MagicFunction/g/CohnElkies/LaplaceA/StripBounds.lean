module
public import SpherePacking.MagicFunction.g.CohnElkies.Defs
public import SpherePacking.MagicFunction.g.CohnElkies.LaplaceLemmas
public import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.Schwartz.DecayI1
public import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
public import SpherePacking.MagicFunction.g.CohnElkies.DeltaBounds
public import SpherePacking.ModularForms.PhiTransform
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.Exponential
import SpherePacking.ForMathlib.ModularFormsHelpers
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import SpherePacking.MagicFunction.a.SpecialValues
import SpherePacking.ForMathlib.ExpPiIMulMulI
import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
import SpherePacking.ModularForms.PhiTransformLemmas

/-!
# Laplace integral for `a'` and strip bounds for the contour deformation

Defines `aLaplaceIntegrand`, proves measurability/integrability lemmas for blueprint
proposition `prop:a-double-zeros`, plus the finite-difference identities for `Φ₁'`, `Φ₃'`,
`Φ₅'` on the imaginary axis and strip bounds used by `LaplaceRepresentation`.
-/

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
