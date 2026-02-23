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
import SpherePacking.ForMathlib.Intervals
import SpherePacking.ForMathlib.UpperHalfPlane

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

/-- Combine the exponential weights `exp(2π t)` and `exp(-π u t)` into a single `exp` term. -/
public lemma exp_two_pi_mul_mul_exp_neg_pi_mul (u t : ℝ) :
    Real.exp (2 * π * t) * Real.exp (-π * u * t) = Real.exp (-(π * (u - 2)) * t) := by
  have hsum : 2 * π * t + (-π * u * t) = -(π * (u - 2)) * t := by
    ring_nf
  calc
    Real.exp (2 * π * t) * Real.exp (-π * u * t) = Real.exp (2 * π * t + (-π * u * t)) := by
      simp [Real.exp_add]
    _ = Real.exp (-(π * (u - 2)) * t) := by
      simpa using congrArg Real.exp hsum

/-- The Laplace integrand appearing in the representation of the radial profile `a'`. -/
@[expose] public def aLaplaceIntegrand (u t : ℝ) : ℂ :=
  ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) * Real.exp (-π * u * t)

lemma continuousOn_phi0''_div_Ioi :
    ContinuousOn (fun t : ℝ => φ₀'' ((Complex.I : ℂ) / (t : ℂ))) (Set.Ioi (0 : ℝ)) := by
  -- On `t > 0`, the map `t ↦ I/t` lands in the open upper half-plane, where `φ₀''` is continuous.
  have hcontφ : ContinuousOn (fun z : ℂ => φ₀'' z) {z : ℂ | 0 < z.im} :=
    MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn
  have hcontIdiv : ContinuousOn (fun t : ℝ => (Complex.I : ℂ) / (t : ℂ)) (Set.Ioi (0 : ℝ)) := by
    refine continuousOn_const.div (Complex.continuous_ofReal.continuousOn) ?_
    intro t ht
    exact_mod_cast (ne_of_gt ht)
  have hmaps :
      Set.MapsTo (fun t : ℝ => (Complex.I : ℂ) / (t : ℂ)) (Set.Ioi (0 : ℝ))
        {z : ℂ | 0 < z.im} := by
    intro t ht
    have him : (((Complex.I : ℂ) / (t : ℂ)) : ℂ).im = t⁻¹ := by
      calc
        (((Complex.I : ℂ) / (t : ℂ)) : ℂ).im
            = (((Complex.I : ℂ) * (t : ℂ)⁻¹) : ℂ).im := by simp [div_eq_mul_inv]
        _ = (((Complex.I : ℂ) * ((t⁻¹ : ℝ) : ℂ)) : ℂ).im := by simp [Complex.ofReal_inv]
        _ = t⁻¹ := by simp
    simpa [him] using (inv_pos.2 (by simpa using ht) : 0 < (t⁻¹ : ℝ))
  exact hcontφ.comp hcontIdiv hmaps

lemma aestronglyMeasurable_phi0''_div_Ioi :
    AEStronglyMeasurable (fun t : ℝ => φ₀'' ((Complex.I : ℂ) / (t : ℂ)))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  exact (continuousOn_phi0''_div_Ioi).aestronglyMeasurable measurableSet_Ioi

/-- Integrability of `t^2 * exp(-a * t)` on a ray `Set.Ioi A` (for `0 < a`). -/
public lemma integrableOn_sq_mul_exp_neg (A a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-a * t)) (Set.Ioi A) := by
  -- Use `integrable_of_isBigO_exp_neg` and the fact that polynomials are `o(exp(b*t))` at `∞`.
  have hb : 0 < a / 2 := half_pos ha
  have hcont : ContinuousOn (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-a * t)) (Set.Ici A) := by
    fun_prop
  have hpow :
      (fun t : ℝ => t ^ (2 : ℕ)) =O[atTop] fun t : ℝ => Real.exp ((a / 2) * t) :=
    (isLittleO_pow_exp_pos_mul_atTop (k := 2) hb).isBigO
  have hmul :
      (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-a * t)) =O[atTop]
        fun t : ℝ => Real.exp ((a / 2) * t) * Real.exp (-a * t) :=
    hpow.mul (Asymptotics.isBigO_refl _ _)
  have hmul' :
      (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-a * t)) =O[atTop]
        fun t : ℝ => Real.exp (-(a / 2) * t) := by
    refine hmul.congr_right ?_
    intro t
    have : (a / 2) * t + (-a * t) = (-(a / 2) * t) := by ring_nf
    calc
      Real.exp ((a / 2) * t) * Real.exp (-a * t) = Real.exp ((a / 2) * t + (-a * t)) := by
        simp [Real.exp_add]
      _ = Real.exp (-(a / 2) * t) := by rw [this]
  exact integrable_of_isBigO_exp_neg (a := A) (b := a / 2) hb hcont hmul'

lemma aestronglyMeasurable_aLaplaceIntegrand_Ioi (u : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => aLaplaceIntegrand u t)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have ht2 :
      AEStronglyMeasurable (fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    ((continuous_ofReal.comp (continuous_id.pow 2)).aestronglyMeasurable
        (μ := (volume : Measure ℝ))).mono_measure Measure.restrict_le_self
  have hexp :
      AEStronglyMeasurable (fun t : ℝ => (Real.exp (-π * u * t) : ℂ))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hcont : Continuous fun t : ℝ => (Real.exp (-π * u * t) : ℂ) := by fun_prop
    have hmeas :
        AEStronglyMeasurable (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (MeasureTheory.volume) :=
      hcont.aestronglyMeasurable
    exact hmeas.mono_measure Measure.restrict_le_self
  simpa [aLaplaceIntegrand, mul_assoc] using (ht2.mul aestronglyMeasurable_phi0''_div_Ioi).mul hexp

/-- Convergence of the Laplace integral defining `a'` (integrability on `(0, ∞)` for `u > 2`). -/
public lemma aLaplaceIntegral_convergent {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioi (0 : ℝ)) := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  -- Measurability of the Laplace integrand on `(0, ∞)`.
  have hMeasIoi :
      AEStronglyMeasurable (fun t : ℝ => aLaplaceIntegrand u t)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    aestronglyMeasurable_aLaplaceIntegrand_Ioi (u := u)
  -- Split the integral into `(0,1]` and `(1,∞)`.
  have hIoi_split :
      (Set.Ioi (0 : ℝ)) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
    simp [Set.Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one]
  -- Integrability near `0+` on `(0,1]`.
  have hsmall : IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioc (0 : ℝ) 1) := by
    let C₀ : ℝ := MagicFunction.a.Schwartz.I1Decay.Cφ
    have hs : (MeasureTheory.volume : Measure ℝ) (Set.Ioc (0 : ℝ) 1) < ⊤ := by simp
    have hMeas_small :
        AEStronglyMeasurable (fun t : ℝ => aLaplaceIntegrand u t)
          (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      have hμ :
          (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1) : Measure ℝ) ≤
            MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
        Measure.restrict_mono_set (MeasureTheory.volume : Measure ℝ) (by
          intro t ht
          exact ht.1)
      exact hMeasIoi.mono_measure hμ
    refine MeasureTheory.IntegrableOn.of_bound hs hMeas_small C₀ ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall ?_
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hφ₀'' :
        ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ ≤ C₀ := by
      have hs : (1 : ℝ) ≤ t⁻¹ := (one_le_inv_iff₀.2 ⟨ht0, ht1⟩)
      have hC₀ : 0 ≤ C₀ := by
        simpa [C₀] using (MagicFunction.a.Schwartz.I1Decay.Cφ_pos).le
      have hdecay :
          ‖φ₀'' ((Complex.I : ℂ) * (t⁻¹ : ℂ))‖ ≤ C₀ * rexp (-2 * π * t⁻¹) := by
        simpa [C₀] using (MagicFunction.a.Schwartz.I1Decay.norm_φ₀''_le (s := t⁻¹) hs)
      have hexp : rexp (-2 * π * t⁻¹) ≤ 1 := by
        have : (-2 * π * t⁻¹) ≤ 0 := by
          have htinv : 0 ≤ t⁻¹ := inv_nonneg.2 (le_of_lt ht0)
          nlinarith [Real.pi_pos, htinv]
        simpa using (Real.exp_le_one_iff.2 this)
      have hmul : C₀ * rexp (-2 * π * t⁻¹) ≤ C₀ := by
        exact (mul_le_mul_of_nonneg_left hexp hC₀).trans_eq (by simp)
      have hdecay' : ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ ≤ C₀ * rexp (-2 * π * t⁻¹) := by
        simpa [div_eq_mul_inv, Complex.ofReal_inv] using hdecay
      exact hdecay'.trans hmul
    -- Combine the bounds for the product.
    have ht2_le : ‖((t ^ (2 : ℕ) : ℝ) : ℂ)‖ ≤ 1 := by
      have ht_abs : |t| ≤ 1 := by simpa [abs_of_pos ht0] using ht1
      simpa [Complex.norm_real] using (pow_le_one₀ (n := 2) (abs_nonneg t) ht_abs)
    have hexp_le : ‖(Real.exp (-π * u * t) : ℂ)‖ ≤ 1 := by
      have harg : (-π * u * t) ≤ 0 := by
        have : 0 ≤ π * u * t := by positivity [Real.pi_pos.le, hu0.le, ht0.le]
        have h : (-π * u * t) = -(π * u * t) := by ring
        simpa [h] using (neg_nonpos.2 this)
      have hx : Real.exp (-π * u * t) ≤ 1 := Real.exp_le_one_iff.2 harg
      have hn : ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-π * u * t) := by
        simpa [Complex.ofReal_exp] using (Complex.norm_exp (-(π * u * t : ℂ)))
      rw [hn]
      exact hx
    calc
      ‖aLaplaceIntegrand u t‖
          = ‖((t ^ (2 : ℕ) : ℝ) : ℂ) *
              φ₀'' ((Complex.I : ℂ) / (t : ℂ)) *
                Real.exp (-π * u * t)‖ := by rfl
      _ ≤ ‖((t ^ (2 : ℕ) : ℝ) : ℂ)‖ *
            ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ *
              ‖(Real.exp (-π * u * t) : ℂ)‖ := by
            simp [mul_assoc]
      _ ≤ 1 * C₀ * 1 := by
            have hC₀ : 0 ≤ C₀ := by
              simpa [C₀] using (MagicFunction.a.Schwartz.I1Decay.Cφ_pos).le
            gcongr
      _ = C₀ := by ring
  -- Integrability on `(1,∞)` via an exponential domination.
  have htail : IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioi (1 : ℝ)) := by
    -- Split `(1,∞)` further into `[1,A]` and `(A,∞)`.
    -- Use explicit bounds coming from modular forms.
    have hE2bdd : IsBoundedAtImInfty E₂ := E₂_isBoundedAtImInfty
    have hE4bdd : IsBoundedAtImInfty (fun z : ℍ => E₄ z) := ModularFormClass.bdd_at_infty E₄
    have hE6bdd : IsBoundedAtImInfty (fun z : ℍ => E₆ z) := ModularFormClass.bdd_at_infty E₆
    rcases (UpperHalfPlane.isBoundedAtImInfty_iff).1 hE2bdd with ⟨B2, A2, hB2⟩
    rcases (UpperHalfPlane.isBoundedAtImInfty_iff).1 hE4bdd with ⟨B4, A4, hB4⟩
    rcases (UpperHalfPlane.isBoundedAtImInfty_iff).1 hE6bdd with ⟨B6, A6, hB6⟩
    obtain ⟨CΔ, AΔ, hCΔpos, hΔinv⟩ := exists_inv_Delta_bound_exp
    let A : ℝ := max (1 : ℝ) (max AΔ (max A2 (max A4 A6)))
    have hA1 : (1 : ℝ) ≤ A := by
      dsimp [A]
      exact le_max_left _ _
    -- Integrability on the finite interval `(1,A]` by continuity.
    have hmid : IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioc (1 : ℝ) A) := by
      have hcontIoi : ContinuousOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioi (0 : ℝ)) := by
        have ht2 : Continuous fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ) := by fun_prop
        have hexp : Continuous fun t : ℝ => (Real.exp (-π * u * t) : ℂ) := by fun_prop
        have hmul :
            ContinuousOn
              (fun t : ℝ =>
                ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) *
                  (Real.exp (-π * u * t) : ℂ))
              (Set.Ioi (0 : ℝ)) :=
          (ht2.continuousOn.mul continuousOn_phi0''_div_Ioi).mul hexp.continuousOn
        simpa [aLaplaceIntegrand, mul_assoc] using hmul
      have hcontIcc :
          ContinuousOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Icc (1 : ℝ) A) := by
        refine hcontIoi.mono ?_
        intro t ht
        exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht.1
      have hIcc : IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Icc (1 : ℝ) A) :=
        (hcontIcc.integrableOn_Icc (μ := MeasureTheory.volume))
      exact hIcc.mono_set Set.Ioc_subset_Icc_self
    -- Integrability on `(A,∞)` via domination by `t^2 * exp(-π*(u-2)*t)`.
    have hbig : IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioi A) := by
      -- Positive decay rate.
      let a : ℝ := π * (u - 2)
      have ha : 0 < a := mul_pos Real.pi_pos (sub_pos.2 hu)
      -- Constants controlling the modular-form growth.
      let BA : ℝ := B2 * B4 + B6
      let C2 : ℝ := ‖(12 * Complex.I : ℂ) / (π : ℂ)‖
      let C4 : ℝ := ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))‖
      let Cφ : ℝ := (BA ^ (2 : ℕ) + C2 * (B4 * BA) + C4 * (B4 ^ (2 : ℕ))) * CΔ
      have hMeasA :
          AEStronglyMeasurable (fun t : ℝ => aLaplaceIntegrand u t)
            (MeasureTheory.volume.restrict (Set.Ioi A)) := by
        have hμ :
            (MeasureTheory.volume.restrict (Set.Ioi A) : Measure ℝ) ≤
              MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
          Measure.restrict_mono_set (MeasureTheory.volume : Measure ℝ) (by
            intro t ht
            exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_trans hA1 (le_of_lt ht)))
        exact hMeasIoi.mono_measure hμ
      have hdomReal :
          Integrable (fun t : ℝ => Cφ * (t ^ (2 : ℕ) * Real.exp (-a * t)))
            (MeasureTheory.volume.restrict (Set.Ioi A)) := by
        have hbase :
            IntegrableOn (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-a * t)) (Set.Ioi A) :=
          integrableOn_sq_mul_exp_neg A a ha
        have hbase' :
            Integrable (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-a * t))
              (MeasureTheory.volume.restrict (Set.Ioi A)) := by
          simpa [IntegrableOn] using hbase
        exact hbase'.const_mul Cφ
      have hdom :
          ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi A)),
            ‖aLaplaceIntegrand u t‖ ≤ Cφ * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by
        refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
        intro t ht
        have htA : A ≤ t := le_of_lt ht
        have ht1 : (1 : ℝ) ≤ t := le_trans hA1 htA
        have ht0 : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht1
        have ht0' : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht0)
        -- `zH = i*t` in `ℍ`, so `zH.im = t`.
        have hzpos : 0 < (((Complex.I : ℂ) * (t : ℂ)) : ℂ).im := by simpa using ht0
        let zH : ℍ := ⟨(Complex.I : ℂ) * (t : ℂ), hzpos⟩
        have hz_im : zH.im = t := by simp [zH, UpperHalfPlane.im]
        -- `A` dominates all thresholds needed for bounds at `Im → ∞`.
        have hAΔ : AΔ ≤ A := by
          dsimp [A]
          exact le_trans (le_max_left AΔ (max A2 (max A4 A6))) (le_max_right (1 : ℝ) _)
        have hA2 : A2 ≤ A := by
          dsimp [A]
          exact le_trans (le_max_left A2 (max A4 A6)) <|
            le_trans (le_max_right AΔ (max A2 (max A4 A6))) (le_max_right (1 : ℝ) _)
        have hA4 : A4 ≤ A := by
          dsimp [A]
          exact le_trans (le_max_left A4 A6) <|
            le_trans (le_max_right A2 (max A4 A6)) <|
              le_trans (le_max_right AΔ (max A2 (max A4 A6))) (le_max_right (1 : ℝ) _)
        have hA6 : A6 ≤ A := by
          dsimp [A]
          exact le_trans (le_max_right A4 A6) <|
            le_trans (le_max_right A2 (max A4 A6)) <|
              le_trans (le_max_right AΔ (max A2 (max A4 A6))) (le_max_right (1 : ℝ) _)
        have hzAΔ : AΔ ≤ zH.im := le_trans hAΔ (by simpa [hz_im] using htA)
        have hzA2 : A2 ≤ zH.im := le_trans hA2 (by simpa [hz_im] using htA)
        have hzA4 : A4 ≤ zH.im := le_trans hA4 (by simpa [hz_im] using htA)
        have hzA6 : A6 ≤ zH.im := le_trans hA6 (by simpa [hz_im] using htA)
        have hE2 : ‖E₂ zH‖ ≤ B2 := hB2 zH hzA2
        have hE4 : ‖E₄ zH‖ ≤ B4 := hB4 zH hzA4
        have hE6 : ‖E₆ zH‖ ≤ B6 := hB6 zH hzA6
        have hΔ : ‖(Δ zH)⁻¹‖ ≤ CΔ * Real.exp (2 * π * t) := by
          simpa [hz_im] using hΔinv zH hzAΔ
        have hAterm : ‖E₂ zH * E₄ zH - E₆ zH‖ ≤ BA := by
          have hsub : ‖E₂ zH * E₄ zH - E₆ zH‖ ≤ ‖E₂ zH * E₄ zH‖ + ‖E₆ zH‖ := by
            simpa using norm_sub_le (E₂ zH * E₄ zH) (E₆ zH)
          have hmul : ‖E₂ zH * E₄ zH‖ ≤ B2 * B4 := by
            have hB2_nonneg : 0 ≤ B2 := le_trans (norm_nonneg (E₂ zH)) hE2
            have hmul' := mul_le_mul hE2 hE4 (norm_nonneg (E₄ zH)) hB2_nonneg
            simpa [norm_mul] using hmul'
          have hadd : ‖E₂ zH * E₄ zH‖ + ‖E₆ zH‖ ≤ BA := by
            simpa [BA] using add_le_add hmul hE6
          exact le_trans hsub hadd
        have hφ0 : ‖φ₀ zH‖ ≤ (BA ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t)) := by
          have hBA_nonneg : 0 ≤ BA :=
            le_trans (norm_nonneg (E₂ zH * E₄ zH - E₆ zH)) hAterm
          have hpow' : ‖E₂ zH * E₄ zH - E₆ zH‖ ^ (2 : ℕ) ≤ BA ^ (2 : ℕ) := by
            have hmul :=
              mul_le_mul hAterm hAterm (norm_nonneg (E₂ zH * E₄ zH - E₆ zH)) hBA_nonneg
            simpa [pow_two] using hmul
          have hpow : ‖(E₂ zH * E₄ zH - E₆ zH) ^ (2 : ℕ)‖ ≤ BA ^ (2 : ℕ) := by
            simpa [norm_pow] using hpow'
          have hmulAll :
              ‖(E₂ zH * E₄ zH - E₆ zH) ^ (2 : ℕ)‖ * ‖(Δ zH)⁻¹‖ ≤
                (BA ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t)) := by
            exact mul_le_mul hpow hΔ (norm_nonneg _) (pow_nonneg hBA_nonneg _)
          calc
            ‖φ₀ zH‖ =
                ‖((E₂ zH * E₄ zH - E₆ zH) ^ (2 : ℕ)) * (Δ zH)⁻¹‖ := by
              simp [φ₀, div_eq_mul_inv]
            _ =
                ‖(E₂ zH * E₄ zH - E₆ zH) ^ (2 : ℕ)‖ * ‖(Δ zH)⁻¹‖ := by
              simp
            _ ≤ (BA ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t)) := hmulAll
        have hφ2 : ‖φ₂' zH‖ ≤ (B4 * BA) * (CΔ * Real.exp (2 * π * t)) := by
          have hB4_nonneg : 0 ≤ B4 := le_trans (norm_nonneg (E₄ zH)) hE4
          have hBA_nonneg : 0 ≤ BA :=
            le_trans (norm_nonneg (E₂ zH * E₄ zH - E₆ zH)) hAterm
          have hB4BA_nonneg : 0 ≤ B4 * BA := mul_nonneg hB4_nonneg hBA_nonneg
          have hmulEA :
              ‖E₄ zH‖ * ‖E₂ zH * E₄ zH - E₆ zH‖ ≤ B4 * BA := by
            exact mul_le_mul hE4 hAterm (norm_nonneg _) hB4_nonneg
          have hmulAll :
              (‖E₄ zH‖ * ‖E₂ zH * E₄ zH - E₆ zH‖) * ‖(Δ zH)⁻¹‖ ≤
                (B4 * BA) * (CΔ * Real.exp (2 * π * t)) := by
            exact mul_le_mul hmulEA hΔ (norm_nonneg _) hB4BA_nonneg
          calc
            ‖φ₂' zH‖ = ‖E₄ zH * (E₂ zH * E₄ zH - E₆ zH) * (Δ zH)⁻¹‖ := by
              simp [φ₂', div_eq_mul_inv, mul_assoc]
            _ = (‖E₄ zH‖ * ‖E₂ zH * E₄ zH - E₆ zH‖) * ‖(Δ zH)⁻¹‖ := by
              simp [mul_assoc]
            _ ≤ (B4 * BA) * (CΔ * Real.exp (2 * π * t)) := by
              simpa [mul_assoc] using hmulAll
        have hφ4 : ‖φ₄' zH‖ ≤ (B4 ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t)) := by
          have hB4_nonneg : 0 ≤ B4 := le_trans (norm_nonneg (E₄ zH)) hE4
          have hpow' : ‖E₄ zH‖ ^ (2 : ℕ) ≤ B4 ^ (2 : ℕ) := by
            have hmul := mul_le_mul hE4 hE4 (norm_nonneg (E₄ zH)) hB4_nonneg
            simpa [pow_two] using hmul
          have hpow : ‖(E₄ zH) ^ (2 : ℕ)‖ ≤ B4 ^ (2 : ℕ) := by
            simpa [norm_pow] using hpow'
          have hmulAll :
              ‖(E₄ zH) ^ (2 : ℕ)‖ * ‖(Δ zH)⁻¹‖ ≤
                (B4 ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t)) := by
            exact mul_le_mul hpow hΔ (norm_nonneg _) (pow_nonneg hB4_nonneg _)
          calc
            ‖φ₄' zH‖ = ‖(E₄ zH) ^ (2 : ℕ) * (Δ zH)⁻¹‖ := by
              simp [φ₄', div_eq_mul_inv]
            _ = ‖(E₄ zH) ^ (2 : ℕ)‖ * ‖(Δ zH)⁻¹‖ := by
              simp
            _ ≤ (B4 ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t)) := hmulAll
        -- Rewrite `φ₀'' (i/t)` as `φ₀ (S•zH)`.
        have hScoe : ((ModularGroup.S • zH : ℍ) : ℂ) = (Complex.I : ℂ) / (t : ℂ) := by
          calc
            ((ModularGroup.S • zH : ℍ) : ℂ) = (-1 : ℂ) / (zH : ℂ) :=
              ModularGroup.coe_S_smul (z := zH)
            _ = (Complex.I : ℂ) / (t : ℂ) := by
              simp [zH, div_eq_mul_inv, mul_inv_rev, mul_comm]
        have hphiS : φ₀'' ((Complex.I : ℂ) / (t : ℂ)) = φ₀ (ModularGroup.S • zH) := by
          have harg :
              φ₀'' ((Complex.I : ℂ) / (t : ℂ)) = φ₀'' ((ModularGroup.S • zH : ℍ) : ℂ) :=
            congrArg φ₀'' hScoe.symm
          exact harg.trans (φ₀''_coe_upperHalfPlane (z := ModularGroup.S • zH))
        have hz_norm : ‖(zH : ℂ)‖ = t := by simp [zH, abs_of_pos ht0]
        have hz_inv : ‖(zH : ℂ)⁻¹‖ ≤ 1 := by
          have : ‖(zH : ℂ)‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by simpa [hz_norm] using ht1)
          simpa [norm_inv] using this
        have hz2_inv : ‖((zH : ℂ) ^ (2 : ℕ))⁻¹‖ ≤ 1 := by
          have hz2 : (1 : ℝ) ≤ ‖(zH : ℂ) ^ (2 : ℕ)‖ := by
            have : (1 : ℝ) ≤ t ^ (2 : ℕ) := (one_le_pow₀ ht1 : (1 : ℝ) ≤ t ^ (2 : ℕ))
            simpa [norm_pow, hz_norm] using this
          simpa [norm_inv] using (inv_le_one_of_one_le₀ hz2)
        have hcoeff2 :
            ‖(12 * Complex.I : ℂ) / (π * (zH : ℂ))‖ ≤ C2 := by
          have hrew :
              (12 * Complex.I : ℂ) / (π * (zH : ℂ)) =
                ((12 * Complex.I : ℂ) / (π : ℂ)) * (zH : ℂ)⁻¹ := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, mul_inv_rev]
          calc
            ‖(12 * Complex.I : ℂ) / (π * (zH : ℂ))‖
                = ‖((12 * Complex.I : ℂ) / (π : ℂ)) * (zH : ℂ)⁻¹‖ := by simp [hrew]
            _ = ‖(12 * Complex.I : ℂ) / (π : ℂ)‖ * ‖(zH : ℂ)⁻¹‖ := by simp
            _ ≤ C2 * 1 := by gcongr
            _ = C2 := by simp
        have hcoeff4 :
            ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ))‖ ≤ C4 := by
          have hrew :
              (36 : ℂ) / ((π : ℂ) ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) =
                ((36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * ((zH : ℂ) ^ (2 : ℕ))⁻¹ := by
            simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_inv_rev]
          calc
            ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ))‖
                = ‖((36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * ((zH : ℂ) ^ (2 : ℕ))⁻¹‖ := by simp [hrew]
            _ = ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))‖ * ‖((zH : ℂ) ^ (2 : ℕ))⁻¹‖ := by
                  simp
            _ ≤ C4 * 1 := by gcongr
            _ = C4 := by simp
        -- Bound `‖φ₀'' (i/t)‖` by `Cφ * exp(2π t)`.
        have hphi_bound : ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ ≤ Cφ * Real.exp (2 * π * t) := by
          have htri :
              ‖φ₀ (ModularGroup.S • zH)‖ ≤
                ‖φ₀ zH‖ + ‖(12 * Complex.I) / (π * (zH : ℂ)) * φ₂' zH‖ +
                  ‖36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH‖ := by
            have hEq :
                φ₀ (ModularGroup.S • zH) =
                  φ₀ zH - (12 * Complex.I) / (π * zH) * φ₂' zH
                    - 36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH := by
              simpa using φ₀_S_transform zH
            calc
              ‖φ₀ (ModularGroup.S • zH)‖ =
                  ‖φ₀ zH - (12 * Complex.I) / (π * zH) * φ₂' zH
                      - 36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH‖ := by
                        rw [hEq]
              _ ≤ ‖φ₀ zH - (12 * Complex.I) / (π * zH) * φ₂' zH‖ +
                    ‖36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH‖ := by
                      simpa [sub_eq_add_neg, add_assoc] using
                        (norm_add_le
                          (φ₀ zH - (12 * Complex.I) / (π * zH) * φ₂' zH)
                          (-(36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH)))
              _ ≤ ‖φ₀ zH‖ + ‖(12 * Complex.I) / (π * zH) * φ₂' zH‖ +
                    ‖36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH‖ := by
                      have hsub :
                          ‖φ₀ zH - (12 * Complex.I) / (π * zH) * φ₂' zH‖ ≤
                            ‖φ₀ zH‖ + ‖(12 * Complex.I) / (π * zH) * φ₂' zH‖ :=
                        norm_sub_le (φ₀ zH) ((12 * Complex.I) / (π * zH) * φ₂' zH)
                      have hsub' :
                          ‖φ₀ zH - (12 * Complex.I) / (π * zH) * φ₂' zH‖ +
                              ‖36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH‖ ≤
                            (‖φ₀ zH‖ + ‖(12 * Complex.I) / (π * zH) * φ₂' zH‖) +
                              ‖36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH‖ :=
                        add_le_add_left hsub
                          ‖36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH‖
                      calc
                        ‖φ₀ zH - (12 * Complex.I) / (π * zH) * φ₂' zH‖ +
                            ‖36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH‖
                            ≤
                            (‖φ₀ zH‖ + ‖(12 * Complex.I) / (π * zH) * φ₂' zH‖) +
                              ‖36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH‖ := hsub'
                        _ = ‖φ₀ zH‖ + ‖(12 * Complex.I) / (π * zH) * φ₂' zH‖ +
                              ‖36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH‖ := by
                              simp [add_assoc]
          have h2 :
              ‖(12 * Complex.I) / (π * (zH : ℂ)) * φ₂' zH‖ ≤
                C2 * ((B4 * BA) * (CΔ * Real.exp (2 * π * t))) := by
            calc
              ‖(12 * Complex.I) / (π * (zH : ℂ)) * φ₂' zH‖ =
                  ‖(12 * Complex.I : ℂ) / (π * (zH : ℂ))‖ * ‖φ₂' zH‖ := by
                simp
              _ ≤ C2 * ((B4 * BA) * (CΔ * Real.exp (2 * π * t))) := by
                gcongr
          have h4 :
              ‖36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH‖ ≤
                C4 * ((B4 ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t))) := by
            calc
              ‖36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH‖ =
                  ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ))‖ * ‖φ₄' zH‖ := by
                simp
              _ ≤ C4 * ((B4 ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t))) := by
                gcongr
          have hmain :
              ‖φ₀ (ModularGroup.S • zH)‖ ≤
                (BA ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t)) +
                  C2 * ((B4 * BA) * (CΔ * Real.exp (2 * π * t))) +
                    C4 * ((B4 ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t))) := by
            have hAB :
                ‖φ₀ zH‖ + ‖(12 * Complex.I) / (π * (zH : ℂ)) * φ₂' zH‖ ≤
                  (BA ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t)) +
                    C2 * ((B4 * BA) * (CΔ * Real.exp (2 * π * t))) :=
              add_le_add hφ0 h2
            have hABC :
                ‖φ₀ zH‖ + ‖(12 * Complex.I) / (π * (zH : ℂ)) * φ₂' zH‖ +
                      ‖36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH‖ ≤
                    (BA ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t)) +
                      C2 * ((B4 * BA) * (CΔ * Real.exp (2 * π * t))) +
                        C4 * ((B4 ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t))) := by
              simpa [add_assoc] using add_le_add hAB h4
            exact le_trans htri hABC
          have : ‖φ₀ (ModularGroup.S • zH)‖ ≤ Cφ * Real.exp (2 * π * t) := by
            -- Factor out `CΔ * exp(2πt)` and use the definition of `Cφ`.
            let X : ℝ := CΔ * Real.exp (2 * π * t)
            have hmain' :
                ‖φ₀ (ModularGroup.S • zH)‖ ≤
                  (BA ^ (2 : ℕ)) * X + C2 * ((B4 * BA) * X) + C4 * ((B4 ^ (2 : ℕ)) * X) := by
              simpa [X, mul_assoc] using hmain
            have hx :
                (BA ^ (2 : ℕ)) * X + C2 * ((B4 * BA) * X) + C4 * ((B4 ^ (2 : ℕ)) * X) =
                  (BA ^ (2 : ℕ) + C2 * (B4 * BA) + C4 * (B4 ^ (2 : ℕ))) * X := by
              ring
            have hmain'' :
                ‖φ₀ (ModularGroup.S • zH)‖ ≤
                  (BA ^ (2 : ℕ) + C2 * (B4 * BA) + C4 * (B4 ^ (2 : ℕ))) * X := by
              simpa [hx] using hmain'
            simpa [Cφ, X, mul_assoc] using hmain''
          simpa [hphiS] using this
        have hExpNorm : ‖Complex.exp (-(π * u * t : ℂ))‖ = Real.exp (-π * u * t) := by
          simpa [mul_assoc, neg_mul] using (Complex.norm_exp (-(π * u * t : ℂ)))
        have ht2_norm : ‖((t ^ (2 : ℕ) : ℝ) : ℂ)‖ = t ^ (2 : ℕ) := by
          simp [Complex.norm_real]
        have hExpRew :
            Real.exp (2 * π * t) * Real.exp (-π * u * t) = Real.exp (-a * t) := by
          simpa [a, mul_assoc, mul_left_comm, mul_comm] using
            (exp_two_pi_mul_mul_exp_neg_pi_mul (u := u) (t := t))
        have hpoint :
            ‖aLaplaceIntegrand u t‖ ≤ Cφ * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by
          calc
            ‖aLaplaceIntegrand u t‖
                = ‖((t ^ (2 : ℕ) : ℝ) : ℂ) *
                    φ₀'' ((Complex.I : ℂ) / (t : ℂ)) *
                      (Real.exp (-π * u * t) : ℂ)‖ := by rfl
            _ ≤ ‖((t ^ (2 : ℕ) : ℝ) : ℂ)‖ *
                  ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ *
                    ‖(Real.exp (-π * u * t) : ℂ)‖ := by
              simp [mul_assoc]
            _ ≤ (t ^ (2 : ℕ)) * (Cφ * Real.exp (2 * π * t)) * Real.exp (-π * u * t) := by
                  -- Substitute the norm equalities and apply the `φ₀''` bound.
                  have ht2_nonneg : 0 ≤ t ^ (2 : ℕ) := by positivity
                  have hexp_nonneg : 0 ≤ Real.exp (-π * u * t) := (Real.exp_pos _).le
                  have h1 := mul_le_mul_of_nonneg_left hphi_bound ht2_nonneg
                  have h2 := mul_le_mul_of_nonneg_right h1 hexp_nonneg
                  have hExpNorm' : ‖cexp (-(↑π * (↑u * ↑t)))‖ = Real.exp (-π * u * t) := by
                    simpa [mul_assoc] using hExpNorm
                  simpa [mul_assoc, ht2_norm, hExpNorm'] using h2
            _ = Cφ * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by
                  have hrearr :
                      (t ^ (2 : ℕ)) * (Cφ * Real.exp (2 * π * t)) * Real.exp (-π * u * t) =
                        Cφ * ((t ^ (2 : ℕ)) * (Real.exp (2 * π * t) * Real.exp (-π * u * t))) := by
                    ring
                  calc
                    (t ^ (2 : ℕ)) * (Cφ * Real.exp (2 * π * t)) * Real.exp (-π * u * t) =
                        Cφ *
                          ((t ^ (2 : ℕ)) *
                            (Real.exp (2 * π * t) * Real.exp (-π * u * t))) := by
                      simpa using hrearr
                    _ = Cφ * ((t ^ (2 : ℕ)) * Real.exp (-a * t)) := by
                      exact congrArg (fun x : ℝ => Cφ * ((t ^ (2 : ℕ)) * x)) hExpRew
                    _ = Cφ * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by
                      simp
        exact hpoint
      have hint :
          Integrable (fun t : ℝ => aLaplaceIntegrand u t)
            (MeasureTheory.volume.restrict (Set.Ioi A)) :=
        MeasureTheory.Integrable.mono' (μ := MeasureTheory.volume.restrict (Set.Ioi A))
          hdomReal hMeasA hdom
      simpa [IntegrableOn] using hint
    -- Combine `(1,A]` and `(A,∞)`.
    have hIoi1_split : Set.Ioi (1 : ℝ) = Set.Ioc (1 : ℝ) A ∪ Set.Ioi A := by
      simpa using (SpherePacking.ForMathlib.Ioi_eq_Ioc_union_Ioi (a := (1 : ℝ)) (b := A) hA1)
    have hIoi1 : IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioi (1 : ℝ)) :=
      by
        rw [hIoi1_split]
        exact hmid.union hbig
    -- `htail` follows by rewriting `Set.Ioi 1` as the above union.
    simpa [hIoi1_split] using hIoi1
  -- Put everything together on `(0,∞)`.
  rw [hIoi_split]
  exact hsmall.union htail

end

end MagicFunction.g.CohnElkies.IntegralReps
