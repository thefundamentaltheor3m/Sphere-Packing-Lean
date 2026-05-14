/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

module

public import SpherePacking.ForMathlib.RadialSchwartz.OneSided
public import SpherePacking.MagicFunction.a.Basic
public import SpherePacking.Integration.Measure

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.MagicFunction.a.IntegralEstimates.I2
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Schwartz property for the magic function `a` via smooth cutoff of radial profiles.

Also includes the `I₃` integrand bounds and the Schwartz decay estimate for `RealIntegrals.I₁'`
(inverse-power decay via the change-of-variables representation
`IntegralEstimates.I₁.Complete_Change_of_Variables`), originally in `Schwartz.DecayI1`. -/

namespace MagicFunction.a.IntegralEstimates.I₃

open scoped Function UpperHalfPlane Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral

noncomputable section

variable (r : ℝ)

/-- The integrand on `Ici 1` obtained from `I₃'` after an inversion change of variables. -/
@[expose] public def g : ℝ → ℝ → ℂ := fun r s ↦ -I
  * φ₀'' (I * s) * (s ^ (-4 : ℤ)) * cexp (π * I * r) * cexp (-π * r / s)

/-- Algebraic identity relating the `I₃'` integrand under the inversion `t ↦ 1 / t`. -/
public lemma inv_integrand_eq_integrand {t : ℝ} (ht₀ : 0 < t) (r : ℝ) (phase : ℂ) :
    (-I : ℂ) * φ₀'' (-1 / (I * t)) * t ^ 2 * phase * cexp (-π * r * t) =
      |(-1 / t ^ 2)| •
        ((-I : ℂ) * φ₀'' (I * (1 / t)) * (1 / t) ^ (-4 : ℤ) * phase * cexp (-π * r / (1 / t))) := by
  simp only [Int.reduceNeg, zpow_neg, real_smul]
  rw [show |-1 / t ^ 2| = 1 / t ^ 2 by simp [neg_div],
    show -1 / (I * t) = I / t by rw [div_mul_eq_div_div_swap, div_I]; ring]
  simp only [neg_mul, ofReal_div, ofReal_one, ofReal_pow, mul_div_assoc', mul_one, div_zpow,
    one_zpow, inv_div, div_one, div_div_eq_mul_div, mul_neg, div_mul_eq_mul_div, one_mul, neg_div']
  rw [eq_div_iff (pow_ne_zero 2 (mod_cast ht₀.ne')), neg_mul, neg_inj]
  ring_nf; ac_rfl

/-- Pointwise bound on `‖g r s‖` on `Ici 1` in terms of `‖φ₀'' (I * s)‖`. -/
public lemma I₃'_bounding_aux_1 (r : ℝ) :
    ∀ x ∈ Ici 1, ‖g r x‖ ≤ ‖φ₀'' (I * ↑x)‖ * rexp (-π * r / x) := by
  intro s hs
  simp only [g, neg_mul, Int.reduceNeg, zpow_neg, norm_neg, norm_mul, norm_I, one_mul, norm_inv,
    norm_zpow, norm_real, norm_eq_abs, norm_exp, neg_re, mul_re, ofReal_re, I_re, mul_zero,
    ofReal_im, I_im, mul_one, zero_mul, mul_im, add_zero, Real.exp_zero, div_ofReal_re, sub_zero]
  conv_rhs => rw [← mul_one ‖φ₀'' (I * ↑s)‖]
  gcongr
  have hs1 : (1 : ℝ) ≤ s := hs
  simpa [abs_of_nonneg (zero_le_one.trans hs1)] using
    inv_le_one_of_one_le₀ (one_le_zpow₀ hs1 <| Int.zero_le_ofNat 4)

/-- The model bound integrand is integrable on `Ici 1`. -/
public lemma Bound_integrableOn (r C₀ : ℝ) :
    IntegrableOn (fun s ↦ C₀ * rexp (-2 * π * s) * rexp (-π * r / s)) (Ici 1) volume := by
  set μ := volume.restrict (Ici (1 : ℝ))
  have h_g : Integrable (fun s ↦ C₀ * rexp (-2 * π * s)) μ :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_exp_mul_Ioi (by linarith [pi_pos]) 1)).const_mul C₀
  have hφ : AEStronglyMeasurable (fun s ↦ rexp (-π * r / s)) μ := by fun_prop
  have hb : ∀ᵐ s ∂μ, ‖rexp (-π * r / s)‖ ≤ rexp (π * |r|) :=
    (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s (hs : 1 ≤ s) ↦ by
      simp only [Real.norm_eq_abs, abs_of_nonneg (exp_pos _).le]
      refine exp_le_exp.mpr <| (le_abs_self _).trans ?_
      rw [abs_div, abs_mul, abs_neg, abs_of_nonneg pi_pos.le, abs_of_nonneg (zero_le_one.trans hs)]
      exact div_le_self (by positivity) hs
  simpa [IntegrableOn, μ, mul_assoc] using h_g.mul_bdd hφ hb

end

end MagicFunction.a.IntegralEstimates.I₃

namespace MagicFunction.a.IntegralEstimates.I₁

noncomputable section

open scoped Function UpperHalfPlane Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral

variable (r : ℝ)

/-- The integrand on `Ici 1` obtained from `I₁'` after an inversion change of variables. -/
@[expose] public def g : ℝ → ℝ → ℂ := fun r s ↦
  -I * φ₀'' (I * s) * (s ^ (-4 : ℤ)) * cexp (-π * I * r) * cexp (-π * r / s)

lemma Reconciling_Change_of_Variables (r : ℝ) :
    I₁' r = ∫ t in Ioc 0 1, |(-1 / t ^ 2)| • (g r (1 / t)) := by
  simp only [I₁'_eq_Ioc, g]
  refine setIntegral_congr_ae₀ nullMeasurableSet_Ioc (ae_of_all _ fun t ht => ?_)
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (MagicFunction.a.IntegralEstimates.I₃.inv_integrand_eq_integrand (t := t) ht.1 r
      (cexp (-π * I * r)))

/-- Rewrite `I₁' r` as an integral of `g r` over `Ici 1`. -/
public theorem Complete_Change_of_Variables (r : ℝ) :
    I₁' r = ∫ s in Ici (1 : ℝ), (g r s) :=
  (Reconciling_Change_of_Variables (r := r)).trans <| by
    simpa using
      (SpherePacking.Integration.InvChangeOfVariables.integral_Ici_one_eq_integral_abs_deriv_smul
        (g := g r)).symm

end

end MagicFunction.a.IntegralEstimates.I₁

namespace MagicFunction.a.Schwartz.I1Decay

noncomputable section

open scoped Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter
open SpherePacking.Integration (μIciOne)

open MagicFunction.a.RealIntegrals
open MagicFunction.a.IntegralEstimates.I₁

def μ : Measure ℝ := μIciOne

def coeff (s : ℝ) : ℂ := (-π : ℂ) * (I + (1 / (s : ℂ)))

def gN (n : ℕ) (r s : ℝ) : ℂ := (coeff s) ^ n * g r s

/-- Constant bounding `‖φ₀ z‖` for `im z ≥ 1 / 2`, from `PolyFourierCoeffBound.norm_φ₀_le`. -/
public noncomputable def Cφ : ℝ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le.choose

public lemma Cφ_pos : 0 < Cφ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le.choose_spec.1

/-- Bound `‖φ₀'' (I * s)‖` for `s ≥ 1`. -/
public lemma norm_φ₀''_le (s : ℝ) (hs : 1 ≤ s) :
    ‖φ₀'' (I * (s : ℂ))‖ ≤ Cφ * rexp (-2 * π * s) := by
  have hpos : 0 < (I * (s : ℂ)).im := by simpa using lt_of_lt_of_le (by norm_num) hs
  let z : ℍ := ⟨I * (s : ℂ), hpos⟩
  have hz_im : z.im = s := by simp [z, UpperHalfPlane.im]
  simpa [Cφ, hz_im, show φ₀'' (I * (s : ℂ)) = φ₀ z by simpa [z] using φ₀''_def hpos] using
    (MagicFunction.PolyFourierCoeffBound.norm_φ₀_le).choose_spec.2 z
      (hz_im ▸ lt_of_lt_of_le (by norm_num : (1/2 : ℝ) < 1) hs)

lemma g_norm_bound (r s : ℝ) (hs : s ∈ Ici (1 : ℝ)) :
    ‖g r s‖ ≤ Cφ * rexp (-2 * π * s) * rexp (-π * r / s) := by
  have hnorm : ‖MagicFunction.a.IntegralEstimates.I₃.g r s‖ = ‖g r s‖ := by
    let A : ℂ := (-I) * φ₀'' (I * s) * (s ^ (-4 : ℤ)) * cexp (-π * r / s)
    simp [show ‖cexp (π * I * r)‖ = (1 : ℝ) by
        simpa [mul_assoc, mul_left_comm, mul_comm] using norm_exp_ofReal_mul_I (π * r),
      show ‖cexp (-(π * I * r))‖ = (1 : ℝ) by
        simpa [mul_assoc, mul_left_comm, mul_comm] using norm_exp_ofReal_mul_I (-π * r),
      show MagicFunction.a.IntegralEstimates.I₃.g r s = A * cexp (π * I * r) by
        simp [MagicFunction.a.IntegralEstimates.I₃.g, A, mul_assoc, mul_left_comm, mul_comm],
      show g r s = A * cexp (-π * I * r) by simp [g, A, mul_assoc, mul_left_comm, mul_comm]]
  refine ((by simpa [hnorm] using
    MagicFunction.a.IntegralEstimates.I₃.I₃'_bounding_aux_1 (r := r) s hs :
    ‖g r s‖ ≤ ‖φ₀'' (I * (s : ℂ))‖ * rexp (-π * r / s))).trans ?_
  gcongr; exact norm_φ₀''_le (s := s) hs

lemma coeff_norm_le (s : ℝ) (hs : s ∈ Ici (1 : ℝ)) : ‖coeff s‖ ≤ 2 * π := by
  have hs1 : (1 : ℝ) ≤ s := hs
  calc ‖coeff s‖ ≤ (π : ℝ) * (‖I‖ + ‖(1 / (s : ℂ))‖) := by
        rw [coeff, norm_mul, show ‖(-π : ℂ)‖ = (π : ℝ) by
          simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le]]
        gcongr; exact norm_add_le _ _
    _ ≤ (π : ℝ) * (1 + 1) := by
        gcongr <;> [simp; simpa [one_div, Complex.norm_real] using inv_le_one_of_one_le₀
          (by simpa [abs_of_nonneg (zero_le_one.trans hs1)] using hs1)]
    _ = 2 * π := by ring

lemma gN_norm_bound (n : ℕ) (r s : ℝ) (hs : s ∈ Ici (1 : ℝ)) :
    ‖gN n r s‖ ≤ (2 * π) ^ n * (Cφ * rexp (-2 * π * s) * rexp (-π * r / s)) := by
  simpa [gN, norm_pow, mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (coeff_norm_le (s := s) hs) n)
      (g_norm_bound (r := r) (s := s) hs) (norm_nonneg _) (by positivity)

/-- Continuity of `s ↦ φ₀'' (I * s)` on `Ici 1`. -/
public lemma φ₀''_I_mul_continuousOn :
    ContinuousOn (fun s : ℝ ↦ φ₀'' (I * (s : ℂ))) (Ici (1 : ℝ)) :=
  (continuousOn_const.mul
    (MagicFunction.a.RealIntegrands.Φ₆_contDiffOn (r := (0 : ℝ))).continuousOn :
    ContinuousOn (fun s : ℝ ↦ (-I) * MagicFunction.a.RealIntegrands.Φ₆ (r := (0 : ℝ)) s)
      (Ici (1 : ℝ))).congr fun s hs => by
    simp [MagicFunction.a.ComplexIntegrands.Φ₆',
      MagicFunction.Parametrisations.z₆'_eq_of_mem hs, ← mul_assoc, mul_comm]

/-- Continuity of `s ↦ (s : ℂ) ^ (-4 : ℤ)` on `Ici 1`. -/
public lemma zpow_neg_four_continuousOn :
    ContinuousOn (fun s : ℝ ↦ (s : ℂ) ^ (-4 : ℤ)) (Ici (1 : ℝ)) :=
  Complex.continuous_ofReal.continuousOn.zpow₀ (-4 : ℤ) fun s hs =>
    Or.inl (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hs).ne')

lemma gN_measurable (n : ℕ) (r : ℝ) : AEStronglyMeasurable (gN n r) μ := by
  have hinv : ContinuousOn (fun s : ℝ ↦ (s : ℂ)⁻¹) (Ici (1 : ℝ)) :=
    Complex.continuous_ofReal.continuousOn.inv₀ fun s hs => by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hs).ne'
  have hcoeff : ContinuousOn coeff (Ici (1 : ℝ)) :=
    (continuousOn_const.mul (continuousOn_const.add hinv) :
      ContinuousOn (fun s : ℝ ↦ (-π : ℂ) * ((I : ℂ) + (s : ℂ)⁻¹)) (Ici (1 : ℝ))).congr
      fun s _ => by simp [coeff, one_div]
  have hg : ContinuousOn (fun s : ℝ ↦ g r s) (Ici (1 : ℝ)) :=
    (((continuousOn_const.mul φ₀''_I_mul_continuousOn).mul zpow_neg_four_continuousOn).mul
      continuousOn_const).mul <| by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (continuousOn_const.mul hinv :
          ContinuousOn (fun s : ℝ ↦ ((-π : ℂ) * (r : ℂ)) * (s : ℂ)⁻¹) (Ici (1 : ℝ))).cexp
  simpa [μ, SpherePacking.Integration.μIciOne] using
    ((by simpa [gN] using (hcoeff.pow n).mul hg :
      ContinuousOn (fun s : ℝ ↦ gN n r s) (Ici (1 : ℝ))).aestronglyMeasurable measurableSet_Ici)

lemma integrable_exp_neg_two_pi : Integrable (fun s : ℝ ↦ rexp (-(2 * π) * s)) μ := by
  simpa [IntegrableOn, SpherePacking.Integration.μIciOne, mul_assoc, mul_left_comm, mul_comm] using
    (MagicFunction.a.IntegralEstimates.I₃.Bound_integrableOn (r := (0 : ℝ)) (C₀ := (1 : ℝ)))

lemma exp_neg_pi_mul_div_le_exp_pi_abs (r s : ℝ) (hs : 1 ≤ s) :
    rexp (-π * r / s) ≤ rexp (π * |r|) :=
  Real.exp_le_exp.2 <| by
    have : (-r / s : ℝ) ≤ |r| / s := by
      simpa [abs_div, abs_neg, abs_of_nonneg (zero_le_one.trans hs)] using le_abs_self (-r / s)
    simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left (this.trans (div_le_self (abs_nonneg r) hs)) Real.pi_pos.le

lemma integrable_gN (n : ℕ) (r : ℝ) : Integrable (gN n r) μ := by
  refine (integrable_exp_neg_two_pi.const_mul ((2 * π) ^ n * (Cφ * rexp (π * |r|)))).mono'
    (gN_measurable (n := n) (r := r)) ?_
  refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s hs => ?_
  refine (gN_norm_bound (n := n) (r := r) (s := s) hs).trans ?_
  have hExp : rexp (-π * r / s) ≤ rexp (π * |r|) :=
    exp_neg_pi_mul_div_le_exp_pi_abs (r := r) (s := s) hs
  have hmul := mul_le_mul_of_nonneg_left hExp (show 0 ≤ (2 * π) ^ n * (Cφ * rexp (-2 * π * s)) from
    mul_nonneg (by positivity) (mul_nonneg Cφ_pos.le (Real.exp_pos _).le))
  grind only

lemma hasDerivAt_integral_gN (n : ℕ) (r₀ : ℝ) :
    HasDerivAt (fun r : ℝ ↦ ∫ s, gN n r s ∂μ) (∫ s, gN (n + 1) r₀ s ∂μ) r₀ := by
  let R : ℝ := |r₀| + 1
  let bound : ℝ → ℝ := fun s ↦ (2 * π) ^ (n + 1) * (Cφ * rexp (π * R)) * rexp (-(2 * π) * s)
  have hbound_int : Integrable bound μ := by
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using
      integrable_exp_neg_two_pi.const_mul ((2 * π) ^ (n + 1) * (Cφ * rexp (π * R)))
  have h_bound :
      ∀ᵐ s ∂μ, ∀ r ∈ Metric.ball r₀ (1 : ℝ), ‖gN (n + 1) r s‖ ≤ bound s := by
    refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s hs r hr => ?_
    refine (gN_norm_bound (n := n + 1) (r := r) (s := s) hs).trans ?_
    have hExp : rexp (-π * r / s) ≤ rexp (π * R) :=
      (exp_neg_pi_mul_div_le_exp_pi_abs (r := r) (s := s) hs).trans (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_left
          (SpherePacking.ForMathlib.abs_le_abs_add_of_mem_ball hr) Real.pi_pos.le))
    have hmul := mul_le_mul_of_nonneg_left hExp
      (show 0 ≤ (2 * π) ^ (n + 1) * (Cφ * rexp (-2 * π * s)) from
        mul_nonneg (by positivity) (mul_nonneg Cφ_pos.le (Real.exp_pos _).le))
    grind only
  simpa [μ, SpherePacking.Integration.μIciOne] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := fun r s ↦ gN n r s) (x₀ := r₀) (s := Metric.ball r₀ (1 : ℝ))
      (hs := by simpa using Metric.ball_mem_nhds r₀ (by norm_num))
      (hF_meas := Filter.Eventually.of_forall fun r => gN_measurable (n := n) (r := r))
      (hF_int := integrable_gN (n := n) (r := r₀))
      (hF'_meas := gN_measurable (n := n + 1) (r := r₀))
      (h_bound := h_bound) (bound_integrable := hbound_int)
      (h_diff := (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s _ r _ => by
        have hg : HasDerivAt (fun r : ℝ ↦ g r s) (coeff s * g r s) r := by
          simpa [g, show ∀ r : ℝ, cexp ((r : ℂ) * coeff s) =
              cexp ((-π : ℂ) * I * (r : ℂ)) * cexp ((-π : ℂ) * (r : ℂ) / (s : ℂ)) from fun r => by
              rw [← Complex.exp_add]; congr 1; simp [coeff]; ring,
            mul_assoc, mul_left_comm, mul_comm]
            using SpherePacking.ForMathlib.hasDerivAt_mul_cexp_ofReal_mul_const
              (a := (-I) * φ₀'' (I * (s : ℂ)) * (s ^ (-4 : ℤ) : ℂ)) (c := coeff s) (x := r)
        simpa [gN, pow_succ, mul_assoc] using hg.const_mul (coeff s ^ n))).2

lemma norm_iteratedDeriv_le (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n I₁' x‖ ≤
      ∫ s in Ici (1 : ℝ), (2 * π) ^ n * (Cφ * rexp (-2 * π * s) * rexp (-π * x / s)) := calc
    ‖iteratedDeriv n I₁' x‖ ≤ ∫ s in Ici (1 : ℝ), ‖gN n x s‖ := by
      have iteratedDeriv_eq_integral_gN :
          iteratedDeriv n I₁' = fun r : ℝ ↦ ∫ s, gN n r s ∂μ := by
        induction n with
        | zero => funext r; simp [iteratedDeriv_zero, gN, μ, μIciOne, Complete_Change_of_Variables]
        | succ n ih => funext r; simpa [iteratedDeriv_succ, ih] using
            (hasDerivAt_integral_gN (n := n) (r₀ := r)).deriv
      simpa [iteratedDeriv_eq_integral_gN, μ, SpherePacking.Integration.μIciOne] using
        norm_integral_le_integral_norm (gN n x)
    _ ≤ _ := setIntegral_mono_on
        (by simpa [IntegrableOn, μIciOne] using (integrable_gN (n := n) (r := x)).norm)
        (by simpa [mul_assoc, mul_left_comm, mul_comm] using
          ((MagicFunction.a.IntegralEstimates.I₃.Bound_integrableOn
            (r := x) (C₀ := Cφ)).const_mul ((2 * π) ^ n)))
        measurableSet_Ici fun s hs => gN_norm_bound (n := n) (r := x) (s := s) hs

lemma xpow_integral_le_of_Cpow (k : ℕ) {Cpow : ℝ}
    (hCpow : ∀ u : ℝ, 0 ≤ u → u ^ k * rexp (-u) ≤ Cpow) :
    ∀ x : ℝ, 0 ≤ x →
      x ^ k * (∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * rexp (-π * x / s)) ≤
        ((π ^ k)⁻¹ * Cpow) * (∫ s in Ici (1 : ℝ), s ^ k * rexp (-2 * π * s)) := by
  intro x hx
  let f : ℝ → ℝ := fun s ↦ x ^ k * (rexp (-2 * π * s) * rexp (-π * x / s))
  let g : ℝ → ℝ := fun s ↦ ((π ^ k)⁻¹ * Cpow) * (s ^ k * rexp (-2 * π * s))
  have hf_int : IntegrableOn f (Ici (1 : ℝ)) volume := by
    simpa [f, mul_assoc, mul_left_comm, mul_comm] using
      (MagicFunction.a.IntegralEstimates.I₃.Bound_integrableOn (r := x) (C₀ := (1 : ℝ))).const_mul
        (x ^ k)
  have hg_int : IntegrableOn g (Ici (1 : ℝ)) volume := by
    simpa [g, mul_assoc, mul_left_comm, mul_comm] using
      ((show IntegrableOn (fun s : ℝ ↦ s ^ k * rexp (-2 * π * s)) (Ici (1 : ℝ)) volume by
        simpa [mul_assoc] using
          SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := k) (b := 2 * π)
            (by positivity))).const_mul ((π ^ k)⁻¹ * Cpow)
  have hmono : ∀ s ∈ Ici (1 : ℝ), f s ≤ g s := fun s hs => by
    have hs1 : (1 : ℝ) ≤ s := hs
    have hpt : x ^ k * rexp (-π * x / s) ≤ (π ^ k)⁻¹ * Cpow * s ^ k := by
      set u : ℝ := (π * x) / s
      have hxpow : x ^ k = (π ^ k)⁻¹ * s ^ k * u ^ k := by
        simp [show x = u * s / π from CancelDenoms.cancel_factors_eq_div
          (id (div_mul_cancel₀ (π * x)
            (lt_of_lt_of_le (by norm_num) hs1).ne').symm) Real.pi_ne_zero,
          mul_pow, div_eq_mul_inv, inv_pow, mul_assoc, mul_left_comm, mul_comm]
      calc x ^ k * rexp (-π * x / s)
          = (π ^ k)⁻¹ * s ^ k * (u ^ k * rexp (-u)) := by
            rw [congrArg rexp (show -π * x / s = -u by ring), hxpow]; ring
        _ ≤ (π ^ k)⁻¹ * s ^ k * Cpow := by
            gcongr; exact hCpow u (div_nonneg (by positivity) (zero_le_one.trans hs1))
        _ = (π ^ k)⁻¹ * Cpow * s ^ k := by ring
    calc f s = rexp (-2 * π * s) * (x ^ k * rexp (-π * x / s)) := by simp [f, mul_assoc, mul_comm]
      _ ≤ rexp (-2 * π * s) * (((π ^ k)⁻¹ * Cpow) * s ^ k) := by gcongr
      _ = g s := by simp [g, mul_assoc, mul_left_comm, mul_comm]
  simpa [show (∫ s in Ici (1 : ℝ), f s) =
      x ^ k * (∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * rexp (-π * x / s)) from
      integral_const_mul (x ^ k) fun a => rexp (-2 * π * a) * rexp (-π * x / a),
    show (∫ s in Ici (1 : ℝ), g s) =
      ((π ^ k)⁻¹ * Cpow) * (∫ s in Ici (1 : ℝ), s ^ k * rexp (-2 * π * s)) from
      integral_const_mul ((π ^ k)⁻¹ * Cpow) fun a => a ^ k * rexp (-2 * π * a),
    mul_assoc, mul_left_comm, mul_comm] using
    setIntegral_mono_on hf_int hg_int measurableSet_Ici hmono

/-- Schwartz-style decay estimate for `RealIntegrals.I₁'`. -/
public theorem decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₁' x‖ ≤ C := by
  intro k n
  obtain ⟨Cpow, hCpow⟩ : ∃ C, ∀ u : ℝ, 0 ≤ u → u ^ k * rexp (-u) ≤ C := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      (((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).eventually
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ => le_of_lt)
    obtain ⟨u0, _, hu0max⟩ := isCompact_Icc.exists_isMaxOn (s := Icc 0 (max N 0))
      ⟨0, le_refl _, le_max_right _ _⟩
      (show Continuous fun u : ℝ ↦ u ^ k * rexp (-u) by fun_prop).continuousOn
    refine ⟨max 1 (u0 ^ k * rexp (-u0)), fun u hu => ?_⟩
    by_cases huN : u ≤ max N 0
    exacts [(hu0max ⟨hu, huN⟩).trans (le_max_right _ _),
      (hN u ((le_max_left N 0).trans (le_of_not_ge huN))).trans (le_max_left _ _)]
  let I : ℝ := ∫ s in Ici (1 : ℝ), s ^ k * rexp (-2 * π * s)
  refine ⟨(2 * π) ^ n * (Cφ * ((π ^ k)⁻¹ * Cpow) * I), fun x hx => ?_⟩
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₁' x‖
        = x ^ k * ‖iteratedDeriv n I₁' x‖ := by
          simp [Real.norm_of_nonneg hx,
            norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ) (n := n) (f := I₁') (x := x)]
    _ ≤ x ^ k * (∫ s in Ici (1:ℝ), (2*π) ^ n * (Cφ * rexp (-2*π*s) * rexp (-π*x/s))) :=
        mul_le_mul_of_nonneg_left (norm_iteratedDeriv_le (n := n) (x := x)) (by positivity)
    _ = ((2*π) ^ n * Cφ) * (x ^ k * (∫ s in Ici (1:ℝ), rexp (-2*π*s) * rexp (-π*x/s))) := by
        rw [show (∫ s in Ici (1:ℝ), (2*π) ^ n * (Cφ * rexp (-2*π*s) * rexp (-π*x/s))) =
          ((2 * π) ^ n * Cφ) * (∫ s in Ici (1:ℝ), rexp (-2*π*s) * rexp (-π*x/s)) by
          simpa [mul_assoc, mul_left_comm, mul_comm] using MeasureTheory.integral_const_mul
            (μ := (volume : Measure ℝ).restrict (Ici (1 : ℝ))) ((2 * π) ^ n * Cφ)
            (fun s : ℝ ↦ rexp (-2 * π * s) * rexp (-π * x / s))]; ring
    _ ≤ ((2 * π) ^ n * Cφ) * (((π ^ k)⁻¹ * Cpow) * I) := mul_le_mul_of_nonneg_left
        (xpow_integral_le_of_Cpow (k := k) (Cpow := Cpow) hCpow x hx)
        (mul_nonneg (by positivity) Cφ_pos.le)
    _ = (2 * π) ^ n * (Cφ * ((π ^ k)⁻¹ * Cpow) * I) := by ring

end

end MagicFunction.a.Schwartz.I1Decay

namespace MagicFunction.a.IntegralEstimates.I₆

open scoped Function UpperHalfPlane Topology Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral

variable (r : ℝ)

/-- The integrand on `Ici 1` whose set integral is `I₆'`. -/
@[expose] public noncomputable def g : ℝ → ℝ → ℂ := fun r t ↦ I * φ₀'' (I * t) * cexp (-π * r * t)

/-- Rewrite `I₆' r` as a set integral of `g r` over `Ici 1` (up to the factor `2`). -/
public lemma I₆'_eq_integral_g_Ioo (r : ℝ) : I₆' r = 2 * ∫ t in Ici (1 : ℝ), g r t := by
  simp [I₆'_eq, g]

noncomputable section Schwartz_Decay

open SchwartzMap
open scoped Topology
open SpherePacking.Integration (μIciOne)

def coeff (t : ℝ) : ℂ := (-π * t : ℂ)

def gN (n : ℕ) (r t : ℝ) : ℂ := (coeff t) ^ n * g r t

lemma coeff_norm_pow_of_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : ‖coeff t‖ ^ n = (π * t) ^ n := by
  simp [coeff, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg ht]

private lemma aestronglyMeasurable_gN (n : ℕ) (r : ℝ) :
    AEStronglyMeasurable (gN n r) μIciOne := by
  simpa [gN, μIciOne] using ContinuousOn.aestronglyMeasurable
    (((by unfold coeff; fun_prop : Continuous coeff).pow n).continuousOn.mul
      ((MagicFunction.a.RealIntegrands.Φ₆_contDiffOn (r := r)).continuousOn.congr fun t ht ↦ by
        dsimp [MagicFunction.a.RealIntegrands.Φ₆, MagicFunction.a.ComplexIntegrands.Φ₆', g]
        rw [z₆'_eq_of_mem ht, show (π : ℂ) * I * (r : ℂ) * (I * (t : ℂ)) = -π * r * t by
          ring_nf; simp [I_sq]]; ac_rfl))
    measurableSet_Ici

/-- A uniform-in-`r` bound on the integrand `g r t` on `Ici 1`. -/
public lemma g_norm_bound_uniform :
    ∃ C₀ > 0, ∀ r : ℝ, ∀ t ∈ Ici (1 : ℝ),
      ‖g r t‖ ≤ C₀ * rexp (-2 * π * t) * rexp (-π * r * t) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀_le
  refine ⟨C₀, hC₀_pos, fun r t ht ↦ ?_⟩
  have ht1 : (1 : ℝ) ≤ t := ht
  have hpos : 0 < (I * t).im := by simpa using one_pos.trans_le ht1
  rw [show ‖g r t‖ = ‖φ₀'' (I * t)‖ * rexp (-π * r * t) by simp [g, norm_exp]]
  gcongr
  simpa [φ₀'', hpos, one_pos.trans_le ht1] using hC₀ ⟨I * t, hpos⟩ (by simpa using by linarith)

private lemma integrable_gN (n : ℕ) (r : ℝ) (hr : -1 < r) : Integrable (gN n r) μIciOne := by
  obtain ⟨C₀, -, hC₀⟩ := g_norm_bound_uniform
  let bound : ℝ → ℝ := fun t ↦ (π ^ n) * (t ^ n * rexp (-(π * (r + 2)) * t)) * C₀
  have hbound_int : Integrable bound μIciOne := by
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using
      (show Integrable (fun t : ℝ ↦ t ^ n * rexp (-(π * (r + 2)) * t)) μIciOne by
        simpa [IntegrableOn, μIciOne] using
          SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n) (b := π * (r + 2))
            (mul_pos Real.pi_pos (by linarith))).const_mul ((π ^ n) * C₀)
  refine Integrable.mono' hbound_int (aestronglyMeasurable_gN (n := n) (r := r)) <|
    (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht ↦ ?_
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hcoeff : ‖coeff t‖ ^ n ≤ (π * t) ^ n := by
    simpa using (coeff_norm_pow_of_nonneg (n := n) (t := t) ht0).le
  calc ‖gN n r t‖ = ‖coeff t‖ ^ n * ‖g r t‖ := by simp [gN]
    _ ≤ (π * t) ^ n * (C₀ * rexp (-2 * π * t) * rexp (-π * r * t)) := by gcongr; exact hC₀ r t ht
    _ = bound t := by
      simp only [bound, mul_pow, ← show rexp (-2 * π * t) * rexp (-π * r * t) =
        rexp (-(π * (r + 2)) * t) by rw [← Real.exp_add]; ring_nf]; ring

private lemma hasDerivAt_integral_gN (n : ℕ) (r₀ : ℝ) (hr₀ : -1 < r₀) :
    HasDerivAt (fun r : ℝ ↦ ∫ t in Ici (1 : ℝ), gN n r t)
      (∫ t in Ici (1 : ℝ), gN (n + 1) r₀ t) r₀ := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := g_norm_bound_uniform
  let bound : ℝ → ℝ := fun t ↦ (π ^ (n + 1)) * (t ^ (n + 1) * rexp (-(π * (r₀ + 1)) * t)) * C₀
  have h_bound : ∀ᵐ t ∂μIciOne, ∀ r ∈ Metric.ball r₀ (1 : ℝ), ‖gN (n + 1) r t‖ ≤ bound t := by
    refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht r hr ↦ ?_
    have ht0 : 0 ≤ t := zero_le_one.trans ht
    have hr_lower : r₀ - 1 ≤ r := by
      nlinarith [abs_lt.1 (by simpa [Metric.mem_ball, dist_eq_norm] using hr : |r - r₀| < 1) |>.1]
    calc ‖gN (n + 1) r t‖ = ‖coeff t‖ ^ (n + 1) * ‖g r t‖ := by simp [gN]
      _ ≤ (π * t) ^ (n + 1) * (C₀ * rexp (-2 * π * t) * rexp (-π * (r₀ - 1) * t)) :=
        mul_le_mul (by simpa using (coeff_norm_pow_of_nonneg (n := n + 1) (t := t) ht0).le)
          (le_mul_of_le_mul_of_nonneg_left (hC₀ r t ht) (Real.exp_le_exp.2 <| by
            simpa [mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg] using
              mul_le_mul_of_nonpos_left
                (mul_le_mul_of_nonneg_right hr_lower ht0 : (r₀ - 1) * t ≤ r * t)
                (by nlinarith [Real.pi_pos] : (-π : ℝ) ≤ 0)) (by positivity))
          (by positivity) (pow_nonneg (mul_nonneg Real.pi_pos.le ht0) (n + 1))
      _ = bound t := by
        simp only [bound, mul_pow, ← show rexp (-2 * π * t) * rexp (-π * (r₀ - 1) * t) =
          rexp (-(π * (r₀ + 1)) * t) by rw [← Real.exp_add]; ring_nf]; ring
  have bound_integrable : Integrable bound μIciOne := by
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using
      (show Integrable (fun t : ℝ ↦ t ^ (n + 1) * rexp (-(π * (r₀ + 1)) * t)) μIciOne by
        simpa [IntegrableOn, μIciOne] using
          SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n + 1)
            (b := π * (r₀ + 1)) (mul_pos Real.pi_pos (by linarith))).const_mul ((π ^ (n + 1)) * C₀)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μIciOne)
    (F := fun r t ↦ gN n r t) (x₀ := r₀) (s := Metric.ball r₀ (1 : ℝ))
    (hs := by simpa using Metric.ball_mem_nhds r₀ (by norm_num))
    (hF_meas := .of_forall fun r ↦ aestronglyMeasurable_gN (n := n) (r := r))
    (hF_int := integrable_gN (n := n) (r := r₀) hr₀)
    (hF'_meas := aestronglyMeasurable_gN (n := n + 1) (r := r₀))
    (h_bound := h_bound) (bound_integrable := bound_integrable)
    (h_diff := ae_of_all _ fun t r _ ↦ by
      simpa [gN, show ∀ y : ℝ, g y t = (I * φ₀'' (I * t)) * cexp ((y : ℂ) * coeff t) by
        intro y; simp [g, coeff, mul_assoc, mul_left_comm, mul_comm], pow_succ,
        mul_assoc, mul_left_comm, mul_comm] using
        SpherePacking.ForMathlib.hasDerivAt_pow_mul_mul_cexp_ofReal_mul_const
          (a := I * φ₀'' (I * t)) (c := coeff t) (n := n) (x := r))).2

lemma iteratedDeriv_bound (n : ℕ) :
    ∃ C₁ > 0, ∀ r : ℝ, 0 ≤ r → ‖iteratedDeriv n I₆' r‖ ≤ C₁ * rexp (-π * r) := by
  have iteratedDeriv_eq : ∀ n : ℕ, ∀ r : ℝ, -1 < r →
      iteratedDeriv n I₆' r = 2 * ∫ t in Ici (1 : ℝ), gN n r t := by
    intro n
    induction n with
    | zero => intro r _; simp [gN, I₆'_eq_integral_g_Ioo]
    | succ n hn =>
      intro r hr
      calc iteratedDeriv (n + 1) I₆' r = deriv (iteratedDeriv n I₆') r := by
            simp [iteratedDeriv_succ]
        _ = deriv (fun x : ℝ ↦ 2 * ∫ t in Ici (1 : ℝ), gN n x t) r :=
          Filter.EventuallyEq.deriv_eq
            (by filter_upwards [Ioi_mem_nhds hr] with x hx using hn x hx)
        _ = 2 * ∫ t in Ici (1 : ℝ), gN (n + 1) r t := by
          simpa using ((hasDerivAt_integral_gN (n := n) (r₀ := r) hr).const_mul (2 : ℂ)).deriv
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := g_norm_bound_uniform
  let B : ℝ → ℝ := fun t ↦ C₀ * (π ^ n) * (t ^ n * rexp (-(2 * π) * t))
  have hB_int : IntegrableOn B (Ici (1 : ℝ)) volume := by
    simpa [B, mul_assoc, mul_left_comm, mul_comm] using
      (show IntegrableOn (fun t : ℝ ↦ t ^ n * rexp (-(2 * π) * t)) (Ici (1 : ℝ)) volume by
        simpa using SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici
          (n := n) (b := 2 * π) (by positivity)).const_mul (C₀ * (π ^ n))
  let A : ℝ := ∫ t in Ici (1 : ℝ), B t
  have hA_nonneg : 0 ≤ A :=
    MeasureTheory.setIntegral_nonneg (μ := volume) (s := Ici (1 : ℝ)) measurableSet_Ici
      fun t ht ↦ by have : 0 ≤ t := zero_le_one.trans ht; simp only [B]; positivity
  refine ⟨2 * (A + 1), by nlinarith [hA_nonneg], fun r hr ↦ ?_⟩
  have hr' : (-1 : ℝ) < r := lt_of_lt_of_le (by norm_num) hr
  simpa [mul_assoc, mul_left_comm, mul_comm] using calc
    ‖iteratedDeriv n I₆' r‖ = 2 * ‖∫ t in Ici (1 : ℝ), gN n r t‖ := by
      rw [iteratedDeriv_eq n r hr']; simp
    _ ≤ 2 * ∫ t in Ici (1 : ℝ), B t * rexp (-π * r) := by
      gcongr
      refine (norm_integral_le_integral_norm (gN n r)).trans <| setIntegral_mono_on
        (by simpa [IntegrableOn, μIciOne] using (integrable_gN (n := n) (r := r) hr').norm)
        (by simpa [mul_assoc] using hB_int.mul_const (rexp (-π * r)))
        measurableSet_Ici fun t ht ↦ by
        have ht0 : 0 ≤ t := zero_le_one.trans ht
        calc ‖gN n r t‖ = ‖coeff t‖ ^ n * ‖g r t‖ := by simp [gN]
          _ ≤ ((π ^ n) * (t ^ n)) * (C₀ * rexp (-2 * π * t) * rexp (-π * r)) :=
            mul_le_mul (by simpa [mul_pow] using
                (coeff_norm_pow_of_nonneg (n := n) (t := t) ht0).le)
              (le_mul_of_le_mul_of_nonneg_left (hC₀ r t ht) (Real.exp_le_exp.2 <| by
                nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left (ht : (1 : ℝ) ≤ t) hr])
                (by positivity)) (by positivity) (by positivity)
          _ = B t * rexp (-π * r) := by simp [B, mul_assoc, mul_left_comm, mul_comm]
    _ = 2 * (A * rexp (-π * r)) := by
      rw [MeasureTheory.integral_mul_const (μ := volume.restrict (Ici (1 : ℝ)))]
    _ ≤ (2 * (A + 1)) * rexp (-π * r) := by nlinarith [hA_nonneg, Real.exp_pos (-π * r)]

/-- Schwartz-style decay estimate for `I₆'`. -/
public theorem decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₆' x‖ ≤ C := fun k n ↦ by
  simpa using MagicFunction.a.IntegralEstimates.decay_of_bounding_uniform_norm_iteratedDeriv
    (I := I₆') (n := n) (iteratedDeriv_bound (n := n)) k

end Schwartz_Decay

end MagicFunction.a.IntegralEstimates.I₆

noncomputable section

open scoped ContDiff SchwartzMap
open SchwartzMap

namespace MagicFunction.a.Schwartz.SmoothI24Common

open scoped Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter intervalIntegral
open MagicFunction.PolyFourierCoeffBound
open MagicFunction.a.ComplexIntegrands
open SpherePacking.Integration
open SpherePacking.ForMathlib

/-- The coefficient function `t ↦ (π * I) * z t` shared by `I₂'` and `I₄'`. -/
@[expose] public def coeff (z : ℝ → ℂ) : ℝ → ℂ := fun t : ℝ => ((π : ℂ) * I) * z t

/-- The Mobius argument `t ↦ -1 / (z t + shift)` used to feed `φ₀''`. -/
@[expose] public def arg (z : ℝ → ℂ) (shift : ℂ) : ℝ → ℂ :=
    fun t : ℝ => (-1 : ℂ) / (z t + shift)

/-- The integrand `t ↦ prefactor * (φ₀''(arg t) * (z t + shift)^2)`. -/
@[expose] public def hf (z : ℝ → ℂ) (shift prefactor : ℂ) : ℝ → ℂ :=
    fun t : ℝ => prefactor * (φ₀'' (arg z shift t) * (z t + shift) ^ (2 : ℕ))

public lemma coeff_norm_le {z : ℝ → ℂ} (hnorm : ∀ t : ℝ, ‖z t‖ ≤ 2) (t : ℝ) :
    ‖coeff z t‖ ≤ 2 * π := by
  simpa [coeff, mul_assoc] using norm_mul_pi_I_le_two_pi (z := z t) (hz := hnorm t)

public lemma continuous_coeff {z : ℝ → ℂ} (hz : Continuous z) : Continuous (coeff z) := by
  simpa [coeff, mul_assoc] using continuous_const.mul hz

/-- Continuity of `hf` on `Ioo 0 1` given the continuity of `z`, non-vanishing of
`z + shift`, and the geometric fact that `arg` lands in the upper half-plane. -/
public lemma continuousOn_hf {z : ℝ → ℂ} (shift prefactor : ℂ)
    (hz : Continuous z)
    (hden : ∀ t, t ∈ Ioo (0 : ℝ) 1 → z t + shift ≠ 0)
    (harg_im_pos : ∀ t, t ∈ Ioo (0 : ℝ) 1 → 0 < (arg z shift t).im) :
    ContinuousOn (hf z shift prefactor) (Ioo (0 : ℝ) 1) := by
  have harg : ContinuousOn (arg z shift) (Ioo (0 : ℝ) 1) :=
    continuousOn_const.div (hz.continuousOn.add continuousOn_const) hden
  simpa [hf, mul_assoc] using continuousOn_const.mul
    ((φ₀''_holo.continuousOn.comp harg harg_im_pos).mul
      ((hz.add continuous_const).pow 2).continuousOn)

/-- Uniform bound on `hf` over `Ioo 0 1` given `‖z t‖ ≤ 2` and `Im(arg t) > 1/2`. -/
public lemma exists_bound_norm_hf {z : ℝ → ℂ} (shift prefactor : ℂ)
    (hnorm : ∀ t : ℝ, ‖z t‖ ≤ 2) (hshift : ‖shift‖ ≤ 1)
    (harg_im_half : ∀ t, t ∈ Ioo (0 : ℝ) 1 → (1 / 2 : ℝ) < (arg z shift t).im) :
    ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖hf z shift prefactor t‖ ≤ M := by
  rcases norm_φ₀_le with ⟨C₀, hC₀_pos, hC₀⟩
  refine ⟨‖prefactor‖ * (C₀ * rexp (-π) * ((3 : ℝ) ^ (2 : ℕ))), fun t ht => ?_⟩
  have hpos : 0 < (arg z shift t).im :=
    lt_trans (by norm_num : (0 : ℝ) < 1 / 2) (harg_im_half t ht)
  have hφle : ‖φ₀'' (arg z shift t)‖ ≤ C₀ * rexp (-π) :=
    norm_φ₀''_le_mul_exp_neg_pi_of_one_half_lt_im (C₀ := C₀) (hC₀_pos := hC₀_pos)
      (hC₀ := hC₀) (z := ⟨arg z shift t, hpos⟩) (harg_im_half t ht)
  have hpow : ‖(z t + shift) ^ (2 : ℕ)‖ ≤ (3 : ℝ) ^ (2 : ℕ) := by
    simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _)
      ((norm_add_le _ _).trans <| by linarith [hnorm t, hshift]) 2
  calc ‖hf z shift prefactor t‖
      = ‖prefactor‖ * (‖φ₀'' (arg z shift t)‖ * ‖(z t + shift) ^ (2 : ℕ)‖) := by simp [hf]
    _ ≤ ‖prefactor‖ * ((C₀ * rexp (-π)) * ((3 : ℝ) ^ (2 : ℕ))) := by gcongr
    _ = ‖prefactor‖ * (C₀ * rexp (-π) * ((3 : ℝ) ^ (2 : ℕ))) := by ring

/-- Smoothness of the integral `f` expressed via `DifferentiationUnderIntegral.g`
with kernel `coeff z` and integrand `hf z shift prefactor`. -/
public theorem contDiff_of_eq_integral_g_Ioo {z : ℝ → ℂ} {shift prefactor : ℂ} {f : ℝ → ℂ}
    (hfEq :
      ∀ x : ℝ, f x = ∫ t in Ioo (0 : ℝ) 1,
        DifferentiationUnderIntegral.g (coeff := coeff z) (hf := hf z shift prefactor) x t)
    (hz : Continuous z)
    (hnorm : ∀ t : ℝ, ‖z t‖ ≤ 2) (hshift : ‖shift‖ ≤ 1)
    (hden : ∀ t, t ∈ Ioo (0 : ℝ) 1 → z t + shift ≠ 0)
    (harg_im_pos : ∀ t, t ∈ Ioo (0 : ℝ) 1 → 0 < (arg z shift t).im)
    (harg_im_half : ∀ t, t ∈ Ioo (0 : ℝ) 1 → (1 / 2 : ℝ) < (arg z shift t).im) :
    ContDiff ℝ (⊤ : ℕ∞) f := by
  simpa [funext hfEq] using
    (DifferentiationUnderIntegral.contDiff_integral_g_Ioo
      (coeff := coeff z) (hf := hf z shift prefactor)
      (continuousOn_hf shift prefactor hz hden harg_im_pos)
      (continuous_coeff hz)
      (exists_bound_norm_hf shift prefactor hnorm hshift harg_im_half)
      (coeff_norm_le hnorm))

end MagicFunction.a.Schwartz.SmoothI24Common

namespace MagicFunction.a.Schwartz.I1Smooth

open scoped Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter intervalIntegral
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals
open MagicFunction.a.RealIntegrands MagicFunction.a.ComplexIntegrands
open MagicFunction.a.Schwartz.SmoothI24Common
open SpherePacking.Integration SpherePacking.ForMathlib

private lemma arg_z₁'_eq_I_div (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    arg z₁' (1 : ℂ) t = I / t := by
  have htne : (t : ℂ) ≠ 0 := mod_cast ht.1.ne'
  change (-1 : ℂ) / (z₁' t + 1) = I / t
  rw [z₁'_eq_of_mem (mem_Icc_of_Ioo ht)]
  field_simp; ring_nf; simp [Complex.I_sq]

/-- Smoothness of `RealIntegrals.I₁'` as a function `ℝ → ℂ`. -/
public theorem I₁'_contDiff : ContDiff ℝ (⊤ : ℕ∞) I₁' :=
  contDiff_of_eq_integral_g_Ioo (z := z₁') (shift := (1 : ℂ)) (prefactor := I)
    (f := I₁') (fun x => by
      simp [RealIntegrals.I₁', MagicFunction.a.RealIntegrands.Φ₁_def,
        DifferentiationUnderIntegral.g, Φ₁', coeff, hf, SmoothI24Common.arg,
        intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le, integral_Ioc_eq_integral_Ioo,
        mul_assoc, mul_left_comm, mul_comm])
    continuous_z₁' norm_z₁'_le_two (by norm_num)
    (fun t ht h0 => by
      have h1 := congrArg Complex.im h0
      simp [z₁'_eq_of_mem (mem_Icc_of_Ioo ht)] at h1; exact ht.1.ne' h1)
    (fun t ht => by simpa [arg_z₁'_eq_I_div (t := t) ht] using one_div_pos.2 ht.1)
    (fun t ht => by linarith [(one_lt_one_div ht.1) ht.2,
      show (arg z₁' (1 : ℂ) t).im = 1 / t from by simp [arg_z₁'_eq_I_div (t := t) ht]])

end MagicFunction.a.Schwartz.I1Smooth

namespace MagicFunction.a.Schwartz.I2Smooth

open scoped Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter intervalIntegral
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals
open MagicFunction.a.RealIntegrands MagicFunction.a.ComplexIntegrands
open MagicFunction.a.Schwartz.SmoothI24Common
open SpherePacking.Integration SpherePacking.ForMathlib

private lemma arg_z₂'_im_eq (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (arg z₂' (1 : ℂ) t).im = 1 / (t ^ 2 + 1) := by
  have harg : arg z₂' (1 : ℂ) t = (-1 : ℂ) / ((t : ℂ) + I) := by
    change (-1 : ℂ) / (z₂' t + 1) = (-1 : ℂ) / ((t : ℂ) + I)
    simpa [add_left_comm, add_comm, add_assoc] using
      congrArg (fun z : ℂ => (-1 : ℂ) / (z + 1)) (z₂'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht))
  simpa [harg] using im_neg_one_div_ofReal_add_I (t := t)

/-- Smoothness of `RealIntegrals.I₂'` as a function `ℝ → ℂ`. -/
public theorem I₂'_contDiff : ContDiff ℝ (⊤ : ℕ∞) I₂' :=
  contDiff_of_eq_integral_g_Ioo (z := z₂') (shift := (1 : ℂ)) (prefactor := (1 : ℂ))
    (f := I₂') (fun x => by
      simp [RealIntegrals.I₂', MagicFunction.a.RealIntegrands.Φ₂_def,
        DifferentiationUnderIntegral.g, Φ₂', Φ₁', coeff, hf, SmoothI24Common.arg,
        intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le, integral_Ioc_eq_integral_Ioo,
        mul_assoc, mul_left_comm, mul_comm])
    continuous_z₂' norm_z₂'_le_two (by norm_num)
    (fun t ht h0 => by
      simpa [z₂'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht), add_left_comm, add_comm] using
        congrArg Complex.im h0)
    (fun t ht => by rw [arg_z₂'_im_eq t ht]; positivity)
    (fun t ht => by
      simpa [arg_z₂'_im_eq (t := t) ht] using one_half_lt_one_div_sq_add_one_of_mem_Ioo01 ht)

end MagicFunction.a.Schwartz.I2Smooth

namespace MagicFunction.a.Schwartz.I4Smooth

open scoped Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter intervalIntegral
open MagicFunction.Parametrisations
open MagicFunction.a.RealIntegrals
open MagicFunction.a.RealIntegrands
open MagicFunction.a.ComplexIntegrands
open MagicFunction.a.Schwartz.SmoothI24Common
open SpherePacking.Integration SpherePacking.ForMathlib

private lemma arg_z₄'_im_eq (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (arg z₄' (-1 : ℂ) t).im = 1 / (t ^ 2 + 1) := by
  have harg : arg z₄' (-1 : ℂ) t = (-1 : ℂ) / ((-t : ℂ) + I) := by
    change (-1 : ℂ) / (z₄' t + (-1 : ℂ)) = (-1 : ℂ) / ((-t : ℂ) + I)
    simpa [sub_eq_add_neg, add_left_comm, add_comm, add_assoc] using
      congrArg (fun z : ℂ => (-1 : ℂ) / (z - 1)) (z₄'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht))
  simpa [harg] using im_neg_one_div_neg_ofReal_add_I (t := t)

/-- Smoothness of `RealIntegrals.I₄'` as a function `ℝ → ℂ`. -/
public theorem I₄'_contDiff : ContDiff ℝ (⊤ : ℕ∞) I₄' :=
  contDiff_of_eq_integral_g_Ioo (z := z₄') (shift := (-1 : ℂ)) (prefactor := (-1 : ℂ))
    (f := I₄') (fun x => by
      simp [RealIntegrals.I₄', MagicFunction.a.RealIntegrands.Φ₄_def,
        DifferentiationUnderIntegral.g, Φ₄', Φ₃', coeff, hf, SmoothI24Common.arg, sub_eq_add_neg,
        intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le, integral_Ioc_eq_integral_Ioo,
        mul_assoc, mul_left_comm, mul_comm])
    continuous_z₄' norm_z₄'_le_two (by norm_num)
    (fun t ht h0 => by
      simpa [z₄'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht), sub_eq_add_neg,
        add_left_comm, add_comm, add_assoc] using congrArg Complex.im h0)
    (fun t ht => by rw [arg_z₄'_im_eq t ht]; positivity)
    (fun t ht => by
      simpa [arg_z₄'_im_eq (t := t) ht] using one_half_lt_one_div_sq_add_one_of_mem_Ioo01 ht)

end MagicFunction.a.Schwartz.I4Smooth

namespace MagicFunction.a.SchwartzProperties

open MagicFunction MagicFunction.a MagicFunction.a.RadialFunctions MagicFunction.a.RealIntegrals
  MagicFunction.Parametrisations MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands
open Set Complex Real MeasureTheory

section Smooth

public theorem I₁'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₁' :=
  MagicFunction.a.Schwartz.I1Smooth.I₁'_contDiff

public theorem I₂'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₂' :=
  MagicFunction.a.Schwartz.I2Smooth.I₂'_contDiff

private lemma I₃'_eq_exp_mul_I₁' :
    RealIntegrals.I₃' = fun x : ℝ => cexp (2 * π * I * x) * RealIntegrals.I₁' x := by
  ext x; rw [I₃'_eq, I₁'_eq, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun t _ => by
    rw [show cexp (↑π * I * ↑x) = cexp (2 * ↑π * I * ↑x) * cexp (-↑π * I * ↑x) by
      rw [← Complex.exp_add]; ring_nf]; ring

public theorem I₃'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₃' :=
  I₃'_eq_exp_mul_I₁' ▸ (contDiff_const.mul ofRealCLM.contDiff).cexp.mul I₁'_smooth'

public theorem I₄'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₄' :=
  MagicFunction.a.Schwartz.I4Smooth.I₄'_contDiff

private lemma I₅'_eq_mul_exp_mul_I₁' :
    RealIntegrals.I₅' = fun x : ℝ ↦ (-2 : ℂ) * cexp (π * I * x) * RealIntegrals.I₁' x := by
  ext x; let f : ℝ → ℂ := fun t => (-I) * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * x * t)
  rw [show RealIntegrals.I₁' x = (∫ t in (0 : ℝ)..1, f t) * cexp (-π * I * x) by
    rw [show RealIntegrals.I₁' x = ∫ t in (0 : ℝ)..1, f t * cexp (-π * I * x) by
      simpa [f, mul_assoc, mul_left_comm, mul_comm] using (I₁'_eq (r := x))]
    simp [intervalIntegral.integral_mul_const],
    show RealIntegrals.I₅' x = (-2 : ℂ) * ∫ t in (0 : ℝ)..1, f t by
      simpa [f, mul_assoc, mul_left_comm, mul_comm] using (I₅'_eq (r := x))]
  linear_combination (2 * ∫ t in (0 : ℝ)..1, f t) *
    (by simp [← Complex.exp_add] : cexp (π * I * x) * cexp (-π * I * x) = 1)

public theorem I₅'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₅' := I₅'_eq_mul_exp_mul_I₁' ▸
  (contDiff_const.mul (contDiff_const.mul ofRealCLM.contDiff).cexp).mul I₁'_smooth'

namespace MagicFunction.a.Schwartz.I6Smooth

open scoped Topology
open Complex Real Set MeasureTheory Filter
open MagicFunction.a.RealIntegrals MagicFunction.a.IntegralEstimates.I₆ RadialSchwartz

local notation "μ" => SpherePacking.Integration.μIciOne

/-- The coefficient capturing the `r`-dependence of the exponential factor. -/
private def coeff (t : ℝ) : ℂ := (-Real.pi * t : ℂ)

private def gN (n : ℕ) (r t : ℝ) : ℂ := (coeff t) ^ n * g r t

private lemma gN_measurable (n : ℕ) (r : ℝ) : AEStronglyMeasurable (gN n r) μ := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ici
  simpa [gN] using
    (show Continuous fun t : ℝ ↦ (coeff t) ^ n by unfold coeff; fun_prop).continuousOn.mul
      ((MagicFunction.a.RealIntegrands.Φ₆_contDiffOn (r := r)).continuousOn.congr fun t ht ↦ by
        dsimp [MagicFunction.a.RealIntegrands.Φ₆, MagicFunction.a.ComplexIntegrands.Φ₆', g]
        rw [MagicFunction.Parametrisations.z₆'_eq_of_mem ht, show (π : ℂ) * I * (r : ℂ) *
          (I * (t : ℂ)) = (-π : ℂ) * (r : ℂ) * (t : ℂ) by ring_nf; simp [I_sq]]
        ac_rfl)

private lemma gN_integrable (n : ℕ) (r : ℝ) (hr : -2 < r) : Integrable (gN n r) μ := by
  obtain ⟨C₀, _, hC₀⟩ := g_norm_bound_uniform
  refine Integrable.mono' (g := fun t : ℝ ↦ (π ^ n) * (t ^ n * rexp (-(π * (r + 2)) * t)) * C₀)
    (by simpa [mul_assoc, mul_left_comm, mul_comm] using
      (show Integrable (fun t : ℝ ↦ t ^ n * rexp (-(π * (r + 2)) * t)) μ by
        simpa [IntegrableOn, SpherePacking.Integration.μIciOne] using
          SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n) (b := π * (r + 2))
            (mul_pos Real.pi_pos (by linarith))).const_mul ((π ^ n) * C₀))
    (gN_measurable n r) <| (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht ↦ ?_
  have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
  calc ‖gN n r t‖ = ‖coeff t‖ ^ n * ‖g r t‖ := by simp [gN, norm_pow]
    _ ≤ (π * t) ^ n * (C₀ * rexp (-2 * π * t) * rexp (-π * r * t)) := by
          gcongr ?_ * ?_
          · simp [coeff, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg ht0]
          · exact hC₀ r t ht
    _ = (π ^ n) * (t ^ n * rexp (-(π * (r + 2)) * t)) * C₀ := by
          rw [show rexp (-(π * (r + 2)) * t) = rexp (-2 * π * t) * rexp (-π * r * t) by
            rw [← Real.exp_add]; ring_nf]; ring

/-- The `hf` specialising `SmoothIntegralIciOne.gN` to the a-side `gN`. -/
private abbrev hφ : ℝ → ℂ := fun t : ℝ ↦ φ₀'' (I * t)

private lemma gN_eq_sharedGN (n : ℕ) (r t : ℝ) :
    gN n r t = SpherePacking.Integration.SmoothIntegralIciOne.gN (hf := hφ) n r t := by
  simp [gN, coeff, SpherePacking.Integration.SmoothIntegralIciOne.gN,
    SpherePacking.Integration.SmoothIntegralIciOne.g,
    SpherePacking.Integration.SmoothIntegralIciOne.coeff,
    MagicFunction.a.IntegralEstimates.I₆.g, hφ, mul_assoc, mul_left_comm, mul_comm]

private theorem I₆'_contDiffOn_Ioi_neg2 :
    ContDiffOn ℝ ∞ MagicFunction.a.RealIntegrals.I₆' (Ioi (-2 : ℝ)) := by
  obtain ⟨C₀, _, hC₀⟩ := MagicFunction.a.IntegralEstimates.I₆.g_norm_bound_uniform
  have hF0 : ContDiffOn ℝ ∞ (fun r => ∫ t in Ici (1 : ℝ), gN 0 r t) (Ioi (-2 : ℝ)) :=
    SpherePacking.ForMathlib.contDiffOn_family_infty_of_hasDerivAt
      (F := fun n r => ∫ t in Ici (1 : ℝ), gN n r t) (s := Ioi (-2 : ℝ))
      isOpen_Ioi (fun n r₀ hr₀ => by
        convert SpherePacking.Integration.SmoothIntegralIciOne.hasDerivAt_integral_gN
          (hf := hφ) (shift := (2 : ℝ))
          (exists_bound_norm_hf := ⟨C₀, fun t ht ↦ by
            simpa [MagicFunction.a.IntegralEstimates.I₆.g, hφ, mul_assoc, mul_comm,
              show rexp (-2 * π * t) * rexp (-π * 0 * t) = rexp (-(π * 2) * t) by
                rw [← Real.exp_add]; ring_nf] using hC₀ 0 t (by simpa using ht)⟩)
          (gN_measurable := fun n x =>
            (aestronglyMeasurable_congr (.of_forall (gN_eq_sharedGN n x))).mp (gN_measurable n x))
          (n := n) (x := r₀) hr₀
          (hF_int :=
            (integrable_congr (.of_forall (gN_eq_sharedGN n r₀))).mp
              (gN_integrable n r₀ hr₀)) using 1
        · exact funext fun r => integral_congr_ae ((ae_restrict_iff' measurableSet_Ici).2 <|
            .of_forall fun t _ ↦ gN_eq_sharedGN n r t)
        · exact integral_congr_ae ((ae_restrict_iff' measurableSet_Ici).2 <|
            .of_forall fun t _ ↦ gN_eq_sharedGN (n + 1) r₀ t)) 0
  refine ((contDiff_const (c := (2 : ℂ))).contDiffOn.mul hF0).congr fun r _ ↦ ?_
  simpa [gN, coeff] using MagicFunction.a.IntegralEstimates.I₆.I₆'_eq_integral_g_Ioo (r := r)

/-- Smoothness of the cutoff radial profile `r ↦ cutoffC r * RealIntegrals.I₆' r`. -/
public theorem cutoffC_mul_I₆'_contDiff :
    ContDiff ℝ ∞ (fun r : ℝ ↦ cutoffC r * RealIntegrals.I₆' r) :=
  contDiff_cutoffC_mul_of_contDiffOn_Ioi_neg1 <| I₆'_contDiffOn_Ioi_neg2.mono fun x hx => by
    simpa [Set.mem_Ioi] using lt_trans (by norm_num : (-2 : ℝ) < -1) hx

end MagicFunction.a.Schwartz.I6Smooth

public theorem I₆'_smooth' : ContDiff ℝ ∞ (fun r : ℝ ↦
    RadialSchwartz.cutoffC r * RealIntegrals.I₆' r) :=
  MagicFunction.a.Schwartz.I6Smooth.cutoffC_mul_I₆'_contDiff

end Smooth

section Decay

public theorem I₁'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₁' x‖ ≤ C :=
  MagicFunction.a.Schwartz.I1Decay.decay'

public theorem I₂'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₂' x‖ ≤ C :=
  MagicFunction.a.IntegralEstimates.I₂.decay'

public theorem I₃'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₃' x‖ ≤ C := fun k n ↦ by
  let g3 : ℝ → ℂ := fun x ↦ cexp ((x : ℂ) * ((2 * π : ℂ) * I))
  obtain ⟨C, hC⟩ := SpherePacking.ForMathlib.decay_iteratedFDeriv_mul_of_bound_left (f := g3)
    (g := RealIntegrals.I₁') (k := k) (n := n) (B := fun m ↦ (2 * π) ^ m)
    (ofRealCLM.contDiff.mul contDiff_const).cexp I₁'_smooth' (fun m x => by
      simpa [g3, mul_assoc, mul_left_comm, mul_comm, abs_of_nonneg Real.pi_pos.le] using
        SpherePacking.ForMathlib.norm_iteratedFDeriv_cexp_mul_ofReal_mul_I_le (a := 2 * π) m x)
    (I₁'_decay' (k := k))
  exact ⟨C, fun x hx => by simpa [I₃'_eq_exp_mul_I₁', g3, mul_comm, mul_left_comm] using hC x hx⟩

public theorem I₄'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₄' x‖ ≤ C :=
  MagicFunction.a.IntegralEstimates.I₄.decay'

public theorem I₅'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₅' x‖ ≤ C := fun k n ↦ by
  let g5 : ℝ → ℂ := fun x ↦ cexp ((x : ℂ) * ((π : ℂ) * I))
  let f5 : ℝ → ℂ := fun x ↦ (-2 : ℂ) * g5 x
  have hg5_smooth : ContDiff ℝ ∞ g5 := (ofRealCLM.contDiff.mul contDiff_const).cexp
  obtain ⟨C, hC⟩ := SpherePacking.ForMathlib.decay_iteratedFDeriv_mul_of_bound_left (f := f5)
    (g := RealIntegrals.I₁') (k := k) (n := n) (B := fun m ↦ 2 * π ^ m)
    (contDiff_const.mul hg5_smooth) I₁'_smooth' (fun m x => by
      rw [show iteratedFDeriv ℝ m f5 x = (-2 : ℂ) • iteratedFDeriv ℝ m g5 x by
        simpa [f5, smul_eq_mul] using iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := m)
          (a := (-2 : ℂ)) (f := g5) (hg5_smooth.contDiffAt.of_le (by exact_mod_cast le_top)),
        norm_smul, show ‖(-2 : ℂ)‖ = (2 : ℝ) from by simp]
      exact mul_le_mul_of_nonneg_left
        (SpherePacking.ForMathlib.norm_iteratedFDeriv_cexp_mul_pi_I_le m x) (by norm_num))
    (I₁'_decay' (k := k))
  exact ⟨C, fun x hx => by
    simpa [I₅'_eq_mul_exp_mul_I₁', f5, g5, mul_comm, mul_left_comm] using hC x hx⟩

public theorem I₆'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₆' x‖ ≤ C :=
  MagicFunction.a.IntegralEstimates.I₆.decay'

end Decay

end MagicFunction.a.SchwartzProperties

namespace MagicFunction.a.SchwartzIntegrals

open RadialSchwartz.Bridge MagicFunction.a.SchwartzProperties

/-- Schwartz function on `ℝ` from primed radial integral `I₁'`. -/
@[expose] public def I₁' : 𝓢(ℝ, ℂ) :=
  fCutSchwartz (f := MagicFunction.a.RealIntegrals.I₁') I₁'_smooth' I₁'_decay'
@[expose] public def I₂' : 𝓢(ℝ, ℂ) :=
  fCutSchwartz (f := MagicFunction.a.RealIntegrals.I₂') I₂'_smooth' I₂'_decay'
@[expose] public def I₃' : 𝓢(ℝ, ℂ) :=
  fCutSchwartz (f := MagicFunction.a.RealIntegrals.I₃') I₃'_smooth' I₃'_decay'
@[expose] public def I₄' : 𝓢(ℝ, ℂ) :=
  fCutSchwartz (f := MagicFunction.a.RealIntegrals.I₄') I₄'_smooth' I₄'_decay'
@[expose] public def I₅' : 𝓢(ℝ, ℂ) :=
  fCutSchwartz (f := MagicFunction.a.RealIntegrals.I₅') I₅'_smooth' I₅'_decay'

/-- Schwartz function on `ℝ` from primed radial integral `I₆'` (cutoff variant). -/
@[expose] public def I₆' : 𝓢(ℝ, ℂ) where
  toFun := RadialSchwartz.Bridge.fCut MagicFunction.a.RealIntegrals.I₆'
  smooth' := by simpa [RadialSchwartz.Bridge.fCut] using I₆'_smooth'
  decay' := by
    simpa using RadialSchwartz.cutoffC_mul_decay_of_nonneg_of_contDiff
      (f := MagicFunction.a.RealIntegrals.I₆') (hg_smooth := I₆'_smooth') I₆'_decay'

public abbrev liftSchwartz (f : 𝓢(ℝ, ℂ)) : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) f

/-- Schwartz function on `EuclideanSpace ℝ (Fin 8)` from radial profile `I₁'`. -/
@[expose] public def I₁ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) := liftSchwartz I₁'
@[expose] public def I₂ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) := liftSchwartz I₂'
@[expose] public def I₃ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) := liftSchwartz I₃'
@[expose] public def I₄ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) := liftSchwartz I₄'
@[expose] public def I₅ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) := liftSchwartz I₅'
@[expose] public def I₆ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) := liftSchwartz I₆'

@[simp] public lemma I₁'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₁' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₁' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma I₂'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₂' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₂' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma I₃'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₃' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₃' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma I₄'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₄' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₄' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma I₅'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₅' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₅' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma I₆'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₆' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₆' r := fCut_apply_of_nonneg _ hr

end MagicFunction.a.SchwartzIntegrals

namespace MagicFunction.FourierEigenfunctions

open SchwartzMap

/-- The radial profile of the `+1` Fourier eigenfunction `a`. -/
@[expose] public def a' : 𝓢(ℝ, ℂ) :=
    MagicFunction.a.SchwartzIntegrals.I₁'
  + MagicFunction.a.SchwartzIntegrals.I₂'
  + MagicFunction.a.SchwartzIntegrals.I₃'
  + MagicFunction.a.SchwartzIntegrals.I₄'
  + MagicFunction.a.SchwartzIntegrals.I₅'
  + MagicFunction.a.SchwartzIntegrals.I₆'

/-- The +1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[expose] public def a : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) a'

/-- Expand `a` as the sum of the six defining integrals from `MagicFunction.a.RadialFunctions`. -/
public theorem a_eq_sum_integrals_RadialFunctions :
    a = MagicFunction.a.RadialFunctions.I₁ + MagicFunction.a.RadialFunctions.I₂
      + MagicFunction.a.RadialFunctions.I₃ + MagicFunction.a.RadialFunctions.I₄
      + MagicFunction.a.RadialFunctions.I₅ + MagicFunction.a.RadialFunctions.I₆ := by
  ext x
  open MagicFunction.a.RadialFunctions in
  simp [a, a', I₁, I₂, I₃, I₄, I₅, I₆, sq_nonneg ‖x‖, add_assoc]

end MagicFunction.FourierEigenfunctions

end
