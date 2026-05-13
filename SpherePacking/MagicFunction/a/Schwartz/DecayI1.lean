/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

module

public import SpherePacking.MagicFunction.a.IntegralEstimates.I1
public import SpherePacking.MagicFunction.a.Integrability.RealIntegrands
import SpherePacking.MagicFunction.a.IntegralEstimates.I3
import SpherePacking.MagicFunction.PolyFourierCoeffBound
import Mathlib.Analysis.Calculus.ParametricIntegral
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.IntegrablePowMulExp
import SpherePacking.Integration.Measure

/-! # Schwartz decay for `RealIntegrals.I₁'`: inverse-power decay (`decay'`) via the
change-of-variables representation `IntegralEstimates.I₁.Complete_Change_of_Variables`. -/

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
