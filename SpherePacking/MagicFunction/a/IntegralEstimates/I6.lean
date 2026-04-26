/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/
module

public import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.Basic
public import SpherePacking.MagicFunction.a.Integrability.RealIntegrands
public import SpherePacking.MagicFunction.a.IntegralEstimates.PowExpBounds
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.IntegrablePowMulExp
import SpherePacking.Integration.Measure

/-!
# Bounds for `I₆'`

This file proves the analytic estimates needed for the auxiliary integral `I₆'`: a representation
as an integral over `Ici 1`, uniform exponential bounds, and Schwartz decay for iterated
derivatives in the parameter `r`.

## Main definitions
* `g`

## Main statements
* `I₆'_eq_integral_g_Ioo`
* `g_norm_bound_uniform`
* `decay'`
-/

namespace MagicFunction.a.IntegralEstimates.I₆

open scoped Function UpperHalfPlane Topology Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral

variable (r : ℝ)

/-- The integrand on `Ici 1` whose set integral is `I₆'`. -/
@[expose] public noncomputable def g : ℝ → ℝ → ℂ :=
  fun r t ↦ I * φ₀'' (I * t) * cexp (-π * r * t)

/-- Rewrite `I₆' r` as a set integral of `g r` over `Ici 1` (up to the factor `2`). -/
public lemma I₆'_eq_integral_g_Ioo (r : ℝ) : I₆' r = 2 * ∫ t in Ici (1 : ℝ), g r t := by
  simp [I₆'_eq, g]

lemma I₆'_bounding_aux_1 (r : ℝ) : ∀ t ∈ Ici 1, ‖g r t‖ = ‖φ₀'' (I * t)‖ * rexp (-π * r * t) := by
  simp [g, neg_mul, norm_I, one_mul, norm_exp]

lemma I₆'_bounding_aux_2' (C₀ : ℝ)
    (hC₀ : ∀ z : ℍ, 1 / 2 < z.im → ‖φ₀ z‖ ≤ C₀ * rexp (-2 * π * z.im)) (r : ℝ) :
    ∀ t ∈ Ici (1 : ℝ), ‖g r t‖ ≤ C₀ * rexp (-2 * π * t) * rexp (-π * r * t) := by
  intro t ht
  have ht1 : (1 : ℝ) ≤ t := ht
  have htpos : 0 < t := one_pos.trans_le ht1
  have hpos : 0 < (I * t).im := by simpa using htpos
  rw [I₆'_bounding_aux_1 r t ht]
  gcongr
  simpa [φ₀'', hpos, htpos] using hC₀ ⟨I * t, hpos⟩ (by simpa using by linarith : _)

noncomputable section Schwartz_Decay

open SchwartzMap

open scoped Topology

open SpherePacking.Integration (μIciOne)

def coeff (t : ℝ) : ℂ := (-π * t : ℂ)

def gN (n : ℕ) (r t : ℝ) : ℂ := (coeff t) ^ n * g r t

lemma coeff_norm (t : ℝ) : ‖coeff t‖ = |π * t| := by simp [coeff]

lemma coeff_norm_of_nonneg {t : ℝ} (ht : 0 ≤ t) : ‖coeff t‖ = π * t := by
  simp [coeff_norm, abs_of_nonneg (mul_nonneg Real.pi_pos.le ht)]

lemma coeff_norm_pow_of_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖coeff t‖ ^ n = (π * t) ^ n := by
  simp [coeff_norm_of_nonneg (t := t) ht]

lemma coeff_norm_pow_le_pi_mul (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖coeff t‖ ^ n ≤ (π ^ n) * (t ^ n) := by
  simp [coeff_norm_pow_of_nonneg (n := n) (t := t) ht, mul_pow]

lemma g_eq_Φ₆ (r : ℝ) : EqOn (g r) (MagicFunction.a.RealIntegrands.Φ₆ (r := r))
    (Ici (1 : ℝ)) := by
  intro t ht
  dsimp [MagicFunction.a.RealIntegrands.Φ₆, MagicFunction.a.ComplexIntegrands.Φ₆', g]
  rw [z₆'_eq_of_mem ht,
    show (π : ℂ) * I * (r : ℂ) * (I * (t : ℂ)) = (-π : ℂ) * (r : ℂ) * (t : ℂ) by
      ring_nf; simp [I_sq]]
  ac_rfl

private lemma aestronglyMeasurable_gN (n : ℕ) (r : ℝ) :
    AEStronglyMeasurable (gN n r) μIciOne := by
  simpa [gN, μIciOne] using
    ContinuousOn.aestronglyMeasurable
      (((show Continuous coeff by unfold coeff; fun_prop).pow n).continuousOn.mul
        (((MagicFunction.a.RealIntegrands.Φ₆_contDiffOn (r := r)).continuousOn.mono
          fun _ hx ↦ hx).congr (g_eq_Φ₆ (r := r)))) measurableSet_Ici

/-- A uniform-in-`r` bound on the integrand `g r t` on `Ici 1`. -/
public lemma g_norm_bound_uniform :
    ∃ C₀ > 0, ∀ r : ℝ, ∀ t ∈ Ici (1 : ℝ),
      ‖g r t‖ ≤ C₀ * rexp (-2 * π * t) * rexp (-π * r * t) :=
  let ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀_le
  ⟨C₀, hC₀_pos, fun r t ht ↦ by simpa using I₆'_bounding_aux_2' (C₀ := C₀) hC₀ r t ht⟩

lemma gN_norm (n : ℕ) (r t : ℝ) :
    ‖gN n r t‖ = ‖coeff t‖ ^ n * ‖g r t‖ := by
  simp [gN]

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
  calc ‖gN n r t‖ = ‖coeff t‖ ^ n * ‖g r t‖ := gN_norm (n := n) (r := r) (t := t)
    _ ≤ (π * t) ^ n * (C₀ * rexp (-2 * π * t) * rexp (-π * r * t)) := by gcongr; exact hC₀ r t ht
    _ = bound t := by
      have h1 : (π * t) ^ n = (π ^ n) * (t ^ n) := by simp [mul_pow, mul_comm]
      have h2 : rexp (-2 * π * t) * rexp (-π * r * t) = rexp (-(π * (r + 2)) * t) := by
        rw [← Real.exp_add]; ring_nf
      grind only

private lemma hasDerivAt_integral_gN (n : ℕ) (r₀ : ℝ) (hr₀ : -1 < r₀) :
    HasDerivAt (fun r : ℝ ↦ ∫ t in Ici (1 : ℝ), gN n r t)
      (∫ t in Ici (1 : ℝ), gN (n + 1) r₀ t) r₀ := by
  let μ : Measure ℝ := μIciOne
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := g_norm_bound_uniform
  let bound : ℝ → ℝ := fun t ↦ (π ^ (n + 1)) * (t ^ (n + 1) * rexp (-(π * (r₀ + 1)) * t)) * C₀
  have h_bound : ∀ᵐ t ∂μ, ∀ r ∈ Metric.ball r₀ (1 : ℝ), ‖gN (n + 1) r t‖ ≤ bound t := by
    refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht r hr ↦ ?_
    have ht0 : 0 ≤ t := zero_le_one.trans ht
    have hr_lower : r₀ - 1 ≤ r := by
      have : |r - r₀| < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hr
      nlinarith [abs_lt.1 this |>.1]
    calc ‖gN (n + 1) r t‖ = ‖coeff t‖ ^ (n + 1) * ‖g r t‖ := gN_norm (n := n + 1) (r := r) (t := t)
      _ ≤ (π * t) ^ (n + 1) * (C₀ * rexp (-2 * π * t) * rexp (-π * (r₀ - 1) * t)) :=
        mul_le_mul (by simpa using (coeff_norm_pow_of_nonneg (n := n + 1) (t := t) ht0).le)
          (le_mul_of_le_mul_of_nonneg_left (hC₀ r t ht) (Real.exp_le_exp.2 <| by
            simpa [mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg] using
              mul_le_mul_of_nonpos_left
                (mul_le_mul_of_nonneg_right hr_lower ht0 : (r₀ - 1) * t ≤ r * t)
                (by nlinarith [Real.pi_pos] : (-π : ℝ) ≤ 0)) (by positivity))
          (by positivity) (pow_nonneg (mul_nonneg Real.pi_pos.le ht0) (n + 1))
      _ = bound t := by
        have : (π * t) ^ (n + 1) = (π ^ (n + 1)) * (t ^ (n + 1)) := by simp [mul_pow, mul_comm]
        have : rexp (-2 * π * t) * rexp (-π * (r₀ - 1) * t) = rexp (-(π * (r₀ + 1)) * t) := by
          rw [← Real.exp_add]; ring_nf
        grind only
  have bound_integrable : Integrable bound μ := by
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using
      (show Integrable (fun t : ℝ ↦ t ^ (n + 1) * rexp (-(π * (r₀ + 1)) * t)) μ by
        simpa [IntegrableOn, μ, μIciOne] using
          SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n + 1)
            (b := π * (r₀ + 1)) (mul_pos Real.pi_pos (by linarith))).const_mul ((π ^ (n + 1)) * C₀)
  have h_diff : ∀ᵐ t ∂μ, ∀ r ∈ Metric.ball r₀ (1 : ℝ),
      HasDerivAt (fun r : ℝ ↦ gN n r t) (gN (n + 1) r t) r := ae_of_all _ fun t r _ ↦ by
    let A : ℂ := I * φ₀'' (I * t)
    simpa [gN, show ∀ y : ℝ, g y t = A * cexp ((y : ℂ) * coeff t) from fun y => by
      simp [A, g, coeff, mul_assoc, mul_left_comm, mul_comm], pow_succ,
      mul_assoc, mul_left_comm, mul_comm] using
      SpherePacking.ForMathlib.hasDerivAt_pow_mul_mul_cexp_ofReal_mul_const (a := A) (c := coeff t)
        (n := n) (x := r)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun r t ↦ gN n r t) (x₀ := r₀) (s := Metric.ball r₀ (1 : ℝ))
    (hs := by simpa using Metric.ball_mem_nhds r₀ (by norm_num))
    (hF_meas := .of_forall fun r ↦ by simpa [μ] using aestronglyMeasurable_gN (n := n) (r := r))
    (hF_int := integrable_gN (n := n) (r := r₀) hr₀)
    (hF'_meas := aestronglyMeasurable_gN (n := n + 1) (r := r₀))
    (h_bound := h_bound) (bound_integrable := bound_integrable) (h_diff := h_diff)).2

lemma iteratedDeriv_I₆'_eq_integral_gN (n : ℕ) :
    ∀ r : ℝ, -1 < r → iteratedDeriv n I₆' r = 2 * ∫ t in Ici (1 : ℝ), gN n r t := by
  induction n with
  | zero => intro r _; simp [gN, I₆'_eq_integral_g_Ioo]
  | succ n hn =>
    intro r hr
    calc
      iteratedDeriv (n + 1) I₆' r = deriv (iteratedDeriv n I₆') r := by simp [iteratedDeriv_succ]
      _ = deriv (fun x : ℝ ↦ 2 * ∫ t in Ici (1 : ℝ), gN n x t) r := by
        simpa using (show (iteratedDeriv n I₆') =ᶠ[𝓝 r]
            (fun x : ℝ ↦ 2 * ∫ t in Ici (1 : ℝ), gN n x t) from by
          filter_upwards [Ioi_mem_nhds hr] with x hx using hn x hx).deriv_eq
      _ = 2 * ∫ t in Ici (1 : ℝ), gN (n + 1) r t := by
        simpa using ((hasDerivAt_integral_gN (n := n) (r₀ := r) hr).const_mul (2 : ℂ)).deriv

lemma iteratedDeriv_bound (n : ℕ) :
    ∃ C₁ > 0, ∀ r : ℝ, 0 ≤ r → ‖iteratedDeriv n I₆' r‖ ≤ C₁ * rexp (-π * r) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := g_norm_bound_uniform
  let B : ℝ → ℝ := fun t ↦ C₀ * (π ^ n) * (t ^ n * rexp (-(2 * π) * t))
  have hB_int : IntegrableOn B (Ici (1 : ℝ)) volume := by
    simpa [B, mul_assoc, mul_left_comm, mul_comm] using
      (show IntegrableOn (fun t : ℝ ↦ t ^ n * rexp (-(2 * π) * t)) (Ici (1 : ℝ)) volume by
        simpa using SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici
          (n := n) (b := 2 * π) (by positivity)).const_mul (C₀ * (π ^ n))
  let A : ℝ := ∫ t in Ici (1 : ℝ), B t
  have hA_nonneg : 0 ≤ A :=
    MeasureTheory.setIntegral_nonneg (μ := volume) (s := Ici (1 : ℝ))
      measurableSet_Ici fun t ht ↦ by
        have : 0 ≤ t := zero_le_one.trans ht; simp only [B]; positivity
  refine ⟨2 * (A + 1), by nlinarith [hA_nonneg], fun r hr ↦ ?_⟩
  have hr' : (-1 : ℝ) < r := lt_of_lt_of_le (by norm_num) hr
  simpa [mul_assoc, mul_left_comm, mul_comm] using show
      ‖iteratedDeriv n I₆' r‖ ≤ (2 * (A + 1)) * rexp (-π * r) from calc
    ‖iteratedDeriv n I₆' r‖ = 2 * ‖∫ t in Ici (1 : ℝ), gN n r t‖ := by
      rw [iteratedDeriv_I₆'_eq_integral_gN (n := n) r hr']; simp
    _ ≤ 2 * ∫ t in Ici (1 : ℝ), B t * rexp (-π * r) := by
      gcongr
      refine (norm_integral_le_integral_norm (gN n r)).trans <| setIntegral_mono_on
        (by simpa [IntegrableOn, μIciOne] using (integrable_gN (n := n) (r := r) hr').norm)
        (by simpa [mul_assoc] using hB_int.mul_const (rexp (-π * r)))
        measurableSet_Ici fun t ht ↦ by
        have ht0 : 0 ≤ t := zero_le_one.trans ht
        calc ‖gN n r t‖ = ‖coeff t‖ ^ n * ‖g r t‖ := gN_norm (n := n) (r := r) (t := t)
          _ ≤ ((π ^ n) * (t ^ n)) * (C₀ * rexp (-2 * π * t) * rexp (-π * r)) :=
            mul_le_mul (by simpa using coeff_norm_pow_le_pi_mul (n := n) (t := t) ht0)
              (le_mul_of_le_mul_of_nonneg_left (hC₀ r t ht) (Real.exp_le_exp.2 <| by
                nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left (ht : (1 : ℝ) ≤ t) hr])
                (by positivity)) (by positivity) (by positivity)
          _ = B t * rexp (-π * r) := by simp [B, mul_assoc, mul_left_comm, mul_comm]
    _ = 2 * (A * rexp (-π * r)) := by
      rw [MeasureTheory.integral_mul_const (μ := volume.restrict (Ici (1 : ℝ)))
        (r := rexp (-π * r)) (f := fun t : ℝ ↦ B t)]
    _ ≤ (2 * (A + 1)) * rexp (-π * r) := by nlinarith [hA_nonneg, Real.exp_pos (-π * r)]

/--
Schwartz-style decay estimate for `I₆'`: all iterated derivatives decay faster than any power.

The prime in the name indicates that this result is about the auxiliary integral `I₆'`.
-/
public theorem decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₆' x‖ ≤ C := fun k n ↦ by
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := iteratedDeriv_bound (n := n)
  simpa using MagicFunction.a.IntegralEstimates.decay_of_bounding_uniform_norm_iteratedDeriv
    (I := I₆') (n := n) ⟨C₁, hC₁_pos, hC₁⟩ k

end Schwartz_Decay

end I₆

end MagicFunction.a.IntegralEstimates
