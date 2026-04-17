module
public import SpherePacking.ForMathlib.RadialSchwartz.Cutoff
public import SpherePacking.MagicFunction.a.IntegralEstimates.I6

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import SpherePacking.ForMathlib.ContDiffOnByDeriv
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.IntegrablePowMulExp
import SpherePacking.Integration.Measure

/-!
# Smoothness of `RealIntegrals.I₆'`

This file proves that the function `r ↦ cutoffC r * RealIntegrals.I₆' r` is smooth on `ℝ`. The
main work is to show `ContDiffOn` for `RealIntegrals.I₆'` on `Ioi (-2)` by differentiating under
the integral sign in the `Ici 1` representation of `I₆'`.

## Main statement
* `cutoffC_mul_I₆'_contDiff`
-/

open scoped Topology ContDiff
open Complex Real Set MeasureTheory Filter

noncomputable section

namespace MagicFunction.a.Schwartz.I6Deriv

open MagicFunction.a.RealIntegrals
open MagicFunction.a.IntegralEstimates.I₆

/-- The measure on `Ici 1` used for the `I₆'` integral representation. -/
def μ : Measure ℝ := SpherePacking.Integration.μIciOne

/-- The coefficient capturing the `r`-dependence of the exponential factor. -/
def coeff (t : ℝ) : ℂ := (-Real.pi * t : ℂ)

lemma norm_coeff_of_nonneg {t : ℝ} (ht : 0 ≤ t) : ‖coeff t‖ = π * t := by
  simp [coeff, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg ht]

def gN (n : ℕ) (r t : ℝ) : ℂ := (coeff t) ^ n * g r t

lemma gN_measurable (n : ℕ) (r : ℝ) : AEStronglyMeasurable (gN n r) (μ) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ici
  have hcoeff : Continuous (fun t : ℝ ↦ (coeff t) ^ n) := by unfold coeff; fun_prop
  have hg : ContinuousOn (g r) (Ici (1 : ℝ)) :=
    (MagicFunction.a.RealIntegrands.Φ₆_contDiffOn (r := r)).continuousOn.congr fun t ht ↦ by
      dsimp [MagicFunction.a.RealIntegrands.Φ₆, MagicFunction.a.ComplexIntegrands.Φ₆', g]
      rw [MagicFunction.Parametrisations.z₆'_eq_of_mem ht,
        show (π : ℂ) * I * (r : ℂ) * (I * (t : ℂ)) = (-π : ℂ) * (r : ℂ) * (t : ℂ) by
          ring_nf; simp [I_sq]]
      ac_rfl
  simpa [gN] using hcoeff.continuousOn.mul hg

lemma gN_integrable (n : ℕ) (r : ℝ) (hr : -2 < r) : Integrable (gN n r) (μ) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := g_norm_bound_uniform
  let bound : ℝ → ℝ := fun t ↦ (π ^ n) * (t ^ n * rexp (-(π * (r + 2)) * t)) * C₀
  have hbound_int : Integrable bound (μ) := by
    have hInt : Integrable (fun t : ℝ ↦ t ^ n * rexp (-(π * (r + 2)) * t)) (μ) := by
      simpa [IntegrableOn, μ, SpherePacking.Integration.μIciOne] using
        SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n) (b := π * (r + 2))
          (mul_pos Real.pi_pos (by linarith))
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using hInt.const_mul ((π ^ n) * C₀)
  refine Integrable.mono' hbound_int (gN_measurable n r) ?_
  refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht ↦ ?_
  have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
  have hexp : rexp (-2 * π * t) * rexp (-π * r * t) = rexp (-(π * (r + 2)) * t) := by
    rw [← Real.exp_add]; ring_nf
  calc
    ‖gN n r t‖ = ‖coeff t‖ ^ n * ‖g r t‖ := by simp [gN, norm_pow]
    _ ≤ (π * t) ^ n * (C₀ * rexp (-2 * π * t) * rexp (-π * r * t)) := by
          have : ‖coeff t‖ ^ n ≤ (π * t) ^ n := by simp [norm_coeff_of_nonneg ht0]
          gcongr
          exact hC₀ r t ht
    _ = (π ^ n) * (t ^ n * rexp (-(π * (r + 2)) * t)) * C₀ := by rw [← hexp]; ring

end MagicFunction.a.Schwartz.I6Deriv

namespace MagicFunction.a.Schwartz.I6Smooth

open MagicFunction.a.RealIntegrals
open MagicFunction.a.Schwartz.I6Deriv
open RadialSchwartz

/-- The open set on which the integral defining `I₆'` is smoothly differentiable. -/
def s : Set ℝ := Ioi (-2 : ℝ)

/-- Generalize `I6Deriv.hasDerivAt_integral_gN` from `r₀ > -1` to `r₀ > -2` by shrinking the
neighborhood of differentiation. -/
lemma hasDerivAt_integral_gN_of_gt_neg2 (n : ℕ) (r₀ : ℝ) (hr₀ : -2 < r₀) :
    HasDerivAt (fun r : ℝ ↦ ∫ t in Ici (1 : ℝ), gN n r t)
      (∫ t in Ici (1 : ℝ), gN (n + 1) r₀ t) r₀ := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.a.IntegralEstimates.I₆.g_norm_bound_uniform
  let ε : ℝ := (r₀ + 2) / 2
  have ε_pos : 0 < ε := by grind only
  let bound : ℝ → ℝ := fun t ↦ (π ^ (n + 1)) * (t ^ (n + 1) * rexp (-(π * ε) * t)) * C₀
  have hbound_int : Integrable bound (μ) := by
    have hInt : Integrable (fun t : ℝ ↦ t ^ (n + 1) * rexp (-(π * ε) * t)) (μ) := by
      simpa [IntegrableOn, SpherePacking.Integration.μIciOne] using
        SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n + 1) (b := π * ε)
          (mul_pos Real.pi_pos ε_pos)
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using
      hInt.const_mul ((π ^ (n + 1)) * C₀)
  have h_bound :
      ∀ᵐ t ∂(μ), ∀ r ∈ Metric.ball r₀ ε, ‖gN (n + 1) r t‖ ≤ bound t := by
    refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht r hr ↦ ?_
    have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
    have hε_le : ε ≤ r + 2 := by
      have hball : |r - r₀| < ε := by simpa [Metric.mem_ball, dist_eq_norm] using hr
      rw [abs_sub_lt_iff] at hball
      have hε : ε = (r₀ + 2) / 2 := rfl
      linarith
    have hexp2 : rexp (-(π * (r + 2)) * t) ≤ rexp (-(π * ε) * t) :=
      Real.exp_le_exp.2 <| by
        nlinarith [ht0, hε_le, Real.pi_pos.le, mul_nonneg Real.pi_pos.le ht0]
    have hg' : ‖MagicFunction.a.IntegralEstimates.I₆.g r t‖ ≤ C₀ * rexp (-(π * ε) * t) :=
      calc ‖MagicFunction.a.IntegralEstimates.I₆.g r t‖
          ≤ C₀ * rexp (-2 * π * t) * rexp (-π * r * t) := hC₀ r t ht
        _ = C₀ * rexp (-(π * (r + 2)) * t) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
        _ ≤ C₀ * rexp (-(π * ε) * t) := mul_le_mul_of_nonneg_left hexp2 hC₀_pos.le
    calc
      ‖gN (n + 1) r t‖ =
          ‖coeff t‖ ^ (n + 1) * ‖MagicFunction.a.IntegralEstimates.I₆.g r t‖ := by
        simp [gN, norm_pow]
      _ ≤ (π * t) ^ (n + 1) * (C₀ * rexp (-(π * ε) * t)) := by
            have : ‖coeff t‖ ^ (n + 1) ≤ (π * t) ^ (n + 1) := by
              simp [norm_coeff_of_nonneg ht0]
            gcongr
      _ = bound t := by simp [bound, mul_pow, mul_assoc, mul_left_comm, mul_comm]
  have h_diff :
      ∀ᵐ t ∂μ, ∀ r ∈ Metric.ball r₀ ε,
        HasDerivAt (fun r : ℝ ↦ gN n r t) (gN (n + 1) r t) r := by
    refine ae_of_all _ fun t r _ ↦ ?_
    let A : ℂ := I * φ₀'' (I * t)
    have hg_fun (y : ℝ) :
        MagicFunction.a.IntegralEstimates.I₆.g y t = A * cexp ((y : ℂ) * coeff t) := by
      simp [MagicFunction.a.IntegralEstimates.I₆.g, A, I6Deriv.coeff,
        mul_assoc, mul_left_comm, mul_comm]
    simpa [gN, hg_fun, pow_succ, mul_assoc, mul_left_comm, mul_comm] using
      (SpherePacking.ForMathlib.hasDerivAt_pow_mul_mul_cexp_ofReal_mul_const
        (a := A) (c := coeff t) (n := n) (x := r))
  simpa [SpherePacking.Integration.μIciOne, ε] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun r t ↦ gN n r t) (x₀ := r₀) (s := Metric.ball r₀ ε)
      (hs := Metric.ball_mem_nhds r₀ ε_pos)
      (hF_meas := Eventually.of_forall fun r ↦ gN_measurable n r)
      (hF_int := gN_integrable n r₀ hr₀)
      (hF'_meas := gN_measurable (n + 1) r₀)
      (h_bound := h_bound) (bound_integrable := hbound_int)
      (h_diff := h_diff)).2

/-- The family of integrals `F n r = ∫ t in Ici 1, gN n r t`, whose smooth differentiability
in `r` captures the smoothness of `I₆'`. -/
def F (n : ℕ) (r : ℝ) : ℂ := ∫ t in Ici (1 : ℝ), gN n r t

theorem I₆'_contDiffOn_Ioi_neg2 : ContDiffOn ℝ ∞ MagicFunction.a.RealIntegrals.I₆' s := by
  have hF0 : ContDiffOn ℝ ∞ (F 0) s :=
    SpherePacking.ForMathlib.contDiffOn_family_infty_of_hasDerivAt (F := F) (s := s)
      (by simpa [s] using (isOpen_Ioi : IsOpen (Ioi (-2 : ℝ))))
      (fun n r hr ↦ hasDerivAt_integral_gN_of_gt_neg2 n r hr) 0
  refine ((contDiff_const (c := (2 : ℂ))).contDiffOn.mul hF0).congr fun r _ ↦ ?_
  simpa [F, gN, coeff] using
    MagicFunction.a.IntegralEstimates.I₆.I₆'_eq_integral_g_Ioo (r := r)

/-- Smoothness of the cutoff radial profile `r ↦ cutoffC r * RealIntegrals.I₆' r`. -/
public theorem cutoffC_mul_I₆'_contDiff :
    ContDiff ℝ ∞ (fun r : ℝ ↦ cutoffC r * RealIntegrals.I₆' r) :=
  contDiff_cutoffC_mul_of_contDiffOn_Ioi_neg1 <| I₆'_contDiffOn_Ioi_neg2.mono fun x hx ↦ by
    simpa [s, Set.mem_Ioi] using
      lt_trans (by norm_num : (-2 : ℝ) < (-1 : ℝ)) (by simpa [Set.mem_Ioi] using hx)

end MagicFunction.a.Schwartz.I6Smooth

end
