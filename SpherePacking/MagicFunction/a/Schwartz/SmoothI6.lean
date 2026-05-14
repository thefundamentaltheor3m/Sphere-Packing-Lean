module
public import SpherePacking.ForMathlib.RadialSchwartz.OneSided
public import SpherePacking.MagicFunction.a.IntegralEstimates.I6

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.IntegrablePowMulExp
import SpherePacking.Integration.Measure
import SpherePacking.Integration.SmoothIntegralIciOne

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

namespace MagicFunction.a.Schwartz.I6Smooth

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

end
