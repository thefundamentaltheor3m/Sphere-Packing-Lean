module
public import SpherePacking.ForMathlib.RadialSchwartz.Cutoff
public import SpherePacking.MagicFunction.a.IntegralEstimates.I6

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import SpherePacking.ForMathlib.ContDiffOnByDeriv
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
  obtain ⟨C₀, _, hC₀⟩ := g_norm_bound_uniform
  let bound : ℝ → ℝ := fun t ↦ (π ^ n) * (t ^ n * rexp (-(π * (r + 2)) * t)) * C₀
  have hbound_int : Integrable bound (μ) := by
    have hInt : Integrable (fun t : ℝ ↦ t ^ n * rexp (-(π * (r + 2)) * t)) (μ) := by
      simpa [IntegrableOn, μ, SpherePacking.Integration.μIciOne] using
        SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n) (b := π * (r + 2))
          (mul_pos Real.pi_pos (by linarith))
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using hInt.const_mul ((π ^ n) * C₀)
  refine Integrable.mono' hbound_int (gN_measurable n r) <|
    (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht ↦ ?_
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

/-- The `hf` specialising `SmoothIntegralIciOne.gN` to the a-side `gN`. -/
private abbrev hφ : ℝ → ℂ := fun t : ℝ ↦ φ₀'' (I * t)

private lemma gN_eq_sharedGN (n : ℕ) (r t : ℝ) :
    gN n r t =
      SpherePacking.Integration.SmoothIntegralIciOne.gN (hf := hφ) n r t := by
  simp [gN, coeff, SpherePacking.Integration.SmoothIntegralIciOne.gN,
    SpherePacking.Integration.SmoothIntegralIciOne.g,
    SpherePacking.Integration.SmoothIntegralIciOne.coeff,
    MagicFunction.a.IntegralEstimates.I₆.g, hφ, mul_assoc, mul_left_comm, mul_comm]

/-- Differentiate under the integral sign for `∫ t ∈ Ici 1, gN n r t` on `r₀ > -2`, by
delegating to the shared dominated-differentiation lemma in `SmoothIntegralIciOne`. -/
lemma hasDerivAt_integral_gN_of_gt_neg2 (n : ℕ) (r₀ : ℝ) (hr₀ : -2 < r₀) :
    HasDerivAt (fun r : ℝ ↦ ∫ t in Ici (1 : ℝ), gN n r t)
      (∫ t in Ici (1 : ℝ), gN (n + 1) r₀ t) r₀ := by
  obtain ⟨C₀, _, hC₀⟩ := MagicFunction.a.IntegralEstimates.I₆.g_norm_bound_uniform
  have hbound_hf :
      ∃ C, ∀ t : ℝ, 1 ≤ t → ‖hφ t‖ ≤ C * Real.exp (-(Real.pi * (2 : ℝ)) * t) := by
    refine ⟨C₀, fun t ht ↦ ?_⟩
    have hexp : rexp (-2 * π * t) * rexp (-π * 0 * t) = rexp (-(π * 2) * t) := by
      rw [← Real.exp_add]; ring_nf
    simpa [MagicFunction.a.IntegralEstimates.I₆.g, hφ, mul_assoc, hexp, mul_comm] using
      hC₀ 0 t (by simpa using ht)
  have h :=
    SpherePacking.Integration.SmoothIntegralIciOne.hasDerivAt_integral_gN
      (hf := hφ) (shift := (2 : ℝ))
      (exists_bound_norm_hf := hbound_hf)
      (gN_measurable := fun n x =>
        (aestronglyMeasurable_congr (.of_forall (gN_eq_sharedGN n x))).mp (gN_measurable n x))
      (n := n) (x := r₀) hr₀
      (hF_int :=
        (integrable_congr (.of_forall (gN_eq_sharedGN n r₀))).mp (gN_integrable n r₀ hr₀))
  convert h using 1
  · funext r
    exact integral_congr_ae ((ae_restrict_iff' measurableSet_Ici).2 <|
      .of_forall fun t _ ↦ gN_eq_sharedGN n r t)
  · exact integral_congr_ae ((ae_restrict_iff' measurableSet_Ici).2 <|
      .of_forall fun t _ ↦ gN_eq_sharedGN (n + 1) r₀ t)

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
  contDiff_cutoffC_mul_of_contDiffOn_Ioi_neg1 <| I₆'_contDiffOn_Ioi_neg2.mono fun x hx => by
    simpa [s, Set.mem_Ioi] using lt_trans (by norm_num : (-2 : ℝ) < -1) hx

end MagicFunction.a.Schwartz.I6Smooth

end
