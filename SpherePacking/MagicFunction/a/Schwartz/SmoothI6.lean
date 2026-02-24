module
public import SpherePacking.ForMathlib.RadialSchwartz.Cutoff
public import SpherePacking.MagicFunction.a.IntegralEstimates.I6

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import SpherePacking.ForMathlib.ContDiffOnByDeriv
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.IntegrablePowMulExp
import SpherePacking.Integration.Measure
import SpherePacking.Integration.SmoothIntegralIciOne


/-!
# Smoothness of `RealIntegrals.I₆'`

This file proves that the function `r ↦ cutoffC r * RealIntegrals.I₆' r` is smooth on `ℝ`.  The
main work is to show `ContDiffOn` for `RealIntegrals.I₆'` on `Ioi (-2)` by differentiating under the
integral sign in the `Ici 1` representation of `I₆'`.

## Main statement
* `cutoffC_mul_I₆'_contDiff`
-/


open scoped Topology UpperHalfPlane ContDiff
open Complex Real Set MeasureTheory Filter intervalIntegral

noncomputable section

namespace MagicFunction.a.Schwartz.I6Deriv

open MagicFunction.a.RealIntegrals
open MagicFunction.a.IntegralEstimates.I₆

def μ : Measure ℝ := SpherePacking.Integration.μIciOne

/-! The coefficient capturing the `r`-dependence of the exponential factor. -/

def coeff (t : ℝ) : ℂ := (-Real.pi * t : ℂ)

lemma norm_coeff_of_nonneg {t : ℝ} (ht : 0 ≤ t) : ‖coeff t‖ = π * t := by
  have h : ‖coeff t‖ = |π * t| := by
    -- `coeff t` is a real complex number.
    simp [coeff]
  have : 0 ≤ π * t := mul_nonneg Real.pi_pos.le ht
  simp [h, abs_of_nonneg this]

def gN (n : ℕ) (r t : ℝ) : ℂ := (coeff t) ^ n * g r t

lemma gN_measurable (n : ℕ) (r : ℝ) : AEStronglyMeasurable (gN n r) (μ) := by
  have hcoeff_cont : ContinuousOn (fun t : ℝ ↦ (coeff t) ^ n) (Ici (1 : ℝ)) := by
    have hcoeff : Continuous coeff := by
      simpa [coeff, mul_assoc] using
        (continuous_const.mul Complex.continuous_ofReal)
    simpa using (hcoeff.pow n).continuousOn
  have hΦ : ContinuousOn (MagicFunction.a.RealIntegrands.Φ₆ (r := r)) (Ici (1 : ℝ)) :=
    (MagicFunction.a.RealIntegrands.Φ₆_contDiffOn (r := r)).continuousOn
  have hgEq : EqOn (g r) (MagicFunction.a.RealIntegrands.Φ₆ (r := r)) (Ici (1 : ℝ)) := by
    intro t ht
    have hexparg :
        (π : ℂ) * I * (r : ℂ) * (I * (t : ℂ)) = (-π : ℂ) * (r : ℂ) * (t : ℂ) := by
      ring_nf
      simp [I_sq]
    dsimp [MagicFunction.a.RealIntegrands.Φ₆, MagicFunction.a.ComplexIntegrands.Φ₆', g]
    rw [MagicFunction.Parametrisations.z₆'_eq_of_mem ht, hexparg]
    ac_rfl
  have hg : ContinuousOn (g r) (Ici (1 : ℝ)) := hΦ.congr hgEq
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ici
  simpa [gN] using hcoeff_cont.mul hg

lemma gN_integrable (n : ℕ) (r : ℝ) (hr : -2 < r) : Integrable (gN n r) (μ) := by
  have hmeas : AEStronglyMeasurable (gN n r) (μ) := gN_measurable (n := n) (r := r)
  have hb : 0 < π * (r + 2) := mul_pos Real.pi_pos (by linarith)
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := g_norm_bound_uniform
  let bound : ℝ → ℝ :=
    fun t ↦ (π ^ n) * (t ^ n * rexp (-(π * (r + 2)) * t)) * C₀
  have hbound_int : Integrable bound (μ) := by
    have : Integrable (fun t : ℝ ↦ t ^ n * rexp (-(π * (r + 2)) * t)) (μ) := by
      simpa [IntegrableOn, μ, SpherePacking.Integration.μIciOne] using
        (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n) (b := π * (r + 2))
          (by simpa [mul_assoc] using hb))
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using this.const_mul ((π ^ n) * C₀)
  refine Integrable.mono' hbound_int hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
  intro t ht
  have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
  have hcoeff : ‖coeff t‖ ^ n ≤ (π * t) ^ n := by
    simp [norm_coeff_of_nonneg (t := t) ht0]
  have hg : ‖g r t‖ ≤ C₀ * rexp (-2 * π * t) * rexp (-π * r * t) := hC₀ r t ht
  have hexp :
      rexp (-2 * π * t) * rexp (-π * r * t) = rexp (-(π * (r + 2)) * t) := by
    have : (-(π * (r + 2)) * t) = (-2 * π * t) + (-π * r * t) := by ring_nf
    simp [this, Real.exp_add, mul_left_comm, mul_comm]
  -- combine
  calc
    ‖gN n r t‖ = ‖coeff t‖ ^ n * ‖g r t‖ := by simp [gN, norm_pow]
    _ ≤ (π * t) ^ n * (C₀ * rexp (-2 * π * t) * rexp (-π * r * t)) := by
          gcongr
    _ = (π ^ n) * (t ^ n * rexp (-(π * (r + 2)) * t)) * C₀ := by
          have hp : (π * t) ^ n = (π ^ n) * (t ^ n) := by
            simp [mul_pow, mul_comm]
          have hmulExp :
              C₀ * rexp (-2 * π * t) * rexp (-π * r * t) = C₀ * rexp (-(π * (r + 2)) * t) := by
            -- avoid `simp`-cancellation; just reassociate then rewrite the exponential product.
            calc
              C₀ * rexp (-2 * π * t) * rexp (-π * r * t)
                  = C₀ * (rexp (-2 * π * t) * rexp (-π * r * t)) := by ring_nf
              _ = C₀ * rexp (-(π * (r + 2)) * t) := by rw [hexp]
          -- rewrite, then normalize by commutativity/associativity.
          -- `ring_nf` is safe here and avoids `mul_eq_mul_*` simp lemmas.
          rw [hmulExp, hp]
          ring_nf

lemma hasDerivAt_integral_gN (n : ℕ) (r₀ : ℝ) (hr₀ : -1 < r₀) :
    HasDerivAt (fun r : ℝ ↦ ∫ t in Ici (1 : ℝ), gN n r t)
      (∫ t in Ici (1 : ℝ), gN (n + 1) r₀ t) r₀ := by
  let hf : ℝ → ℂ := fun t ↦ φ₀'' (I * t)
  obtain ⟨C, _, hC⟩ := g_norm_bound_uniform
  have hbound :
      ∃ C, ∀ t : ℝ, 1 ≤ t → ‖hf t‖ ≤ C * Real.exp (-(Real.pi * (2 : ℝ)) * t) := by
    refine ⟨C, ?_⟩
    intro t ht
    have h := hC 0 t ht
    have harg : (-(Real.pi * (2 : ℝ)) * t) = -2 * Real.pi * t := by ring_nf
    simpa [hf, MagicFunction.a.IntegralEstimates.I₆.g, harg,
      mul_assoc, mul_left_comm, mul_comm] using h
  have hgN (n : ℕ) (x : ℝ) :
      gN n x = SpherePacking.Integration.SmoothIntegralIciOne.gN (hf := hf) n x := by
    funext t
    simp [gN, SpherePacking.Integration.SmoothIntegralIciOne.gN,
      SpherePacking.Integration.SmoothIntegralIciOne.g, hf, coeff,
      SpherePacking.Integration.SmoothIntegralIciOne.coeff,
      MagicFunction.a.IntegralEstimates.I₆.g, mul_assoc, mul_left_comm, mul_comm]
  have hmeas :
      ∀ n : ℕ, ∀ x : ℝ,
        AEStronglyMeasurable (SpherePacking.Integration.SmoothIntegralIciOne.gN (hf := hf) n x)
          SpherePacking.Integration.μIciOne := by
    intro n x
    simpa [hgN n x] using (gN_measurable (n := n) (r := x))
  have hInt :
      Integrable (SpherePacking.Integration.SmoothIntegralIciOne.gN (hf := hf) n r₀)
        SpherePacking.Integration.μIciOne := by
    have hInt' : Integrable (gN n r₀) (μ) := gN_integrable (n := n) (r := r₀) (by linarith)
    simpa [hgN n r₀] using hInt'
  have h :=
    SpherePacking.Integration.SmoothIntegralIciOne.hasDerivAt_integral_gN
      (hf := hf) (shift := (2 : ℝ)) (hshift := by norm_num)
      (exists_bound_norm_hf := hbound) (gN_measurable := hmeas) (n := n) (x := r₀) hr₀ hInt
  simpa [hgN] using h

end MagicFunction.a.Schwartz.I6Deriv

namespace MagicFunction.a.Schwartz.I6Smooth

open MagicFunction.a.RealIntegrals
open MagicFunction.a.Schwartz.I6Deriv
open RadialSchwartz

-- The open set on which the integral defining `I₆'` is smoothly differentiable.
def s : Set ℝ := Ioi (-2 : ℝ)

-- Generalize `gN_integrable` from `r > -1` to `r > -2`.
lemma gN_integrable_of_gt_neg2 (n : ℕ) (r : ℝ) (hr : -2 < r) : Integrable (gN n r) (μ) := by
  simpa using (gN_integrable (n := n) (r := r) hr)

-- Generalize `hasDerivAt_integral_gN` from `r₀ > -1` to `r₀ > -2`.
lemma hasDerivAt_integral_gN_of_gt_neg2 (n : ℕ) (r₀ : ℝ) (hr₀ : -2 < r₀) :
    HasDerivAt (fun r : ℝ ↦ ∫ t in Ici (1 : ℝ), gN n r t)
      (∫ t in Ici (1 : ℝ), gN (n + 1) r₀ t) r₀ := by
  have hF_meas : ∀ᶠ r in 𝓝 r₀, AEStronglyMeasurable (gN n r) (μ) :=
    Eventually.of_forall (fun r ↦ gN_measurable (n := n) (r := r))
  have hF_int : Integrable (gN n r₀) (μ) := gN_integrable_of_gt_neg2 (n := n) (r := r₀) hr₀
  have hF'_meas : AEStronglyMeasurable (gN (n + 1) r₀) (μ) :=
    gN_measurable (n := n + 1) (r := r₀)
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.a.IntegralEstimates.I₆.g_norm_bound_uniform
  -- Shrink the neighborhood to avoid values `r ≤ -2`.
  let ε : ℝ := (r₀ + 2) / 2
  have ε_pos : 0 < ε := by
    have : 0 < r₀ + 2 := by linarith
    positivity
  have hb : 0 < π * ε := mul_pos Real.pi_pos ε_pos
  let bound : ℝ → ℝ :=
    fun t ↦ (π ^ (n + 1)) * (t ^ (n + 1) * rexp (-(π * ε) * t)) * C₀
  have hbound_int : Integrable bound (μ) := by
    have hInt :
        IntegrableOn (fun t : ℝ ↦ t ^ (n + 1) * rexp (-(π * ε) * t)) (Ici (1 : ℝ)) volume :=
      SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n + 1) (b := π * ε)
        (by simpa [mul_assoc] using hb)
    have : Integrable (fun t : ℝ ↦ t ^ (n + 1) * rexp (-(π * ε) * t)) (μ) := by
      simpa [IntegrableOn, SpherePacking.Integration.μIciOne] using hInt
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using
      this.const_mul ((π ^ (n + 1)) * C₀)
  have h_bound :
      ∀ᵐ t ∂(μ), ∀ r ∈ Metric.ball r₀ ε, ‖gN (n + 1) r t‖ ≤ bound t := by
    refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
    intro t ht r hr
    have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
    have hcoeff : ‖coeff t‖ ^ (n + 1) ≤ (π * t) ^ (n + 1) := by
      simp [norm_coeff_of_nonneg (t := t) ht0]
    have hg :
        ‖MagicFunction.a.IntegralEstimates.I₆.g r t‖ ≤
          C₀ * rexp (-2 * π * t) * rexp (-π * r * t) := hC₀ r t ht
    have hg' :
        ‖MagicFunction.a.IntegralEstimates.I₆.g r t‖ ≤ C₀ * rexp (-(π * ε) * t) := by
      have hr_lower : r₀ - ε ≤ r := by
        have : |r - r₀| < ε := by simpa [Metric.mem_ball, dist_eq_norm] using hr
        have hεle : 0 ≤ ε := le_of_lt ε_pos
        have : r₀ - ε < r := by nlinarith [abs_lt.1 this |>.1, hεle]
        exact le_of_lt this
      have hε_def : r₀ + 2 - ε = ε := by
        dsimp [ε]
        ring_nf
      have hε_le : ε ≤ r + 2 := by
        have : r₀ + 2 - ε ≤ r + 2 := by linarith [hr_lower]
        simpa [hε_def] using this
      have hlin : (-(π * (r + 2)) * t : ℝ) ≤ (-(π * ε) * t) := by
        have hπ : (π : ℝ) * ε ≤ (π : ℝ) * (r + 2) :=
          mul_le_mul_of_nonneg_left hε_le Real.pi_pos.le
        have ht' : (π * ε) * t ≤ (π * (r + 2)) * t :=
          mul_le_mul_of_nonneg_right hπ ht0
        simpa [mul_assoc, mul_left_comm, mul_comm] using (neg_le_neg ht')
      have hexp2 : rexp (-(π * (r + 2)) * t) ≤ rexp (-(π * ε) * t) :=
        Real.exp_le_exp.2 hlin
      have hrepl :
          rexp (-2 * π * t) * rexp (-π * r * t) = rexp (-(π * (r + 2)) * t) := by
        have harg : (-(π * (r + 2)) * t) = (-2 * π * t) + (-π * r * t) := by ring_nf
        simp [harg, Real.exp_add, mul_comm]
      calc
        ‖MagicFunction.a.IntegralEstimates.I₆.g r t‖ ≤
            C₀ * rexp (-2 * π * t) * rexp (-π * r * t) := hg
        _ = C₀ * (rexp (-2 * π * t) * rexp (-π * r * t)) := by ring_nf
        _ = C₀ * rexp (-(π * (r + 2)) * t) := by rw [hrepl]
        _ ≤ C₀ * rexp (-(π * ε) * t) := by
              exact mul_le_mul_of_nonneg_left hexp2 hC₀_pos.le
    calc
      ‖gN (n + 1) r t‖ =
          ‖coeff t‖ ^ (n + 1) * ‖MagicFunction.a.IntegralEstimates.I₆.g r t‖ := by
        simp [gN, norm_pow]
      _ ≤ (π * t) ^ (n + 1) * (C₀ * rexp (-(π * ε) * t)) := by
            gcongr
      _ = (π ^ (n + 1)) * (t ^ (n + 1) * rexp (-(π * ε) * t)) * C₀ := by
            simp [mul_pow, mul_assoc, mul_left_comm, mul_comm]
      _ = bound t := by simp [bound, mul_left_comm, mul_comm]
  have h_diff :
      ∀ᵐ t ∂μ, ∀ r ∈ Metric.ball r₀ ε,
        HasDerivAt (fun r : ℝ ↦ gN n r t) (gN (n + 1) r t) r := by
    refine ae_of_all _ ?_
    intro t r _
    -- Expand the derivative of `gN` explicitly.
    let A : ℂ := I * φ₀'' (I * t)
    have hg_fun (y : ℝ) :
        MagicFunction.a.IntegralEstimates.I₆.g y t = A * cexp ((y : ℂ) * coeff t) := by
      have : cexp ((y : ℂ) * coeff t) = cexp (-π * y * t) := by
        simp [I6Deriv.coeff, mul_left_comm, mul_comm]
      simp [MagicFunction.a.IntegralEstimates.I₆.g, A, this, mul_assoc, mul_comm]
    simpa [gN, hg_fun, pow_succ, mul_assoc, mul_left_comm, mul_comm] using
      (SpherePacking.ForMathlib.hasDerivAt_pow_mul_mul_cexp_ofReal_mul_const
        (a := A) (c := coeff t) (n := n) (x := r))
  simpa [SpherePacking.Integration.μIciOne, ε] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (μ))
      (F := fun r t ↦ gN n r t) (x₀ := r₀) (s := Metric.ball r₀ ε)
      (hs := Metric.ball_mem_nhds r₀ ε_pos)
      (hF_meas := hF_meas) (hF_int := hF_int)
      (hF'_meas := hF'_meas) (h_bound := h_bound) (bound_integrable := hbound_int)
      (h_diff := h_diff)).2

def F (n : ℕ) (r : ℝ) : ℂ := ∫ t in Ici (1 : ℝ), gN n r t

lemma hasDerivAt_F (n : ℕ) (r : ℝ) (hr : r ∈ s) :
    HasDerivAt (F n) (F (n + 1) r) r := by
  simpa [F] using hasDerivAt_integral_gN_of_gt_neg2 (n := n) (r₀ := r) (by simpa [s] using hr)

theorem I₆'_contDiffOn_Ioi_neg2 : ContDiffOn ℝ ∞ MagicFunction.a.RealIntegrals.I₆' s := by
  have hs : IsOpen s := by simpa [s] using (isOpen_Ioi : IsOpen (Ioi (-2 : ℝ)))
  have hF0 : ContDiffOn ℝ ∞ (F 0) s := by
    simpa using
      (SpherePacking.ForMathlib.contDiffOn_family_infty_of_hasDerivAt (F := F) (s := s) hs
        (fun n r hr => by simpa using (hasDerivAt_F (n := n) (r := r) hr)) 0)
  have hmul : ContDiffOn ℝ ∞ (fun r : ℝ ↦ (2 : ℂ) * F 0 r) s := by
    simpa using (contDiff_const.contDiffOn.mul hF0)
  refine hmul.congr ?_
  intro r hr
  -- `I₆' r = 2 * ∫ g r`, and `gN 0 = g`.
  simpa [F, gN, coeff] using
    (MagicFunction.a.IntegralEstimates.I₆.I₆'_eq_integral_g_Ioo (r := r))

/-- Smoothness of the cutoff radial profile `r ↦ cutoffC r * RealIntegrals.I₆' r`. -/
public theorem cutoffC_mul_I₆'_contDiff :
    ContDiff ℝ ∞ (fun r : ℝ ↦ cutoffC r * RealIntegrals.I₆' r) := by
  refine contDiff_cutoffC_mul_of_contDiffOn_Ioi_neg1 ?_
  refine I₆'_contDiffOn_Ioi_neg2.mono ?_
  intro x hx
  simpa [s, Set.mem_Ioi] using
    lt_trans (by norm_num : (-2 : ℝ) < (-1 : ℝ)) (by simpa [Set.mem_Ioi] using hx)

end MagicFunction.a.Schwartz.I6Smooth

end
