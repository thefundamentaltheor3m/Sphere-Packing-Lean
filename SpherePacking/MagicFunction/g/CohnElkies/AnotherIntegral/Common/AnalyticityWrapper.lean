module
public import SpherePacking.Basic.Domains.RightHalfPlane
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Generic analyticity wrapper for `∫ base(t) * exp(-π u t)`

This file provides a single lemma that covers both `aAnotherIntegralC_analyticOnNhd`
and `bAnotherIntegralC_analyticOnNhd`. Given a continuous complex-valued function `base`
on `(0, ∞)` whose product with `exp(-π u t)` is integrable for every real `u > 0`, the
complex-parameter integral `u ↦ ∫ t in (0,∞), base(t) * Complex.exp(-π u t)` is analytic
on the right half-plane.

## Main statement
* `analyticOnNhd_integral_base_exp`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open MeasureTheory Real Complex SpherePacking

noncomputable section

private lemma t_mul_exp_le {c t : ℝ} (hc : 0 < c) :
    t * Real.exp (-c * t) ≤ (2 / c) * Real.exp (-(c / 2) * t) := by
  have hc2 : 0 ≤ (2 / c) := (div_pos (by norm_num) hc).le
  have ht_le : t ≤ (2 / c) * Real.exp ((c / 2) * t) := by
    have hmul := mul_le_mul_of_nonneg_left
      (by linarith [Real.add_one_le_exp ((c / 2) * t)] : (c / 2) * t ≤ Real.exp ((c / 2) * t)) hc2
    simpa [mul_assoc, show (2 / c) * ((c / 2) * t) = t by field_simp [hc.ne']] using hmul
  refine (mul_le_mul_of_nonneg_right ht_le (Real.exp_nonneg (-c * t))).trans_eq ?_
  rw [mul_assoc, ← Real.exp_add]; ring_nf

private lemma norm_exp_le_of_re_ge {z : ℂ} {t c : ℝ} (ht0 : 0 ≤ t) (hcz : c ≤ z.re) :
    ‖Complex.exp (-(π : ℂ) * z * (t : ℂ))‖ ≤ Real.exp (-π * c * t) := by
  have hre : (-(π : ℂ) * z * (t : ℂ)).re = -π * z.re * t := by
    simp [mul_assoc, Complex.mul_re, sub_eq_add_neg, add_comm]
  have hle : -π * z.re * t ≤ -π * c * t := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonpos_left hcz (by nlinarith [Real.pi_pos, ht0] : (-π * t : ℝ) ≤ 0)
  simpa [Complex.norm_exp, hre] using Real.exp_le_exp.mpr hle

/--
Generic analyticity of a parameter-dependent integral of the form
`u ↦ ∫ t ∈ (0, ∞), base(t) * Complex.exp(-π u t)` on the right half-plane.

Takes:
* `hbase_cont`: `base` is continuous on `(0, ∞)`.
* `hbase_int`: for every real `u > 0`, `t ↦ base(t) * Real.exp(-π u t)` is
  integrable on `(0, ∞)`.

Produces analyticity of the complex integral on the right half-plane. -/
public theorem analyticOnNhd_integral_base_exp
    {base : ℝ → ℂ}
    (hbase_cont : ContinuousOn base (Set.Ioi (0 : ℝ)))
    (hbase_int : ∀ u : ℝ, 0 < u →
      IntegrableOn (fun t : ℝ => base t * (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ))) :
    AnalyticOnNhd ℂ
      (fun u : ℂ => ∫ t in Set.Ioi (0 : ℝ), base t * Complex.exp (-(π : ℂ) * u * (t : ℂ)))
      rightHalfPlane := by
  have hDiff :
      DifferentiableOn ℂ
        (fun u : ℂ => ∫ t in Set.Ioi (0 : ℝ), base t * Complex.exp (-(π : ℂ) * u * (t : ℂ)))
        rightHalfPlane := by
    intro u hu
    have hu0 : 0 < u.re := by simpa [rightHalfPlane] using hu
    set ε : ℝ := u.re / 2
    have hε : 0 < ε := by dsimp [ε]; nlinarith [hu0]
    let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
    let F : ℂ → ℝ → ℂ := fun z t => base t * Complex.exp (-(π : ℂ) * z * (t : ℂ))
    let F' : ℂ → ℝ → ℂ := fun z t => (-(π : ℂ) * (t : ℂ)) * F z t
    have hF_meas : ∀ z : ℂ, AEStronglyMeasurable (F z) μ := fun z =>
      (hbase_cont.aestronglyMeasurable measurableSet_Ioi).mul
        ((by fun_prop : Continuous fun t : ℝ =>
          Complex.exp (-(π : ℂ) * z * (t : ℂ))).aestronglyMeasurable)
    have hF_meas' : ∀ᶠ z in nhds u, AEStronglyMeasurable (F z) μ :=
      Filter.Eventually.of_forall hF_meas
    have hF'_meas : AEStronglyMeasurable (F' u) μ :=
      ((by fun_prop : Continuous fun t : ℝ =>
        (-(π : ℂ) * (t : ℂ))).aestronglyMeasurable).mul (hF_meas u)
    have hε2 : 0 < ε / 2 := by positivity
    have hBase_ε2 :
        Integrable (fun t : ℝ => base t * (Real.exp (-π * (ε / 2) * t) : ℂ)) μ := by
      simpa [μ, IntegrableOn] using (hbase_int (ε / 2) hε2)
    have hmem_Ioi : ∀ᵐ t ∂μ, t ∈ Set.Ioi (0 : ℝ) := by
      simpa [μ] using
        (ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi)
    have hF_int : Integrable (F u) μ := by
      refine Integrable.mono'
        (g := fun t : ℝ => ‖base t * (Real.exp (-π * (ε / 2) * t) : ℂ)‖)
        hBase_ε2.norm (hF_meas u) ?_
      filter_upwards [hmem_Ioi] with t ht
      have ht0 : 0 ≤ t := le_of_lt ht
      have hExp_norm : ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ ≤ Real.exp (-π * (ε / 2) * t) :=
        norm_exp_le_of_re_ge ht0 (by dsimp [ε]; linarith : (ε / 2 : ℝ) ≤ u.re)
      have hnormExp : ‖(Real.exp (-π * (ε / 2) * t) : ℂ)‖ = Real.exp (-π * (ε / 2) * t) :=
        Complex.norm_of_nonneg (Real.exp_nonneg _)
      calc
        ‖F u t‖ = ‖base t‖ * ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ := by simp [F]
        _ ≤ ‖base t‖ * Real.exp (-π * (ε / 2) * t) :=
          mul_le_mul_of_nonneg_left hExp_norm (norm_nonneg _)
        _ = ‖base t * (Real.exp (-π * (ε / 2) * t) : ℂ)‖ := by rw [norm_mul, hnormExp]
    let bound : ℝ → ℝ :=
      fun t => (2 / ε) * ‖base t * (Real.exp (-π * (ε / 2) * t) : ℂ)‖
    have hbound_int : Integrable bound μ := by
      simpa [bound] using hBase_ε2.norm.const_mul (2 / ε)
    have hbound :
        ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball u ε, ‖F' z t‖ ≤ bound t := by
      filter_upwards [hmem_Ioi] with t ht
      intro z hz
      have ht0 : 0 ≤ t := ht.le
      have htpos : 0 < t := ht
      have hzre : ε ≤ z.re := by
        have hlt : |z.re - u.re| < ε := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            lt_of_le_of_lt (abs_re_le_norm (z - u))
              (by simpa [Metric.mem_ball] using hz : ‖z - u‖ < ε)
        dsimp [ε] at hlt ⊢; nlinarith [(abs_lt.mp hlt).1]
      have hExp : ‖Complex.exp (-(π : ℂ) * z * (t : ℂ))‖ ≤ Real.exp (-π * ε * t) :=
        norm_exp_le_of_re_ge ht0 hzre
      have hExpTrade :
          (π * t) * Real.exp (-π * ε * t) ≤ (2 / ε) * Real.exp (-π * (ε / 2) * t) := by
        have h1 := mul_le_mul_of_nonneg_left
          (t_mul_exp_le (t := t) (by positivity : (0 : ℝ) < π * ε)) Real.pi_pos.le
        have h2 : (π * (t * Real.exp (-(π * ε) * t))) ≤
            (2 / ε) * Real.exp (-π * (ε / 2) * t) := by
          simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv, Real.pi_ne_zero,
            ne_of_gt hε, mul_add, add_mul, sub_eq_add_neg, mul_neg, neg_mul, neg_add,
            add_assoc, add_left_comm, add_comm] using h1
        simpa [mul_assoc, mul_left_comm, mul_comm] using h2
      have hbase_nonneg : 0 ≤ ‖base t‖ := norm_nonneg _
      have hnorm_integ : ‖F z t‖ ≤ ‖base t‖ * Real.exp (-π * ε * t) := by
        simpa [F, norm_mul, mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left hExp hbase_nonneg
      have hnorm_base_exp :
          ‖base t * (Real.exp (-π * (ε / 2) * t) : ℂ)‖ =
            ‖base t‖ * Real.exp (-π * (ε / 2) * t) := by
        rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
      calc
        ‖F' z t‖ = ‖(-(π : ℂ) * (t : ℂ))‖ * ‖F z t‖ := by simp [F']
        _ ≤ (π * t) * ‖F z t‖ := by rw [show ‖(-(π : ℂ) * (t : ℂ))‖ = π * t from by
              simp [abs_of_pos htpos, Real.pi_pos.le]]
        _ ≤ (π * t) * (‖base t‖ * Real.exp (-π * ε * t)) :=
          mul_le_mul_of_nonneg_left hnorm_integ (by nlinarith [Real.pi_pos, ht0])
        _ ≤ (2 / ε) * (‖base t‖ * Real.exp (-π * (ε / 2) * t)) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_left hExpTrade hbase_nonneg
        _ = bound t := by rw [← hnorm_base_exp]
    have hdiff :
        ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball u ε, HasDerivAt (fun w : ℂ => F w t) (F' z t) z := by
      refine Filter.Eventually.of_forall (fun t z _hz => ?_)
      have hexp :
          HasDerivAt (fun w : ℂ => Complex.exp (-(π : ℂ) * w * (t : ℂ)))
            (Complex.exp (-(π : ℂ) * z * (t : ℂ)) * (-(π : ℂ) * (t : ℂ))) z := by
        simpa using (by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            ((hasDerivAt_id z).const_mul (-(π : ℂ) * (t : ℂ))) :
          HasDerivAt (fun w : ℂ => (-(π : ℂ) * w * (t : ℂ))) (-(π : ℂ) * (t : ℂ)) z).cexp
      simpa [F, F', mul_assoc, mul_left_comm, mul_comm] using hexp.const_mul (base t)
    have hDeriv :
        HasDerivAt (fun z : ℂ => ∫ t, F z t ∂μ) (∫ t, F' u t ∂μ) u :=
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
        (s := Metric.ball u ε) (Metric.ball_mem_nhds u hε) (x₀ := u)
        (F := F) (F' := F') (bound := bound)
        (hF_meas := hF_meas') (hF_int := hF_int) (hF'_meas := hF'_meas)
        (h_bound := hbound) (bound_integrable := hbound_int) (h_diff := hdiff)).2
    change DifferentiableWithinAt ℂ
        (fun z : ℂ => ∫ t in Set.Ioi (0 : ℝ), base t * Complex.exp (-(π : ℂ) * z * (t : ℂ)))
        rightHalfPlane u
    exact hDeriv.differentiableAt.differentiableWithinAt
  exact hDiff.analyticOnNhd rightHalfPlane_isOpen

end

end MagicFunction.g.CohnElkies.IntegralReps
