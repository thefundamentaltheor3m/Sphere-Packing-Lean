module
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.Cancellation
public import SpherePacking.Basic.Domains.RightHalfPlane
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv


/-!
# Complex-parameter "another integral" for `b'`

This file defines a complex-parameter integrand and integral for the "another integral"
representation of `b'`, obtained by replacing `Real.exp (-π * u * t)` with
`Complex.exp (-(π : ℂ) * u * (t : ℂ))`. We prove analyticity of the resulting function on the
right half-plane and record its restriction to real parameters.

## Main definitions
* `bAnotherIntegrandC`
* `bAnotherIntegralC`

## Main statements
* `bAnotherIntegralC_ofReal`
* `bAnotherIntegralC_analyticOnNhd`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators

open MeasureTheory Real Complex

noncomputable section

open SpherePacking

/-- Complex-parameter integrand for the "another integral" representation of `b'`. -/
@[expose] public def bAnotherIntegrandC (u : ℂ) (t : ℝ) : ℂ :=
  bAnotherBase t * Complex.exp (-(π : ℂ) * u * (t : ℂ))

/-- Complex-parameter "another integral" associated to `b'`. -/
@[expose] public def bAnotherIntegralC (u : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrandC u t

/-- Unfolding lemma for `bAnotherIntegrandC`. -/
@[simp] public lemma bAnotherIntegrandC_eq (u : ℂ) (t : ℝ) :
    bAnotherIntegrandC u t = bAnotherBase t * Complex.exp (-(π : ℂ) * u * (t : ℂ)) := by
  rfl

/-- Restriction of `bAnotherIntegrandC` to real parameters. -/
public lemma bAnotherIntegrandC_ofReal (u t : ℝ) :
    bAnotherIntegrandC (u : ℂ) t = bAnotherBase t * (Real.exp (-π * u * t) : ℂ) := by
  simp [bAnotherIntegrandC, mul_assoc]

/-- Restriction of `bAnotherIntegralC` to real parameters. -/
public lemma bAnotherIntegralC_ofReal (u : ℝ) :
    bAnotherIntegralC (u : ℂ) =
      ∫ t in Set.Ioi (0 : ℝ), bAnotherBase t * (Real.exp (-π * u * t) : ℂ) := by
  refine MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
    measurableSet_Ioi (fun t _ => by simp)

/-- `bAnotherIntegralC` is analytic on the right half-plane. -/
public lemma bAnotherIntegralC_analyticOnNhd :
    AnalyticOnNhd ℂ bAnotherIntegralC rightHalfPlane := by
  -- On an open set, complex differentiability implies analyticity.
  refine (DifferentiableOn.analyticOnNhd (s := rightHalfPlane) (f := bAnotherIntegralC) ?_
    rightHalfPlane_isOpen)
  intro u hu
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
  have hu_re : 0 < u.re := by simpa [rightHalfPlane] using hu
  let r : ℝ := u.re / 2
  have hr : 0 < r := by simpa [r] using (half_pos hu_re)
  let ε : ℝ := r
  have hε : 0 < ε := by simpa [ε] using hr
  -- Work with a fixed real decay parameter `r = Re u / 2`.
  let base (t : ℝ) : ℂ := bAnotherIntegrandC (r : ℂ) t
  have hbase_int : Integrable base μ := by
    have : Integrable (fun t : ℝ => bAnotherBase t * (Real.exp (-π * r * t) : ℂ)) μ := by
      simpa [μ] using (bAnotherBase_integrable_exp (u := r) hr)
    simpa [base, bAnotherIntegrandC_ofReal] using this
  have hbase_mul_int : Integrable (fun t : ℝ => (t : ℂ) * base t) μ := by
    have :
        Integrable (fun t : ℝ =>
            (t : ℂ) * bAnotherBase t * (Real.exp (-π * r * t) : ℂ)) μ := by
      simpa [μ] using (bAnotherBase_integrable_mul_exp (u := r) hr)
    simpa [base, bAnotherIntegrandC_ofReal, mul_assoc] using this
  -- Ratio term capturing the dependence on the complex parameter.
  let ratio (x : ℂ) (t : ℝ) : ℂ :=
    Complex.exp ((-(π : ℂ) * (x - (r : ℂ))) * (t : ℂ))
  have hratio_meas : ∀ x : ℂ, Measurable (ratio x) := by
    intro x
    have hcont : Continuous fun t : ℝ => (-(π : ℂ) * (x - (r : ℂ))) * (t : ℂ) :=
      continuous_const.mul continuous_ofReal
    simpa [ratio] using (Complex.continuous_exp.comp hcont).measurable
  -- Factorization: `bAnotherIntegrandC x = base * ratio x`.
  have hfactor (x : ℂ) (t : ℝ) : bAnotherIntegrandC x t = base t * ratio x t := by
    have harg :
        (-(π : ℂ) * x * (t : ℂ)) =
          (-(π : ℂ) * (r : ℂ) * (t : ℂ)) + (-(π : ℂ) * (x - (r : ℂ)) * (t : ℂ)) := by
      ring
    have hexp :
        Complex.exp (-(π : ℂ) * x * (t : ℂ)) =
          Complex.exp (-(π : ℂ) * (r : ℂ) * (t : ℂ)) *
            Complex.exp (-(π : ℂ) * (x - (r : ℂ)) * (t : ℂ)) := by
      simpa [Complex.exp_add, mul_assoc] using congrArg Complex.exp harg
    dsimp [bAnotherIntegrandC, base, ratio]
    rw [hexp]
    simp [mul_assoc]
  have hF_meas :
      ∀ᶠ x in nhds u,
        AEStronglyMeasurable (fun t : ℝ => bAnotherIntegrandC x t) μ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hbase_meas : AEStronglyMeasurable base μ := hbase_int.aestronglyMeasurable
    have hratio_meas' : AEStronglyMeasurable (ratio x) μ := (hratio_meas x).aestronglyMeasurable
    refine (hbase_meas.mul hratio_meas').congr ?_
    exact Filter.Eventually.of_forall (fun t => (hfactor x t).symm)
  -- Bound `‖ratio x t‖ ≤ 1` when `x` stays in `ball u ε` and `t > 0`.
  have hratio_norm_le_one :
      ∀ {x : ℂ} {t : ℝ},
        x ∈ Metric.ball u ε → 0 < t → ‖ratio x t‖ ≤ (1 : ℝ) := by
    intro x t hx ht
    have hxnorm : ‖x - u‖ < ε := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    have hxre : r < x.re := by
      have hre_lt : |x.re - u.re| < ε :=
        lt_of_le_of_lt (by simpa [Complex.sub_re] using abs_re_le_norm (x - u)) hxnorm
      have : u.re - x.re < ε := (abs_sub_lt_iff.1 hre_lt).2
      have hxre' : u.re - ε < x.re := by linarith
      have : u.re - ε = r := by dsimp [ε, r]; ring_nf
      linarith
    have hxpos : 0 ≤ x.re - r := (sub_pos.2 hxre).le
    have hpi : (-Real.pi) ≤ 0 := by linarith [Real.pi_pos]
    have hzre : ((-(π : ℂ) * (x - (r : ℂ))) * (t : ℂ)).re ≤ 0 := by
      have hzre_eq :
          ((-(π : ℂ) * (x - (r : ℂ))) * (t : ℂ)).re = (-Real.pi) * (x.re - r) * t := by
        simp [mul_comm]
      have hzre0 : (-Real.pi) * (x.re - r) * t ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hpi hxpos) ht.le
      simpa [hzre_eq] using hzre0
    simpa [ratio, Complex.norm_exp, Real.exp_le_one_iff] using hzre
  have hIoi : ∀ᵐ t ∂μ, 0 < t := by
    simpa [μ] using
      (ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ)))
  have hratio_norm_le_one_ae {x : ℂ} (hx : x ∈ Metric.ball u ε) :
      (∀ᵐ t ∂μ, ‖ratio x t‖ ≤ (1 : ℝ)) := by
    filter_upwards [hIoi] with t ht
    exact hratio_norm_le_one (x := x) (t := t) hx ht
  -- Integrability of the integrand at `u`.
  have hF_int : Integrable (fun t : ℝ => bAnotherIntegrandC u t) μ := by
    have hratio_meas_u : AEStronglyMeasurable (ratio u) μ := (hratio_meas u).aestronglyMeasurable
    have hratio_bdd : ∀ᵐ t ∂μ, ‖ratio u t‖ ≤ (1 : ℝ) := by
      have : u ∈ Metric.ball u ε := Metric.mem_ball_self hε
      exact hratio_norm_le_one_ae (x := u) this
    have hint :
        Integrable (fun t : ℝ => ratio u t • base t) μ :=
      hbase_int.bdd_smul 1 hratio_meas_u hratio_bdd
    refine hint.congr ?_
    exact Filter.Eventually.of_forall (fun t => by
      -- Use the factorization `bAnotherIntegrandC u t = base t * ratio u t`.
      calc
        ratio u t • base t = ratio u t * base t := by simp [smul_eq_mul]
        _ = base t * ratio u t := by simp [mul_comm]
        _ = bAnotherIntegrandC u t := by simpa using (hfactor u t).symm)
  -- Derivative integrand and domination bound.
  let F' (x : ℂ) (t : ℝ) : ℂ := (-(π : ℂ) * (t : ℂ)) * bAnotherIntegrandC x t
  let bound (t : ℝ) : ℝ := ‖(π : ℂ)‖ * ‖(t : ℂ) * base t‖
  have hF'_meas : AEStronglyMeasurable (F' u) μ := by
    have hratio_meas_u : AEStronglyMeasurable (ratio u) μ := (hratio_meas u).aestronglyMeasurable
    have hbase_mul_meas : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) * base t) μ :=
      hbase_mul_int.aestronglyMeasurable
    have hprod :
        AEStronglyMeasurable (fun t : ℝ => ((t : ℂ) * base t) * ratio u t) μ :=
      hbase_mul_meas.mul hratio_meas_u
    have hprod' :
        AEStronglyMeasurable
          (fun t : ℝ => (-(π : ℂ)) * (((t : ℂ) * base t) * ratio u t)) μ :=
      hprod.const_mul (-(π : ℂ))
    refine hprod'.congr ?_
    exact Filter.Eventually.of_forall (fun t => by
      -- Rewrite `bAnotherIntegrandC u t` using `hfactor`, then reassociate.
      dsimp [F']
      rw [hfactor u t]
      simp [mul_assoc])
  have hbound_int : Integrable bound μ := by
    have : Integrable (fun t : ℝ => ‖(t : ℂ) * base t‖) μ := hbase_mul_int.norm
    simpa [bound, mul_assoc] using this.const_mul ‖(π : ℂ)‖
  have hbound :
      ∀ᵐ t ∂μ, ∀ x ∈ Metric.ball u ε, ‖F' x t‖ ≤ bound t := by
    filter_upwards [hIoi] with t ht
    intro x hx
    have hratio_le : ‖ratio x t‖ ≤ (1 : ℝ) := hratio_norm_le_one (x := x) (t := t) hx ht
    -- Factor and bound by `‖ratio x t‖ ≤ 1`.
    have hfac : bAnotherIntegrandC x t = base t * ratio x t := hfactor x t
    have hform :
        F' x t = (-(π : ℂ)) * ((t : ℂ) * base t) * ratio x t := by
      dsimp [F']
      rw [hfac]
      simp [mul_assoc]
    calc
      ‖F' x t‖ = ‖(-(π : ℂ)) * ((t : ℂ) * base t) * ratio x t‖ := by simp [hform]
      _ = ‖(π : ℂ)‖ * ‖(t : ℂ) * base t‖ * ‖ratio x t‖ := by
        simp [mul_assoc, norm_neg]
      _ ≤ ‖(π : ℂ)‖ * ‖(t : ℂ) * base t‖ * (1 : ℝ) := by
        have hnonneg : 0 ≤ ‖(π : ℂ)‖ * ‖(t : ℂ) * base t‖ :=
          mul_nonneg (norm_nonneg _) (norm_nonneg _)
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hratio_le hnonneg
      _ = bound t := by simp [bound]
  have hdiff :
      ∀ᵐ t ∂μ, ∀ x ∈ Metric.ball u ε,
        HasDerivAt (fun z : ℂ => bAnotherIntegrandC z t) (F' x t) x := by
    -- Pointwise differentiation of the integrand in the parameter.
    refine Filter.Eventually.of_forall ?_
    intro t x _hx
    have hlin :
        HasDerivAt (fun z : ℂ => z * (-(π : ℂ) * (t : ℂ))) (-(π : ℂ) * (t : ℂ)) x := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (hasDerivAt_mul_const (x := x) (-(π : ℂ) * (t : ℂ)))
    have hexp :
        HasDerivAt (fun z : ℂ => Complex.exp (z * (-(π : ℂ) * (t : ℂ))))
          (Complex.exp (x * (-(π : ℂ) * (t : ℂ))) * (-(π : ℂ) * (t : ℂ))) x := by
      simpa using (Complex.hasDerivAt_exp (x * (-(π : ℂ) * (t : ℂ)))).comp x hlin
    have := hexp.const_mul (bAnotherBase t)
    simpa [-bAnotherBase_eq, bAnotherIntegrandC, F', mul_assoc, mul_left_comm, mul_comm] using this
  have hderiv :
      HasDerivAt (fun z : ℂ => ∫ t, bAnotherIntegrandC z t ∂μ) (∫ t, F' u t ∂μ) u := by
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (s := Metric.ball u ε)
      (F := fun z t => bAnotherIntegrandC z t) (x₀ := u) (bound := bound)
      (Metric.ball_mem_nhds u hε) hF_meas hF_int hF'_meas hbound hbound_int hdiff).2
  -- `bAnotherIntegralC` is definitionally the same restricted integral.
  change
    DifferentiableWithinAt ℂ (fun z : ℂ => ∫ t, bAnotherIntegrandC z t ∂μ)
      rightHalfPlane u
  exact hderiv.differentiableAt.differentiableWithinAt (s := rightHalfPlane)

end

end MagicFunction.g.CohnElkies.IntegralReps
