module
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Cancellation.ImagAxis
public import
  SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Cancellation.LargeImagApprox
public import
  SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Cancellation.Integrability
public import SpherePacking.Basic.Domains.RightHalfPlane
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
import SpherePacking.Integration.Measure
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv


/-!
# Complex-parameter "another integral" for `a'`

This file defines a complex-parameter integrand and integral by replacing the real factor
`Real.exp (-π * u * t)` with the holomorphic exponential `Complex.exp (-(π : ℂ) * u * (t : ℂ))`.
We prove analyticity of the resulting function on the right half-plane and record its restriction
to real parameters.

## Main definitions
* `aAnotherBase`
* `aAnotherIntegrandC`
* `aAnotherIntegralC`

## Main statements
* `aAnotherIntegralC_ofReal`
* `aAnotherIntegralC_analyticOnNhd`

## Complex parameter version

We replace `Real.exp (-π*u*t)` by the holomorphic `Complex.exp (-(π:ℂ) * u * (t:ℂ))`.
This is the natural object for an analytic-continuation/identity-theorem proof.
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped UpperHalfPlane

open MeasureTheory Real Complex
open SpherePacking.Integration (μIoi0)
open UpperHalfPlane

open SpherePacking

noncomputable section


/-- The `u`-independent bracket in the "another integral" integrand for `a'`. -/
@[expose] public def aAnotherBase (t : ℝ) : ℂ :=
  (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
      ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
      ((8640 / π : ℝ) : ℂ) * t -
      ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))

/-- Complex-parameter integrand for the "another integral" representation of `a'`. -/
@[expose] public def aAnotherIntegrandC (u : ℂ) (t : ℝ) : ℂ :=
  aAnotherBase t * Complex.exp (-(π : ℂ) * u * (t : ℂ))

/-- Complex-parameter "another integral" for `a'`. -/
@[expose] public def aAnotherIntegralC (u : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrandC u t

@[simp]
lemma aAnotherIntegrandC_eq (u : ℂ) (t : ℝ) :
    aAnotherIntegrandC u t = aAnotherBase t * Complex.exp (-(π : ℂ) * u * (t : ℂ)) := by
  rfl

lemma aAnotherIntegrand_eq (u t : ℝ) :
    aAnotherIntegrand u t = aAnotherBase t * Real.exp (-π * u * t) := by
  simp [aAnotherIntegrand, aAnotherBase, mul_assoc]

lemma aAnotherIntegrandC_ofReal (u t : ℝ) :
    aAnotherIntegrandC (u : ℂ) t = aAnotherIntegrand u t := by
  -- `Complex.exp` agrees with `Real.exp` on real arguments.
  simp [aAnotherIntegrandC, aAnotherBase, aAnotherIntegrand]

/-- On real parameters, `aAnotherIntegralC` agrees with
the real "another integral". -/
public lemma aAnotherIntegralC_ofReal (u : ℝ) :
    aAnotherIntegralC (u : ℂ) = ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t := by
  refine MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
    measurableSet_Ioi (fun t _ht => by simpa using aAnotherIntegrandC_ofReal u t)

/-- `aAnotherIntegralC` is analytic on the right half-plane. -/
public lemma aAnotherIntegralC_analyticOnNhd :
    AnalyticOnNhd ℂ aAnotherIntegralC rightHalfPlane := by
  have hDiff : DifferentiableOn ℂ aAnotherIntegralC rightHalfPlane := by
    intro u hu
    have hu0 : 0 < u.re := by simpa [rightHalfPlane] using hu
    set ε : ℝ := u.re / 2
    have hε : 0 < ε := by
      dsimp [ε]
      nlinarith [hu0]
    let μ : Measure ℝ := μIoi0
    have hφ :
        AEStronglyMeasurable (fun t : ℝ => φ₀'' ((Complex.I : ℂ) / (t : ℂ))) μ := by
      have hcontφ : ContinuousOn (fun z : ℂ => φ₀'' z) upperHalfPlaneSet := by
        simpa using MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn
      have hcontDen : ContinuousOn (fun t : ℝ => (t : ℂ)) (Set.Ioi (0 : ℝ)) :=
        (continuous_ofReal : Continuous fun t : ℝ => (t : ℂ)).continuousOn
      have hden0 : ∀ t ∈ Set.Ioi (0 : ℝ), (t : ℂ) ≠ 0 := by
        intro t ht
        exact_mod_cast (ne_of_gt ht)
      have hcontIdiv : ContinuousOn (fun t : ℝ => (Complex.I : ℂ) / (t : ℂ)) (Set.Ioi (0 : ℝ)) :=
        (continuous_const.continuousOn.div hcontDen hden0)
      have hmaps :
          Set.MapsTo (fun t : ℝ => (Complex.I : ℂ) / (t : ℂ)) (Set.Ioi (0 : ℝ))
            upperHalfPlaneSet := by
        intro t ht
        have him : (((Complex.I : ℂ) / (t : ℂ)) : ℂ).im = t⁻¹ := imag_I_div t
        have : 0 < (((Complex.I : ℂ) / (t : ℂ)) : ℂ).im := by
          rw [him]
          exact inv_pos.2 (by simpa using ht)
        exact this
      have hcomp : ContinuousOn (fun t : ℝ => φ₀'' ((Complex.I : ℂ) / (t : ℂ))) (Set.Ioi (0 : ℝ)) :=
        hcontφ.comp hcontIdiv hmaps
      exact hcomp.aestronglyMeasurable measurableSet_Ioi
    have hF_meas : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ => aAnotherIntegrandC z t) μ := by
      intro z
      have hpow :
          AEStronglyMeasurable (fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ)) μ := by
        have : Continuous fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ) := by fun_prop
        exact this.aestronglyMeasurable
      have ht : AEStronglyMeasurable (fun t : ℝ => (t : ℂ)) μ := by
        have : Continuous fun t : ℝ => (t : ℂ) := continuous_ofReal
        exact this.aestronglyMeasurable
      have hexp2 : AEStronglyMeasurable (fun t : ℝ => (Real.exp (2 * π * t) : ℂ)) μ := by
        have : Continuous fun t : ℝ => (Real.exp (2 * π * t) : ℂ) := by fun_prop
        exact this.aestronglyMeasurable
      have hfactor :
          AEStronglyMeasurable (fun t : ℝ => Complex.exp (-(π : ℂ) * z * (t : ℂ))) μ := by
        have : Continuous fun t : ℝ => Complex.exp (-(π : ℂ) * z * (t : ℂ)) := by fun_prop
        exact this.aestronglyMeasurable
      have hbase : AEStronglyMeasurable (fun t : ℝ => aAnotherBase t) μ := by
        have ht2φ :
            AEStronglyMeasurable (fun t : ℝ =>
              ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ))) μ :=
          hpow.mul hφ
        have h36 :
            AEStronglyMeasurable (fun t : ℝ =>
              ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t)) μ :=
          (hexp2.const_mul ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ))
        have h8640 :
            AEStronglyMeasurable (fun t : ℝ => ((8640 / π : ℝ) : ℂ) * t) μ :=
          (ht.const_mul ((8640 / π : ℝ) : ℂ))
        have h18144 :
            AEStronglyMeasurable (fun _t : ℝ => ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) μ :=
          aestronglyMeasurable_const
        simpa [aAnotherBase, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using
          (ht2φ.sub h36).add h8640 |>.sub h18144
      simpa [aAnotherIntegrandC, mul_assoc] using hbase.mul hfactor
    have hF_meas' :
        ∀ᶠ z in nhds u, AEStronglyMeasurable (fun t : ℝ => aAnotherIntegrandC z t) μ :=
      (Filter.Eventually.of_forall hF_meas)
    have hF'_meas_u :
        AEStronglyMeasurable (fun t : ℝ => (-(π : ℂ) * (t : ℂ)) * aAnotherIntegrandC u t) μ := by
      have hlin :
          AEStronglyMeasurable (fun t : ℝ => (-(π : ℂ) * (t : ℂ))) μ := by
        have : Continuous fun t : ℝ => (-(π : ℂ) * (t : ℂ)) := by fun_prop
        exact this.aestronglyMeasurable
      exact hlin.mul (hF_meas u)
    have hmul_exp :
        ∀ {c t : ℝ}, 0 < c → 0 ≤ t →
          t * Real.exp (-c * t) ≤ (2 / c) * Real.exp (-(c / 2) * t) := by
      intro c t hc ht
      have hx : (c / 2) * t ≤ Real.exp ((c / 2) * t) := by
        have h := Real.add_one_le_exp ((c / 2) * t)
        linarith
      have hc2 : 0 ≤ (2 / c) := by
        have : 0 < (2 / c) := div_pos (by norm_num) hc
        exact this.le
      have ht_le :
          t ≤ (2 / c) * Real.exp ((c / 2) * t) := by
        have hmul := mul_le_mul_of_nonneg_left hx hc2
        have hsimp : (2 / c) * ((c / 2) * t) = t := by
          field_simp [hc.ne']
        simpa [mul_assoc, hsimp] using hmul
      have hmul := mul_le_mul_of_nonneg_right ht_le (Real.exp_nonneg (-c * t))
      refine hmul.trans_eq ?_
      calc
        ((2 / c) * Real.exp ((c / 2) * t)) * Real.exp (-c * t)
            = (2 / c) * (Real.exp ((c / 2) * t) * Real.exp (-c * t)) := by ring
        _ = (2 / c) * Real.exp ((c / 2) * t + (-c * t)) := by simp [Real.exp_add]
        _ = (2 / c) * Real.exp (-(c / 2) * t) := by ring_nf
    have hInt_base : Integrable (fun t : ℝ => aAnotherIntegrand (ε / 2) t) μ := by
      have hε2 : 0 < ε / 2 := by positivity
      simpa [μ, μIoi0, IntegrableOn] using (aAnotherIntegrand_integrable_of_pos (u := ε / 2) hε2)
    have hF_int : Integrable (fun t : ℝ => aAnotherIntegrandC u t) μ := by
      refine Integrable.mono' (g := fun t : ℝ => ‖aAnotherIntegrand (ε / 2) t‖)
        (hInt_base.norm) (hF_meas u) ?_
      have hmem : ∀ᵐ t ∂μ, t ∈ Set.Ioi (0 : ℝ) := by
        simpa [μ, μIoi0] using
          (ae_restrict_mem measurableSet_Ioi :
            ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)), t ∈ Set.Ioi (0 : ℝ))
      filter_upwards [hmem] with t ht
      have ht0 : 0 ≤ t := le_of_lt ht
      have hExp :
          ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ ≤ Real.exp (-π * (ε / 2) * t) := by
        have hre : (-(π : ℂ) * u * (t : ℂ)).re = -π * u.re * t := by
          simp [mul_assoc, Complex.mul_re, sub_eq_add_neg, add_comm]
        have hle : -π * u.re * t ≤ -π * (ε / 2) * t := by
          -- `ε = u.re / 2`, so `ε / 2 ≤ u.re`.
          have hu' : (ε / 2 : ℝ) ≤ u.re := by
            dsimp [ε]
            linarith
          have hneg : (-π * t : ℝ) ≤ 0 := by
            have hπ : 0 < (π : ℝ) := Real.pi_pos
            nlinarith [hπ, ht0]
          -- Multiply the inequality by the nonpositive scalar `-π*t`.
          have hmul : (-π * t) * u.re ≤ (-π * t) * (ε / 2) :=
            mul_le_mul_of_nonpos_left hu' hneg
          -- Reassociate.
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
        simpa [Complex.norm_exp, hre] using (Real.exp_le_exp.mpr hle)
      -- Convert the exponential bound into an integrable bound for the full integrand.
      have hExp' :
          ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ ≤
            ‖Complex.exp (-(π : ℂ) * ((ε / 2 : ℝ) : ℂ) * (t : ℂ))‖ := by
        have hreε :
            (-(π : ℂ) * ((ε / 2 : ℝ) : ℂ) * (t : ℂ)).re = -π * (ε / 2) * t := by
          simp [mul_assoc, Complex.mul_re, sub_eq_add_neg, add_comm]
        have hnormε :
            ‖Complex.exp (-(π : ℂ) * ((ε / 2 : ℝ) : ℂ) * (t : ℂ))‖ =
              Real.exp (-π * (ε / 2) * t) := by
          simp [Complex.norm_exp]
        exact le_of_le_of_eq hExp (id (Eq.symm hnormε))
      have hmul :
          ‖aAnotherBase t‖ * ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ ≤
            ‖aAnotherBase t‖ * ‖Complex.exp (-(π : ℂ) * ((ε / 2 : ℝ) : ℂ) * (t : ℂ))‖ :=
        mul_le_mul_of_nonneg_left hExp' (norm_nonneg _)
      -- Now rewrite both sides as norms of the corresponding integrands.
      simpa [aAnotherIntegrandC_eq, aAnotherIntegrand_eq, norm_mul, mul_assoc, mul_left_comm,
        mul_comm, RCLike.norm_ofReal, Real.abs_exp] using hmul
    let bound : ℝ → ℝ := fun t => (2 / ε) * ‖aAnotherIntegrand (ε / 2) t‖
    have hbound_int : Integrable bound μ := by
      have hnorm : Integrable (fun t : ℝ => ‖aAnotherIntegrand (ε / 2) t‖) μ := hInt_base.norm
      simpa [bound] using hnorm.const_mul (2 / ε)
    have hbound :
        ∀ᵐ t : ℝ ∂μ, ∀ z ∈ Metric.ball u ε,
          ‖(-(π : ℂ) * (t : ℂ)) * aAnotherIntegrandC z t‖ ≤ bound t := by
      have hmem : ∀ᵐ t ∂μ, t ∈ Set.Ioi (0 : ℝ) := by
        simpa [μ, μIoi0] using
          (ae_restrict_mem measurableSet_Ioi :
            ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)), t ∈ Set.Ioi (0 : ℝ))
      filter_upwards [hmem] with t ht
      intro z hz
      have ht0 : 0 ≤ t := le_of_lt ht
      have htpos : 0 < t := ht
      have hzre : ε ≤ z.re := by
        have hz' : ‖z - u‖ < ε := by simpa [Metric.mem_ball] using hz
        have habs : |(z - u).re| ≤ ‖z - u‖ := abs_re_le_norm (z - u)
        have hlt : |z.re - u.re| < ε := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using lt_of_le_of_lt habs hz'
        have hl : -ε < z.re - u.re := (abs_lt.mp hlt).1
        dsimp [ε] at hl ⊢
        nlinarith
      have hExp :
          ‖Complex.exp (-(π : ℂ) * z * (t : ℂ))‖ ≤ Real.exp (-π * ε * t) := by
        have hre : (-(π : ℂ) * z * (t : ℂ)).re = -π * z.re * t := by
          simp [mul_assoc, Complex.mul_re, sub_eq_add_neg, add_comm]
        have hle : -π * z.re * t ≤ -π * ε * t := by
          have hneg : (-π * t : ℝ) ≤ 0 := by
            have hπ : 0 < (π : ℝ) := Real.pi_pos
            nlinarith [hπ, ht0]
          have hmul : (-π * t) * z.re ≤ (-π * t) * ε :=
            mul_le_mul_of_nonpos_left hzre hneg
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
        simpa [Complex.norm_exp, hre] using (Real.exp_le_exp.mpr hle)
      have hExpTrade :
          (π * t) * Real.exp (-π * ε * t) ≤ (2 / ε) * Real.exp (-π * (ε / 2) * t) := by
        have hc : 0 < (π * ε) := by positivity
        have h0 :
            t * Real.exp (-(π * ε) * t) ≤ (2 / (π * ε)) * Real.exp (-((π * ε) / 2) * t) :=
          hmul_exp hc ht0
        have hπ : 0 ≤ (π : ℝ) := Real.pi_pos.le
        have h1 := mul_le_mul_of_nonneg_left h0 hπ
        -- Normalize constants and exponents.
        have hεne : (ε : ℝ) ≠ 0 := ne_of_gt hε
        have hπne : (π : ℝ) ≠ 0 := Real.pi_ne_zero
        -- `simp` will rewrite `-(π*ε)*t` to `-π*ε*t` and clear the constant factors.
        -- We keep the algebraic normalization separate to avoid timeouts.
        have : (π * (t * Real.exp (-(π * ε) * t))) ≤
            (2 / ε) * Real.exp (-π * (ε / 2) * t) := by
          -- simplify the RHS constant and exponent
          -- `π * (2 / (π * ε)) = 2 / ε`
          -- `-((π*ε)/2)*t = -π*(ε/2)*t`
          simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv, hπne, hεne, mul_add, add_mul,
            sub_eq_add_neg, mul_neg, neg_mul, neg_add, add_assoc, add_left_comm, add_comm] using h1
        -- rewrite the LHS to match `(π*t) * exp(-π*ε*t)`
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      have hbase_nonneg : 0 ≤ ‖aAnotherBase t‖ := norm_nonneg _
      have hnorm_integrandC :
          ‖aAnotherIntegrandC z t‖ ≤ ‖aAnotherBase t‖ * Real.exp (-π * ε * t) := by
        have hmul := mul_le_mul_of_nonneg_left hExp hbase_nonneg
        simpa [aAnotherIntegrandC_eq, norm_mul, mul_assoc, mul_left_comm, mul_comm] using hmul
      have hlin_norm : ‖(-(π : ℂ) * (t : ℂ))‖ = π * t := by
        have : ‖(t : ℂ)‖ = |t| := by simp
        have htabs : |t| = t := abs_of_pos htpos
        -- `‖(π:ℂ)‖ = π` since `π > 0`.
        simp [htabs, Real.pi_pos.le]
      have hmul_trade :
          (π * t) * (‖aAnotherBase t‖ * Real.exp (-π * ε * t)) ≤
            (2 / ε) * (‖aAnotherBase t‖ * Real.exp (-π * (ε / 2) * t)) := by
        have hmul := mul_le_mul_of_nonneg_left hExpTrade hbase_nonneg
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      have hnorm_another :
          ‖aAnotherIntegrand (ε / 2) t‖ = ‖aAnotherBase t‖ * Real.exp (-π * (ε / 2) * t) := by
        rw [aAnotherIntegrand_eq (u := ε / 2) (t := t)]
        set r : ℝ := Real.exp (-π * (ε / 2) * t)
        have hr : 0 ≤ r := by
          simpa [r] using (Real.exp_nonneg (-π * (ε / 2) * t))
        -- Now `aAnotherIntegrand (ε/2) t = aAnotherBase t * (r : ℂ)`.
        calc
          ‖aAnotherBase t * (r : ℂ)‖
              = ‖aAnotherBase t‖ * ‖(r : ℂ)‖ := by simp
          _ = ‖aAnotherBase t‖ * r := by
                -- Rewrite `‖(r : ℂ)‖` using `hr`.
                exact congrArg (fun x => ‖aAnotherBase t‖ * x) (Complex.norm_of_nonneg hr)
          _ = ‖aAnotherBase t‖ * Real.exp (-π * (ε / 2) * t) := by
                simp [r]
      calc
        ‖(-(π : ℂ) * (t : ℂ)) * aAnotherIntegrandC z t‖
            = ‖(-(π : ℂ) * (t : ℂ))‖ * ‖aAnotherIntegrandC z t‖ := by simp
        _ ≤ (π * t) * ‖aAnotherIntegrandC z t‖ := by
          -- Avoid `simp` rewriting `‖(-π) * t‖` via `norm_mul` before `hlin_norm` can fire.
          rw [hlin_norm]
        _ ≤ (π * t) * (‖aAnotherBase t‖ * Real.exp (-π * ε * t)) := by
          have hπt : 0 ≤ (π * t : ℝ) := by
            have hπ : 0 < (π : ℝ) := Real.pi_pos
            nlinarith [hπ, ht0]
          exact mul_le_mul_of_nonneg_left hnorm_integrandC hπt
        _ ≤ (2 / ε) * (‖aAnotherBase t‖ * Real.exp (-π * (ε / 2) * t)) := hmul_trade
        _ = bound t := by
          simp [bound, hnorm_another]
    have hdiff :
        ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball u ε,
          HasDerivAt (fun w : ℂ => aAnotherIntegrandC w t)
            ((-(π : ℂ) * (t : ℂ)) * aAnotherIntegrandC z t) z := by
      refine (Filter.Eventually.of_forall fun t => ?_)
      intro z _hz
      -- Differentiate the exponential factor; the remaining part is constant in `w`.
      have hlin :
          HasDerivAt (fun w : ℂ => (-(π : ℂ) * w * (t : ℂ))) (-(π : ℂ) * (t : ℂ)) z := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          ((hasDerivAt_id z).const_mul (-(π : ℂ) * (t : ℂ)))
      have hexp :
          HasDerivAt (fun w : ℂ => Complex.exp (-(π : ℂ) * w * (t : ℂ)))
            (Complex.exp (-(π : ℂ) * z * (t : ℂ)) * (-(π : ℂ) * (t : ℂ))) z := by
        simpa using hlin.cexp
      have hbaseConst :
          HasDerivAt (fun w : ℂ => aAnotherBase t * Complex.exp (-(π : ℂ) * w * (t : ℂ)))
            (aAnotherBase t *
                (Complex.exp (-(π : ℂ) * z * (t : ℂ)) * (-(π : ℂ) * (t : ℂ)))) z := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using (hexp.const_mul (aAnotherBase t))
      simpa [aAnotherIntegrandC, mul_assoc, mul_left_comm, mul_comm] using hbaseConst
    have hDerivCore :
        HasDerivAt (fun z : ℂ => ∫ t, aAnotherIntegrandC z t ∂μ)
          (∫ t, (-(π : ℂ) * (t : ℂ)) * aAnotherIntegrandC u t ∂μ) u := by
      refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
        (s := Metric.ball u ε) (hs := Metric.ball_mem_nhds u hε) (x₀ := u)
        (F := fun z t => aAnotherIntegrandC z t)
        (F' := fun z t => (-(π : ℂ) * (t : ℂ)) * aAnotherIntegrandC z t)
        (bound := bound) (hF_meas := hF_meas') (hF_int := hF_int) (hF'_meas := hF'_meas_u)
        (h_bound := hbound) (bound_integrable := hbound_int) (h_diff := hdiff)).2
    have hDeriv :
        HasDerivAt aAnotherIntegralC
          (∫ t in Set.Ioi (0 : ℝ), (-(π : ℂ) * (t : ℂ)) * aAnotherIntegrandC u t) u := by
      assumption
    exact hDeriv.differentiableAt.differentiableWithinAt
  exact hDiff.analyticOnNhd rightHalfPlane_isOpen

end

end MagicFunction.g.CohnElkies.IntegralReps
