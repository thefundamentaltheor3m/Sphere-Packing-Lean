module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Basic
public import SpherePacking.Integration.UpperHalfPlaneComp
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Instances.Real.Lemmas
import SpherePacking.ForMathlib.DerivHelpers

/-!
# Auxiliary bounds on integrals over `(0, 1)`

This file collects reusable lemmas used in the `IntegralEstimates` development for integrals over
`Ioo (0, 1)`. It includes basic norm and monotonicity estimates for set integrals, as well as
lemmas that justify differentiating under the integral sign for integrands of the form
`(coeff t) ^ n * g r t`.

## Main statements
* `bounding_of_eq_integral_g_Ioo01`, `bounding_uniform_of_eq_integral_g_Ioo01`
* `iteratedDeriv_bound_of_iteratedDeriv_eq_integral_pow_mul`
* `iteratedDeriv_eq_setIntegral_pow_mul_of_uniform_bound_ball_one`
-/

open Complex Real Set MeasureTheory Filter intervalIntegral

namespace MagicFunction.a.IntegralEstimates

/-- Bound `‖(coeff t) ^ n * g r t‖` from bounds on `‖coeff t‖` and `‖g r t‖`. -/
public lemma norm_pow_mul_mul_le {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ} {C G : ℝ} {n : ℕ} {r t : ℝ}
    (hC : 0 ≤ C) (hcoeff : ‖coeff t‖ ≤ C) (hg : ‖g r t‖ ≤ G) :
    ‖(coeff t) ^ n * g r t‖ ≤ C ^ n * G := by
  simpa [norm_mul, norm_pow] using
    mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hcoeff n) hg (norm_nonneg _) (pow_nonneg hC _)

/--
Bound `iteratedDeriv n I` when it is represented as a set integral of `(coeff t) ^ n * g r t` with
uniform bounds on `g` and `coeff`.
-/
public lemma iteratedDeriv_bound_of_iteratedDeriv_eq_integral_pow_mul
    {I : ℝ → ℂ} {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ} (n : ℕ)
    (hg_bound :
      ∃ C₀ > 0, ∀ r : ℝ, ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
        ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r))
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hrepr :
      iteratedDeriv n I =
        fun r : ℝ ↦ ∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ n * g r t) :
    ∃ C₁ > 0, ∀ r : ℝ, ‖iteratedDeriv n I r‖ ≤ C₁ * rexp (-π * r) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := hg_bound
  refine ⟨(2 * π) ^ n * (C₀ * rexp (-π) * 2), by positivity, fun r => ?_⟩
  simpa [congrArg (fun f : ℝ → ℂ ↦ f r) hrepr, volume_real_Ioo_of_le zero_le_one] using
    norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (0 : ℝ) 1)
      (f := fun t ↦ (coeff t) ^ n * g r t) measure_Ioo_lt_top fun t ht => by
        simpa [mul_assoc, mul_left_comm, mul_comm] using norm_pow_mul_mul_le (n := n)
          (G := C₀ * rexp (-π) * 2 * rexp (-π * r)) (by positivity) (hcoeff t ht) (hC₀ r t ht)

/--
Integrability of `(coeff t) ^ n * g r t` from a uniform bound on `coeff` and a uniform (in `r`)
bound on `g`, assuming `μ` is finite and the integrand is supported on `Ioo (0, 1)` almost
everywhere.
-/
public lemma integrable_pow_mul_of_ae_mem_Ioo01 {μ : Measure ℝ} {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ}
    {n : ℕ} {r : ℝ}
    (hμ_ne : μ univ ≠ ⊤)
    (hmeas : AEStronglyMeasurable (fun t : ℝ ↦ (coeff t) ^ n * g r t) μ)
    (hmem : ∀ᵐ t ∂μ, t ∈ Ioo (0 : ℝ) 1)
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hg :
      ∃ C₀ > 0, ∀ r : ℝ, ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
        ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r)) :
    Integrable (fun t : ℝ ↦ (coeff t) ^ n * g r t) μ := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := hg
  have hbd : ∀ᵐ t ∂μ,
      ‖(coeff t) ^ n * g r t‖ ≤ (2 * π) ^ n * (C₀ * rexp (-π) * 2) * rexp (-π * r) := by
    filter_upwards [hmem] with t ht
    simpa [mul_assoc, mul_left_comm, mul_comm] using norm_pow_mul_mul_le
      (G := C₀ * rexp (-π) * 2 * rexp (-π * r)) (n := n) (by positivity) (hcoeff t ht) (hC₀ r t ht)
  simpa [IntegrableOn] using
    Measure.integrableOn_of_bounded (s := Set.univ) hμ_ne hmeas (by simpa using hbd)

/-- Specialization of `integrable_pow_mul_of_ae_mem_Ioo01` to `volume.restrict (Ioo (0, 1))`. -/
public lemma integrable_pow_mul_of_volume_restrict_Ioo01 {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ}
    {n : ℕ} {r : ℝ}
    (hmeas : AEStronglyMeasurable (fun t : ℝ ↦ (coeff t) ^ n * g r t)
      ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)))
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hg : ∃ C₀ > 0, ∀ r : ℝ, ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r)) :
    Integrable (fun t : ℝ ↦ (coeff t) ^ n * g r t)
      ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) :=
  integrable_pow_mul_of_ae_mem_Ioo01 (measure_ne_top _ univ) hmeas
    (ae_restrict_mem measurableSet_Ioo) hcoeff hg

/--
For `r` in a unit ball around `r₀`, compare `rexp (-π * r)` to `rexp (-π * r₀)` up to a factor
`rexp π`.
-/
public lemma rexp_neg_pi_mul_le_rexp_pi_mul_rexp_neg_pi_mul_of_mem_ball {r r₀ : ℝ}
    (hr : r ∈ Metric.ball r₀ (1 : ℝ)) :
    rexp (-π * r) ≤ rexp (π) * rexp (-π * r₀) := by
  have : |r - r₀| < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hr
  simpa [Real.exp_add] using Real.exp_le_exp.2
    (by nlinarith [Real.pi_pos, abs_lt.1 this |>.1] : (-π * r : ℝ) ≤ π + (-π * r₀))

/--
Almost-everywhere bound for `‖(coeff t) ^ n * g r t‖` which is uniform in `r` on `Metric.ball r₀ 1`.
-/
public lemma ae_forall_mem_ball_norm_pow_mul_mul_le {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ}
    (n : ℕ) (r₀ C₀ : ℝ)
    (hC₀ : 0 ≤ C₀)
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hg :
      ∀ r : ℝ, ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
        ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r)) :
    ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)), ∀ r ∈ Metric.ball r₀ (1 : ℝ),
      ‖(coeff t) ^ n * g r t‖ ≤
        (2 * π) ^ n * (C₀ * rexp (-π) * 2) * rexp (π) * rexp (-π * r₀) := by
  refine (ae_restrict_iff' measurableSet_Ioo).2 <| .of_forall fun t ht r hr => ?_
  refine (norm_pow_mul_mul_le (G := C₀ * rexp (-π) * 2 * rexp (-π * r)) (n := n)
    (by positivity) (hcoeff t ht) (hg r t ht)).trans ?_
  simpa [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left
    (rexp_neg_pi_mul_le_rexp_pi_mul_rexp_neg_pi_mul_of_mem_ball hr)
    (by positivity : (0 : ℝ) ≤ (2 * π) ^ n * (C₀ * rexp (-π) * 2))

/--
Differentiate `x ↦ ∫ (coeff t) ^ n * g x t` under the integral sign, assuming a uniform bound on
`g` on `Ioo (0, 1)` and a representation `g x t = A t * cexp ((x : ℂ) * coeff t)`.
-/
public lemma hasDerivAt_integral_pow_mul_of_uniform_bound_ball_one
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ} {A : ℝ → ℂ} {n : ℕ} {x₀ : ℝ}
    (hμ : μ = (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1))
    (hg_bound : ∃ C₀ > 0, ∀ r : ℝ, ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r))
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hg_repr : ∀ r t, g r t = A t * cexp ((r : ℂ) * coeff t))
    (hmeas : ∀ n : ℕ, ∀ x : ℝ,
      AEStronglyMeasurable (fun t : ℝ ↦ (coeff t) ^ n * g x t) μ)
    (hint : ∀ n : ℕ, ∀ x : ℝ, Integrable (fun t : ℝ ↦ (coeff t) ^ n * g x t) μ) :
    HasDerivAt (fun x : ℝ ↦ ∫ t, (coeff t) ^ n * g x t ∂μ)
      (∫ t, (coeff t) ^ (n + 1) * g x₀ t ∂μ) x₀ := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := hg_bound
  let K : ℝ := (2 * π) ^ (n + 1) * (C₀ * rexp (-π) * 2) * rexp (π) * rexp (-π * x₀)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := x₀)
    (s := Metric.ball x₀ 1) (Metric.ball_mem_nhds x₀ one_pos) (.of_forall (hmeas n))
    (hint n x₀) (hmeas (n + 1) x₀)
    (show ∀ᵐ t ∂μ, ∀ x ∈ Metric.ball x₀ (1 : ℝ), ‖(coeff t) ^ (n + 1) * g x t‖ ≤ K by
      simpa [hμ, K, mul_assoc, mul_left_comm, mul_comm] using
        ae_forall_mem_ball_norm_pow_mul_mul_le (n := n + 1) (r₀ := x₀) (C₀ := C₀)
          hC₀_pos.le hcoeff hC₀)
    (integrable_const K) <| ae_of_all _ fun t x _hx => by
      simpa [hg_repr, mul_assoc, mul_left_comm, mul_comm] using
        SpherePacking.ForMathlib.hasDerivAt_pow_mul_mul_cexp_ofReal_mul_const
          (a := A t) (c := coeff t) (n := n) (x := x)).2

/--
Express iterated derivatives of `I` as set integrals of `(coeff t) ^ n * g r t`, under uniform
bounds that allow differentiation under the integral sign.
-/
public lemma iteratedDeriv_eq_setIntegral_pow_mul_of_uniform_bound_ball_one
    {I : ℝ → ℂ} {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ} {A : ℝ → ℂ}
    (hI : ∀ r : ℝ, I r = ∫ t in Ioo (0 : ℝ) 1, g r t)
    (hcoeff_cont : Continuous coeff)
    (hg_cont : ∀ r : ℝ, ContinuousOn (g r) (Ioo (0 : ℝ) 1))
    (hg_bound :
      ∃ C₀ > 0, ∀ r : ℝ, ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
        ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r))
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hg_repr : ∀ r t, g r t = A t * cexp ((r : ℂ) * coeff t)) :
    ∀ n : ℕ, iteratedDeriv n I = fun r : ℝ ↦ ∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ n * g r t := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict_Ioo 0 1
  have hmeas (n : ℕ) (r : ℝ) :
      AEStronglyMeasurable (fun t : ℝ ↦ (coeff t) ^ n * g r t) μ := by
    simpa [μ] using ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ))
      ((hcoeff_cont.pow n).continuousOn.mul (hg_cont r)) measurableSet_Ioo
  have hint (n : ℕ) (r : ℝ) : Integrable (fun t : ℝ ↦ (coeff t) ^ n * g r t) μ :=
    integrable_pow_mul_of_volume_restrict_Ioo01 (hmeas n r) hcoeff hg_bound
  intro n
  induction n with
  | zero => funext r; simp [hI]
  | succ n hn => funext r; simp [iteratedDeriv_succ, hn,
      (show HasDerivAt (fun x : ℝ ↦ ∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ n * g x t)
            (∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ (n + 1) * g r t) r from by
        simpa [μ] using hasDerivAt_integral_pow_mul_of_uniform_bound_ball_one (μ := μ)
          (n := n) (x₀ := r) rfl hg_bound hcoeff hg_repr hmeas hint).deriv]

end MagicFunction.a.IntegralEstimates
