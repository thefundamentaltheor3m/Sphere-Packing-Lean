module

import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import SpherePacking.Integration.UpperHalfPlaneComp
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
  have hpow : ‖coeff t‖ ^ n ≤ C ^ n := pow_le_pow_left₀ (norm_nonneg _) hcoeff n
  calc
    ‖(coeff t) ^ n * g r t‖ = ‖coeff t‖ ^ n * ‖g r t‖ := by simp [norm_pow]
    _ ≤ C ^ n * G := by
      exact mul_le_mul hpow hg (norm_nonneg _) (pow_nonneg hC _)

/--
If `‖f t‖` is uniformly bounded on `Ioo (0, 1)`, then the set integral over `Ioo (0, 1)` is also
bounded.
-/
public lemma norm_setIntegral_Ioo01_le_of_norm_le_const {f : ℝ → ℂ} {C : ℝ}
    (hs : (volume : Measure ℝ) (Ioo (0 : ℝ) 1) < ⊤) (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ‖f t‖ ≤ C) :
    ‖∫ t in Ioo (0 : ℝ) 1, f t‖ ≤ C := by
  have h :=
    norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ)) (f := f) (s := Ioo (0 : ℝ) 1)
      hs hbd
  simpa [mul_assoc, mul_left_comm, mul_comm,
    volume_real_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)] using h

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
  refine ⟨(2 * π) ^ n * (C₀ * rexp (-π) * 2), by positivity, ?_⟩
  intro r
  have hrepr_r := congrArg (fun f : ℝ → ℂ ↦ f r) hrepr
  have hs : (volume : Measure ℝ) (Ioo (0 : ℝ) 1) < ⊤ := measure_Ioo_lt_top
  have hbd : ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖(coeff t) ^ n * g r t‖ ≤ ((2 * π) ^ n * (C₀ * rexp (-π) * 2)) * rexp (-π * r) := by
    intro t ht
    have hcoeff' : ‖coeff t‖ ≤ 2 * π := hcoeff t ht
    have hg' : ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r) := hC₀ r t ht
    have h :=
      norm_pow_mul_mul_le (coeff := coeff) (g := g) (C := 2 * π)
        (G := C₀ * rexp (-π) * 2 * rexp (-π * r)) (n := n) (r := r) (t := t) (by positivity)
        hcoeff' hg'
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hInt :
      ‖∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ n * g r t‖ ≤
        ((2 * π) ^ n * (C₀ * rexp (-π) * 2)) * rexp (-π * r) :=
    norm_setIntegral_Ioo01_le_of_norm_le_const (f := fun t ↦ (coeff t) ^ n * g r t) hs hbd
  simpa [hrepr_r] using hInt

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
  let M : ℝ := (2 * π) ^ n * (C₀ * rexp (-π) * 2) * rexp (-π * r)
  have hbd : ∀ᵐ t ∂μ, ‖(coeff t) ^ n * g r t‖ ≤ M := by
    filter_upwards [hmem] with t ht
    have hcoeff' : ‖coeff t‖ ≤ 2 * π := hcoeff t ht
    have hg' : ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r) := hC₀ r t ht
    have h :=
      norm_pow_mul_mul_le (coeff := coeff) (g := g) (C := 2 * π)
        (G := C₀ * rexp (-π) * 2 * rexp (-π * r)) (n := n) (r := r) (t := t) (by positivity)
        hcoeff' hg'
    simpa [M, mul_assoc, mul_left_comm, mul_comm] using h
  have : IntegrableOn (fun t : ℝ ↦ (coeff t) ^ n * g r t) (Set.univ : Set ℝ) μ :=
    Measure.integrableOn_of_bounded (μ := μ) (s := (Set.univ : Set ℝ)) hμ_ne hmeas (by
      simpa using hbd)
  simpa [IntegrableOn] using this

/--
Specialization of `integrable_pow_mul_of_ae_mem_Ioo01` to `volume.restrict (Ioo (0, 1))`.
-/
public lemma integrable_pow_mul_of_volume_restrict_Ioo01 {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ}
    {n : ℕ} {r : ℝ}
    (hmeas :
      AEStronglyMeasurable (fun t : ℝ ↦ (coeff t) ^ n * g r t)
        ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)))
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hg :
      ∃ C₀ > 0, ∀ r : ℝ, ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
        ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r)) :
    Integrable (fun t : ℝ ↦ (coeff t) ^ n * g r t)
      ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)
  have hμ_ne : μ univ ≠ ⊤ := by
    have hμ_fin : μ univ < ⊤ := by
      have hμ_univ :
          μ univ = (volume : Measure ℝ) (Ioo (0 : ℝ) 1) := by
        simp [μ, Measure.restrict_apply, MeasurableSet.univ]
      rw [hμ_univ]
      exact (measure_Ioo_lt_top (a := (0 : ℝ)) (b := (1 : ℝ)))
    exact ne_of_lt hμ_fin
  have hmem : ∀ᵐ t ∂μ, t ∈ Ioo (0 : ℝ) 1 := by
    simpa [μ] using
      (ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Ioo (0 : ℝ) 1) measurableSet_Ioo)
  simpa [μ] using
    (integrable_pow_mul_of_ae_mem_Ioo01 (μ := μ) (coeff := coeff) (g := g) (n := n) (r := r)
      hμ_ne (by simpa [μ] using hmeas) hmem hcoeff hg)

/--
For `r` in a unit ball around `r₀`, compare `rexp (-π * r)` to `rexp (-π * r₀)` up to a factor
`rexp π`.
-/
public lemma rexp_neg_pi_mul_le_rexp_pi_mul_rexp_neg_pi_mul_of_mem_ball {r r₀ : ℝ}
    (hr : r ∈ Metric.ball r₀ (1 : ℝ)) :
    rexp (-π * r) ≤ rexp (π) * rexp (-π * r₀) := by
  have hr_lower : r₀ - 1 ≤ r := by
    have : |r - r₀| < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hr
    nlinarith [abs_lt.1 this |>.1]
  have : (-π * r : ℝ) ≤ π + (-π * r₀) := by
    nlinarith [Real.pi_pos, hr_lower]
  simpa [Real.exp_add] using (Real.exp_le_exp.2 this)

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
  refine (ae_restrict_iff' measurableSet_Ioo).2 <| .of_forall ?_
  intro t ht r hr
  have hC : 0 ≤ (2 * π : ℝ) := by positivity
  have hcoeff' : ‖coeff t‖ ≤ 2 * π := hcoeff t ht
  have hg' : ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r) := hg r t ht
  have hexp : rexp (-π * r) ≤ rexp (π) * rexp (-π * r₀) :=
    rexp_neg_pi_mul_le_rexp_pi_mul_rexp_neg_pi_mul_of_mem_ball (r := r) (r₀ := r₀) hr
  have h0 :
      ‖(coeff t) ^ n * g r t‖ ≤ (2 * π) ^ n * (C₀ * rexp (-π) * 2 * rexp (-π * r)) :=
    (norm_pow_mul_mul_le (coeff := coeff) (g := g) (C := 2 * π)
      (G := C₀ * rexp (-π) * 2 * rexp (-π * r)) (n := n) (r := r) (t := t)
      hC hcoeff' hg')
  have h1 :
      (2 * π) ^ n * (C₀ * rexp (-π) * 2 * rexp (-π * r)) ≤
        (2 * π) ^ n * (C₀ * rexp (-π) * 2) * rexp (π) * rexp (-π * r₀) := by
    have hC₀' : 0 ≤ C₀ * rexp (-π) * 2 := by positivity
    have hG :
        C₀ * rexp (-π) * 2 * rexp (-π * r) ≤
          C₀ * rexp (-π) * 2 * (rexp (π) * rexp (-π * r₀)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using (mul_le_mul_of_nonneg_left hexp hC₀')
    have hmul := mul_le_mul_of_nonneg_left hG (by positivity : (0 : ℝ) ≤ (2 * π) ^ n)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  exact h0.trans h1

/--
Differentiate `x ↦ ∫ gN n x t` under the integral sign using a dominated bound on a ball of radius
`1` around `x₀`.
-/
public lemma hasDerivAt_integral_gN_of_dominated_ball_one
    {μ : Measure ℝ} {gN : ℕ → ℝ → ℝ → ℂ} {n : ℕ} {x₀ C : ℝ}
    (hmeas : ∀ n : ℕ, ∀ x : ℝ, AEStronglyMeasurable (gN n x) μ)
    (hint : ∀ n : ℕ, ∀ x : ℝ, Integrable (gN n x) μ)
    (h_bound : ∀ᵐ t ∂μ, ∀ x ∈ Metric.ball x₀ (1 : ℝ), ‖gN (n + 1) x t‖ ≤ C)
    (hC_int : Integrable (fun _ : ℝ ↦ C) μ)
  (h_diff :
      ∀ᵐ t ∂μ, ∀ x ∈ Metric.ball x₀ (1 : ℝ),
        HasDerivAt (fun x : ℝ ↦ gN n x t) (gN (n + 1) x t) x) :
    HasDerivAt (fun x : ℝ ↦ ∫ t, gN n x t ∂μ) (∫ t, gN (n + 1) x₀ t ∂μ) x₀ := by
  have hF_meas : ∀ᶠ x in nhds x₀, AEStronglyMeasurable (gN n x) μ :=
    Eventually.of_forall (fun x ↦ hmeas n x)
  have hF_int : Integrable (gN n x₀) μ := hint n x₀
  have hF'_meas : AEStronglyMeasurable (gN (n + 1) x₀) μ := hmeas (n + 1) x₀
  simpa using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun x t ↦ gN n x t) (x₀ := x₀) (s := Metric.ball x₀ (1 : ℝ))
      (hs := by simpa using Metric.ball_mem_nhds x₀ (by norm_num))
      (hF_meas := hF_meas) (hF_int := hF_int)
      (hF'_meas := hF'_meas) (h_bound := h_bound) (bound_integrable := hC_int)
      (h_diff := h_diff)).2

/--
Differentiate `x ↦ ∫ (coeff t) ^ n * g x t` under the integral sign, assuming a uniform bound on
`g` on `Ioo (0, 1)` and a representation `g x t = A t * cexp ((x : ℂ) * coeff t)`.
-/
public lemma hasDerivAt_integral_pow_mul_of_uniform_bound_ball_one
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ} {A : ℝ → ℂ} {n : ℕ} {x₀ : ℝ}
    (hμ : μ = (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1))
    (hg_bound :
      ∃ C₀ > 0, ∀ r : ℝ, ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
        ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r))
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hg_repr : ∀ r t, g r t = A t * cexp ((r : ℂ) * coeff t))
    (hmeas :
      ∀ n : ℕ, ∀ x : ℝ,
        AEStronglyMeasurable (fun t : ℝ ↦ (coeff t) ^ n * g x t) μ)
    (hint :
      ∀ n : ℕ, ∀ x : ℝ, Integrable (fun t : ℝ ↦ (coeff t) ^ n * g x t) μ) :
    HasDerivAt (fun x : ℝ ↦ ∫ t, (coeff t) ^ n * g x t ∂μ)
      (∫ t, (coeff t) ^ (n + 1) * g x₀ t ∂μ) x₀ := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := hg_bound
  let K : ℝ := (2 * π) ^ (n + 1) * (C₀ * rexp (-π) * 2) * rexp (π) * rexp (-π * x₀)
  have h_bound :
      ∀ᵐ t ∂μ, ∀ x ∈ Metric.ball x₀ (1 : ℝ),
        ‖(coeff t) ^ (n + 1) * g x t‖ ≤ K := by
    simpa [hμ, K, mul_assoc, mul_left_comm, mul_comm] using
      (ae_forall_mem_ball_norm_pow_mul_mul_le (coeff := coeff) (g := g) (n := n + 1) (r₀ := x₀)
        (C₀ := C₀) (hC₀ := hC₀_pos.le) (hcoeff := hcoeff) (hg := fun r t ht => hC₀ r t ht))
  have hK_int : Integrable (fun _ : ℝ ↦ K) μ := integrable_const K
  have h_diff :
      ∀ᵐ t ∂μ, ∀ x ∈ Metric.ball x₀ (1 : ℝ),
        HasDerivAt (fun x : ℝ ↦ (coeff t) ^ n * g x t) ((coeff t) ^ (n + 1) * g x t) x := by
    refine ae_of_all _ (fun t x _hx => ?_)
    have hg_fun (y : ℝ) : g y t = A t * cexp ((y : ℂ) * coeff t) := hg_repr y t
    simpa [hg_fun, mul_assoc, mul_left_comm, mul_comm] using
      (SpherePacking.ForMathlib.hasDerivAt_pow_mul_mul_cexp_ofReal_mul_const
        (a := A t) (c := coeff t) (n := n) (x := x))
  simpa [K] using
    (hasDerivAt_integral_gN_of_dominated_ball_one (μ := μ)
      (gN := fun n x t ↦ (coeff t) ^ n * g x t) (n := n) (x₀ := x₀) (C := K)
      hmeas hint h_bound hK_int h_diff)

/--
Variant of `hasDerivAt_integral_pow_mul_of_uniform_bound_ball_one` for set integrals over
`Ioo (0, 1)`.
-/
public lemma hasDerivAt_setIntegral_pow_mul_of_uniform_bound_ball_one
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ} {A : ℝ → ℂ} {n : ℕ} {x₀ : ℝ}
    (hμ : μ = (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1))
    (hg_bound :
      ∃ C₀ > 0, ∀ r : ℝ, ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
        ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r))
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hg_repr : ∀ r t, g r t = A t * cexp ((r : ℂ) * coeff t))
    (hmeas :
      ∀ n : ℕ, ∀ x : ℝ,
        AEStronglyMeasurable (fun t : ℝ ↦ (coeff t) ^ n * g x t) μ)
    (hint :
      ∀ n : ℕ, ∀ x : ℝ, Integrable (fun t : ℝ ↦ (coeff t) ^ n * g x t) μ) :
    HasDerivAt (fun x : ℝ ↦ ∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ n * g x t)
      (∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ (n + 1) * g x₀ t) x₀ := by
  simpa [hμ] using
    (hasDerivAt_integral_pow_mul_of_uniform_bound_ball_one (μ := μ) (coeff := coeff) (g := g)
      (A := A) (n := n) (x₀ := x₀) hμ hg_bound hcoeff hg_repr hmeas hint)

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
  intro n
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)
  haveI : IsFiniteMeasure μ := by
    simpa [μ] using
      (inferInstance :
        IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)))
  have hmeas (n : ℕ) (r : ℝ) :
      AEStronglyMeasurable (fun t : ℝ ↦ (coeff t) ^ n * g r t) μ := by
    have hcoeff_contOn : ContinuousOn (fun t : ℝ ↦ (coeff t) ^ n) (Ioo (0 : ℝ) 1) :=
      (hcoeff_cont.pow n).continuousOn
    have hmul : ContinuousOn (fun t : ℝ ↦ (coeff t) ^ n * g r t) (Ioo (0 : ℝ) 1) :=
      hcoeff_contOn.mul (hg_cont r)
    -- `ContinuousOn.aestronglyMeasurable` is phrased as measurability for `volume.restrict`,
    -- so we `simpa` to our `μ`.
    simpa [μ] using (ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ)) hmul
      measurableSet_Ioo)
  have hint (n : ℕ) (r : ℝ) :
      Integrable (fun t : ℝ ↦ (coeff t) ^ n * g r t) μ := by
    simpa [μ] using
      (integrable_pow_mul_of_volume_restrict_Ioo01 (coeff := coeff) (g := g) (n := n) (r := r)
        (hmeas := by simpa [μ] using hmeas n r) hcoeff hg_bound)
  have hasDerivAt_integral_gN (n : ℕ) (r₀ : ℝ) :
      HasDerivAt (fun r : ℝ ↦ ∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ n * g r t)
        (∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ (n + 1) * g r₀ t) r₀ := by
    simpa [μ] using
      (hasDerivAt_setIntegral_pow_mul_of_uniform_bound_ball_one (μ := μ) (coeff := coeff) (g := g)
        (A := A) (n := n) (x₀ := r₀) (hμ := rfl) (hg_bound := hg_bound) (hcoeff := hcoeff)
        (hg_repr := hg_repr) (hmeas := fun n r => by simpa [μ] using hmeas n r)
        (hint := fun n r => by simpa [μ] using hint n r))
  induction n with
  | zero =>
    funext r
    simp [hI]
  | succ n hn =>
    funext r
    have hder :
        deriv (fun r : ℝ ↦ ∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ n * g r t) r =
          ∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ (n + 1) * g r t :=
      (hasDerivAt_integral_gN n r).deriv
    simp [iteratedDeriv_succ, hn, hder]

end MagicFunction.a.IntegralEstimates
