/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/
module

public import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.Basic
public import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.RealDeriv
public import SpherePacking.Integration.Measure
public import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Instances.Real.Lemmas
import SpherePacking.ForMathlib.DerivHelpers

/-! # Bounds for `I₂'` and `I₄'`: representation, uniform exponential bound, and Schwartz decay.

Also contains elementary exponential bounds and auxiliary integral bounds (originally in
`PowExpBounds`):
* Auxiliary bounds on integrals over `(0, 1)` for integrands `(coeff t) ^ n * g r t`;
* Elementary exponential bounds packaged as Schwartz decay lemmas;
* Common skeleton for `I₂'`/`I₄'` integral estimates (namespace `I24Common`).
-/

open scoped Topology
open Complex Real Set MeasureTheory Filter intervalIntegral

namespace MagicFunction.a.IntegralEstimates

/-- Bound `‖(coeff t) ^ n * g r t‖` from bounds on `‖coeff t‖` and `‖g r t‖`. -/
public lemma norm_pow_mul_mul_le {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ} {C G : ℝ} {n : ℕ} {r t : ℝ}
    (hC : 0 ≤ C) (hcoeff : ‖coeff t‖ ≤ C) (hg : ‖g r t‖ ≤ G) :
    ‖(coeff t) ^ n * g r t‖ ≤ C ^ n * G := by
  simpa [norm_mul, norm_pow] using
    mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hcoeff n) hg (norm_nonneg _) (pow_nonneg hC _)

/-- Bound `iteratedDeriv n I` from a set-integral representation with uniform bounds. -/
public lemma iteratedDeriv_bound_of_iteratedDeriv_eq_integral_pow_mul
    {I : ℝ → ℂ} {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ} (n : ℕ)
    (hg_bound : ∃ C₀ > 0, ∀ r : ℝ, ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r))
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hrepr : iteratedDeriv n I = fun r : ℝ ↦ ∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ n * g r t) :
    ∃ C₁ > 0, ∀ r : ℝ, ‖iteratedDeriv n I r‖ ≤ C₁ * rexp (-π * r) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := hg_bound
  refine ⟨(2 * π) ^ n * (C₀ * rexp (-π) * 2), by positivity, fun r ↦ ?_⟩
  simpa [congrArg (fun f : ℝ → ℂ ↦ f r) hrepr, volume_real_Ioo_of_le zero_le_one] using
    norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (0 : ℝ) 1)
      (f := fun t ↦ (coeff t) ^ n * g r t) measure_Ioo_lt_top fun t ht ↦ by
        simpa [mul_assoc, mul_left_comm, mul_comm] using norm_pow_mul_mul_le (n := n)
          (G := C₀ * rexp (-π) * 2 * rexp (-π * r)) (by positivity) (hcoeff t ht) (hC₀ r t ht)

/-- Integrability of `(coeff t) ^ n * g r t` from uniform bounds, on `volume.restrict
`Ioo (0, 1)`. -/
public lemma integrable_pow_mul_of_volume_restrict_Ioo01 {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ}
    {n : ℕ} {r : ℝ}
    (hmeas : AEStronglyMeasurable (fun t : ℝ ↦ (coeff t) ^ n * g r t)
      ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)))
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hg : ∃ C₀ > 0, ∀ r : ℝ, ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r)) :
    Integrable (fun t : ℝ ↦ (coeff t) ^ n * g r t)
      ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) := by
  obtain ⟨C₀, _, hC₀⟩ := hg
  have hbd : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)),
      ‖(coeff t) ^ n * g r t‖ ≤ (2 * π) ^ n * (C₀ * rexp (-π) * 2) * rexp (-π * r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simpa [mul_assoc, mul_left_comm, mul_comm] using norm_pow_mul_mul_le
      (G := C₀ * rexp (-π) * 2 * rexp (-π * r)) (n := n) (by positivity) (hcoeff t ht) (hC₀ r t ht)
  simpa [IntegrableOn] using
    Measure.integrableOn_of_bounded (s := Set.univ) (measure_ne_top _ _) hmeas (by simpa using hbd)

/-- Differentiate `x ↦ ∫ (coeff t) ^ n * g x t` under the integral, given uniform bounds on `g` and
the representation `g x t = A t * cexp ((x : ℂ) * coeff t)`. -/
public lemma hasDerivAt_integral_pow_mul_of_uniform_bound_ball_one
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ} {A : ℝ → ℂ} {n : ℕ} {x₀ : ℝ}
    (hμ : μ = (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1))
    (hg_bound : ∃ C₀ > 0, ∀ r : ℝ, ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r))
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hg_repr : ∀ r t, g r t = A t * cexp ((r : ℂ) * coeff t))
    (hmeas : ∀ n : ℕ, ∀ x : ℝ, AEStronglyMeasurable (fun t : ℝ ↦ (coeff t) ^ n * g x t) μ)
    (hint : ∀ n : ℕ, ∀ x : ℝ, Integrable (fun t : ℝ ↦ (coeff t) ^ n * g x t) μ) :
    HasDerivAt (fun x : ℝ ↦ ∫ t, (coeff t) ^ n * g x t ∂μ)
      (∫ t, (coeff t) ^ (n + 1) * g x₀ t ∂μ) x₀ := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := hg_bound
  let K : ℝ := (2 * π) ^ (n + 1) * (C₀ * rexp (-π) * 2) * rexp (π) * rexp (-π * x₀)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := x₀)
    (s := Metric.ball x₀ 1) (Metric.ball_mem_nhds x₀ one_pos) (.of_forall (hmeas n))
    (hint n x₀) (hmeas (n + 1) x₀)
    (show ∀ᵐ t ∂μ, ∀ x ∈ Metric.ball x₀ (1 : ℝ), ‖(coeff t) ^ (n + 1) * g x t‖ ≤ K from by
      rw [hμ]
      refine (ae_restrict_iff' measurableSet_Ioo).2 <| .of_forall fun t ht r hr ↦ ?_
      refine (norm_pow_mul_mul_le (G := C₀ * rexp (-π) * 2 * rexp (-π * r)) (n := n + 1)
        (by positivity) (hcoeff t ht) (hC₀ r t ht)).trans ?_
      simpa [K, mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left
        (show rexp (-π * r) ≤ rexp π * rexp (-π * x₀) by
          have : |r - x₀| < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hr
          simpa [Real.exp_add] using Real.exp_le_exp.2 (by
            nlinarith [Real.pi_pos, abs_lt.1 this |>.1] : (-π * r : ℝ) ≤ π + (-π * x₀)))
        (by positivity : (0 : ℝ) ≤ (2 * π) ^ (n + 1) * (C₀ * rexp (-π) * 2)))
    (integrable_const K) <| ae_of_all _ fun t x _hx ↦ by
      simpa [hg_repr, mul_assoc, mul_left_comm, mul_comm] using
        SpherePacking.ForMathlib.hasDerivAt_pow_mul_mul_cexp_ofReal_mul_const
          (a := A t) (c := coeff t) (n := n) (x := x)).2

/-- Express `iteratedDeriv n I` as a set integral of `(coeff t) ^ n * g r t` under suitable
uniform bounds. -/
public lemma iteratedDeriv_eq_setIntegral_pow_mul_of_uniform_bound_ball_one
    {I : ℝ → ℂ} {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ} {A : ℝ → ℂ}
    (hI : ∀ r : ℝ, I r = ∫ t in Ioo (0 : ℝ) 1, g r t)
    (hcoeff_cont : Continuous coeff)
    (hg_cont : ∀ r : ℝ, ContinuousOn (g r) (Ioo (0 : ℝ) 1))
    (hg_bound : ∃ C₀ > 0, ∀ r : ℝ, ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r))
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hg_repr : ∀ r t, g r t = A t * cexp ((r : ℂ) * coeff t)) :
    ∀ n : ℕ, iteratedDeriv n I = fun r : ℝ ↦ ∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ n * g r t := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict_Ioo 0 1
  have hmeas (n : ℕ) (r : ℝ) : AEStronglyMeasurable (fun t : ℝ ↦ (coeff t) ^ n * g r t) μ := by
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

/-- For each `k`, the function `x ↦ x ^ k * exp (-π * x)` is bounded on `[0, ∞)`. -/
public lemma pow_mul_exp_neg_pi_bounded (k : ℕ) :
    ∃ C, ∀ x : ℝ, 0 ≤ x → x ^ k * rexp (-π * x) ≤ C := by
  let f : ℝ → ℝ := fun x => x ^ k * rexp (-π * x)
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
      (tendsto_id.const_mul_atTop Real.pi_pos)
    have hpi0 : (π ^ k : ℝ) ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
    have hf : f = fun x : ℝ => (π ^ k)⁻¹ * ((π * x) ^ k * rexp (-(π * x))) := by
      funext x; simp [f, mul_assoc, mul_left_comm, mul_comm, mul_pow, hpi0]
    simpa [hf] using tendsto_const_nhds.mul h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 <|
    (hlim.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))).mono fun _ => le_of_lt
  set N0 : ℝ := max N 0
  obtain ⟨x0, _, hxmax⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) N0)).exists_isMaxOn
      (nonempty_Icc.2 (le_max_right N 0)) (by fun_prop : Continuous f).continuousOn
  refine ⟨max 1 (f x0), fun x hx => ?_⟩
  by_cases hxN : x ≤ N0
  · exact (hxmax ⟨hx, hxN⟩).trans (le_max_right _ _)
  · exact (hN x ((le_max_left N 0).trans (le_of_not_ge hxN))).trans (le_max_left _ _)

/-- Variant for iterated derivatives: a uniform exponential bound on `‖iteratedDeriv n I x‖`
implies Schwartz inverse-power decay. -/
public lemma decay_of_bounding_uniform_norm_iteratedDeriv {I : ℝ → ℂ} (n : ℕ)
    (hI : ∃ C₁ > 0, ∀ x : ℝ, 0 ≤ x → ‖iteratedDeriv n I x‖ ≤ C₁ * rexp (-π * x)) (k : ℕ) :
    ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I x‖ ≤ C := by
  obtain ⟨C₁, _, hC₁⟩ := hI
  obtain ⟨Cpow, hCpow⟩ := pow_mul_exp_neg_pi_bounded (k := k)
  refine ⟨C₁ * Cpow, fun x hx => ?_⟩
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I x‖
        ≤ ‖x‖ ^ k * (C₁ * rexp (-π * x)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ) (n := n) (f := I) (x := x)]
            using hC₁ x hx
    _ = C₁ * (x ^ k * rexp (-π * x)) := by
      simp [Real.norm_of_nonneg hx, mul_left_comm, mul_comm]
    _ ≤ C₁ * Cpow := by gcongr; exact hCpow x hx

/-- Schwartz decay from `iteratedDeriv n I = ∫ t ∈ (0,1), coeff t ^ n * g r t`. -/
public lemma decay_of_iteratedDeriv_eq_integral_pow_mul
    {I : ℝ → ℂ} {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ}
    (hg_bound :
      ∃ C₀ > 0, ∀ r : ℝ, ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
        ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r))
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hrepr :
      ∀ n : ℕ,
        iteratedDeriv n I = fun r : ℝ ↦ ∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ n * g r t) (k n : ℕ) :
    ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I x‖ ≤ C :=
  let ⟨C₁, hC₁_pos, hC₁⟩ :=
    iteratedDeriv_bound_of_iteratedDeriv_eq_integral_pow_mul (n := n) hg_bound hcoeff (hrepr n)
  decay_of_bounding_uniform_norm_iteratedDeriv (n := n) ⟨C₁, hC₁_pos, fun x _ => hC₁ x⟩ k

/-! ## Common skeleton for `I₂'`/`I₄'` integral estimates. -/

namespace I24Common

noncomputable section

open scoped Function UpperHalfPlane Topology Real Complex
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open MagicFunction.PolyFourierCoeffBound MagicFunction.a.ComplexIntegrands

/-- The common coefficient pattern `coeff t = (-π) + (π * I) * shift t`. -/
@[expose] public def coeff (shift : ℝ → ℂ) : ℝ → ℂ :=
  fun t : ℝ ↦ (-π : ℂ) + (π * I) * shift t

public lemma continuous_coeff {shift : ℝ → ℂ} (hshift : Continuous shift) :
    Continuous (coeff shift) :=
  continuous_const.add (continuous_const.mul hshift)

/-- Uniform bound `‖coeff t‖ ≤ 2π` on `Ioo (0, 1)` given `‖shift t‖ ≤ 1` there. -/
public lemma coeff_norm_le {shift : ℝ → ℂ} (hshift : ∀ t ∈ Ioo (0 : ℝ) 1, ‖shift t‖ ≤ 1) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) : ‖coeff shift t‖ ≤ 2 * π := by
  have hnorm : ‖(π * I : ℂ)‖ = π := by simp [abs_of_nonneg Real.pi_pos.le]
  calc
    ‖coeff shift t‖
        ≤ ‖(-π : ℂ)‖ + ‖(π * I : ℂ) * shift t‖ := norm_add_le _ _
    _ = π + π * ‖shift t‖ := by rw [norm_mul, hnorm]; simp [abs_of_nonneg Real.pi_pos.le]
    _ ≤ π + π * 1 := by gcongr; exact hshift t ht
    _ = 2 * π := by ring

/-- Uniform `‖g r t‖ ≤ C₀ * exp(-π) * 2 * exp(-π * r)` bound on `Ioo (0, 1)`. -/
public lemma g_norm_bound_uniform_of {g : ℝ → ℝ → ℂ} {mob : ℝ → ℂ}
    (haux : ∀ r : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ‖g r t‖ ≤ ‖φ₀'' (mob t)‖ * 2 * rexp (-π * r))
    (hmob_im : ∀ t ∈ Ioo (0 : ℝ) 1, (1 / 2 : ℝ) < (mob t).im) :
    ∃ C₀ > 0, ∀ r : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀_le
  refine ⟨C₀, hC₀_pos, fun r t ht ↦ (haux r t ht).trans ?_⟩
  gcongr
  have hpos : 0 < (mob t).im := one_half_pos.trans (hmob_im t ht)
  simpa [φ₀'', hpos] using
    norm_φ₀''_le_mul_exp_neg_pi_of_one_half_lt_im (C₀ := C₀) (hC₀_pos := hC₀_pos) (hC₀ := hC₀)
      (z := ⟨mob t, hpos⟩) (by simpa using hmob_im t ht)

end

end I24Common

end MagicFunction.a.IntegralEstimates

namespace MagicFunction.a.IntegralEstimates.I₂

open scoped Function UpperHalfPlane Topology Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral

variable (r : ℝ)

/-- The integrand on `Ioo (0, 1)` whose set integral is `I₂'`. -/
@[expose] public noncomputable def g (r t : ℝ) : ℂ :=
  φ₀'' (-1 / (t + I)) * (t + I) ^ 2 * cexp (-π * I * r) * cexp (π * I * r * t) * cexp (-π * r)

/-- Rewrite `I₂' r` as a set integral of `g r` over `Ioo (0, 1)`. -/
public lemma I₂'_eq_integral_g_Ioo (r : ℝ) : I₂' r = ∫ t in Ioo (0 : ℝ) 1, g r t := by
  simp [I₂'_eq, intervalIntegral_eq_integral_uIoc, zero_le_one, g, integral_Ioc_eq_integral_Ioo]

/-- A uniform lower bound on the imaginary part of the parametrisation `t ↦ -1 / (t + I)`. -/
public lemma im_parametrisation_lower : ∀ t ∈ Ioo (0 : ℝ) 1, 1 / 2 < (-1 / (↑t + I)).im :=
  fun t ht => by
    simpa [show (-1 / (↑t + I)).im = 1 / (t ^ 2 + 1) by
        simpa using SpherePacking.Integration.im_neg_one_div_ofReal_add_I (t := t)] using
      SpherePacking.Integration.one_half_lt_one_div_sq_add_one_of_mem_Ioo01 ht

/-- A uniform-in-`r` bound on the integrand `g r t` on `Ioo (0, 1)`. -/
public lemma g_norm_bound_uniform :
    ∃ C₀ > 0, ∀ r : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r) :=
  I24Common.g_norm_bound_uniform_of (fun r t ht => by
    rw [g, norm_mul, norm_mul, norm_mul, mul_assoc, mul_assoc, norm_mul]
    gcongr
    · rw [norm_pow, ← normSq_eq_norm_sq, normSq_apply, add_re, ofReal_re, I_re, add_zero, add_im,
        ofReal_im, I_im, zero_add, mul_one]
      nlinarith [ht.1, ht.2]
    · conv_rhs => rw [← one_mul (rexp _), ← one_mul (rexp _)]
      gcongr <;> apply le_of_eq
      · simpa [mul_assoc, mul_left_comm, mul_comm] using norm_exp_ofReal_mul_I (-π * r)
      · simpa [mul_assoc, mul_left_comm, mul_comm] using norm_exp_ofReal_mul_I (π * r * t)
      · rw [norm_exp]; norm_cast) im_parametrisation_lower

noncomputable section Schwartz_Decay

open SchwartzMap

/-- Specialization of `I24Common.coeff` to `shift = fun t => (t : ℂ) - 1`. -/
@[expose] public def coeff : ℝ → ℂ := I24Common.coeff (fun t => (t : ℂ) - 1)

public lemma continuous_coeff : Continuous coeff :=
  I24Common.continuous_coeff (Complex.continuous_ofReal.sub continuous_const)

public lemma coeff_eq_sum (t : ℝ) :
    coeff t = (-π * I : ℂ) + (π * I * (t : ℂ)) + (-π : ℂ) := by
  simp [coeff, I24Common.coeff, sub_eq_add_neg, mul_add, mul_assoc, add_left_comm, add_comm]

/-- The integrand for the `n`-th derivative, obtained by multiplying `g` by `(coeff t) ^ n`. -/
@[expose] public def gN (n : ℕ) (r t : ℝ) : ℂ := (coeff t) ^ n * g r t

public lemma coeff_norm_le (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ‖coeff t‖ ≤ 2 * π :=
  I24Common.coeff_norm_le (shift := fun t => (t : ℂ) - 1)
    (fun t ht => by
      change ‖((t : ℂ) - 1)‖ ≤ 1
      rw [show ((t : ℂ) - 1) = ((t - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
      exact (by grind only [= mem_Ioo, = abs.eq_1, = max_def] : |t - 1| ≤ 1)) t ht

public lemma exp_r_mul_coeff (r t : ℝ) :
    cexp ((r : ℂ) * coeff t) =
      cexp (-π * I * r) * cexp (π * I * r * t) * cexp (-π * r : ℂ) := by
  simp [coeff_eq_sum, Complex.exp_add, add_assoc, mul_assoc, mul_add, mul_left_comm, mul_comm]

/-- Schwartz-style decay estimate for the auxiliary integral `I₂'`. -/
public theorem decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₂' x‖ ≤ C :=
  MagicFunction.a.IntegralEstimates.decay_of_iteratedDeriv_eq_integral_pow_mul
    g_norm_bound_uniform coeff_norm_le
    (fun n => iteratedDeriv_eq_setIntegral_pow_mul_of_uniform_bound_ball_one
      (I := I₂') (coeff := coeff) (g := g) (A := fun t => φ₀'' (-1 / (t + I)) * (t + I) ^ 2)
      (hI := I₂'_eq_integral_g_Ioo) (hcoeff_cont := continuous_coeff)
      (hg_cont := fun r => by
        refine ((MagicFunction.a.RealIntegrands.Φ₂_contDiffOn (r := r)).continuousOn.mono
          fun _ hx => mem_Icc_of_Ioo hx).congr fun t ht => ?_
        have hz : z₂' t = (-1 : ℂ) + t + I := z₂'_eq_of_mem (mem_Icc_of_Ioo ht)
        have hexp' : cexp (π * I * r * (z₂' t : ℂ)) =
            cexp (-π * I * r) * cexp (π * I * r * t) * cexp (-π * r : ℂ) := by
          rw [show π * I * r * (z₂' t : ℂ) =
              (-π * I * r : ℂ) + (π * I * r * t : ℂ) + (-π * r : ℂ) by
            rw [hz]; ring_nf; rw [I_sq]; ring, Complex.exp_add, Complex.exp_add]
        simp [MagicFunction.a.RealIntegrands.Φ₂, MagicFunction.a.ComplexIntegrands.Φ₂',
          MagicFunction.a.ComplexIntegrands.Φ₁', g,
          show z₂' t + 1 = t + I by simp [hz, add_left_comm, add_comm], hexp']
        ac_rfl)
      (hg_bound := g_norm_bound_uniform) (hcoeff := coeff_norm_le)
      (hg_repr := fun r t => by rw [exp_r_mul_coeff]; simp [g]; ring) n)

end Schwartz_Decay
end I₂

end MagicFunction.a.IntegralEstimates

namespace MagicFunction.a.IntegralEstimates.I₄

open scoped Function UpperHalfPlane Topology Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral

variable (r : ℝ)

section Setup

/-- The integrand on `Ioo (0, 1)` whose set integral is `I₄'`. -/
@[expose] public noncomputable def g : ℝ → ℝ → ℂ := fun r t ↦
  -1 * φ₀'' (-1 / (-t + I)) * (-t + I) ^ 2 * cexp (π * I * r) * cexp (-π * I * r * t) *
    cexp (-π * r)

/-- Rewrite `I₄' r` as a set integral of `g r` over `Ioo (0, 1)`. -/
public lemma I₄'_eq_integral_g_Ioo (r : ℝ) : I₄' r = ∫ t in Ioo (0 : ℝ) 1, g r t := by
  simp [I₄'_eq, intervalIntegral_eq_integral_uIoc, zero_le_one, g, integral_Ioc_eq_integral_Ioo]

end Setup

section Bounding

/-- A uniform lower bound on the imaginary part of the parametrisation `t ↦ -1 / (-t + I)`. -/
public lemma im_parametrisation_lower : ∀ t ∈ Ioo (0 : ℝ) 1, 1 / 2 < (-1 / (-↑t + I)).im :=
  fun t ht => by
    simpa [show (-1 / (-↑t + I)).im = 1 / (t ^ 2 + 1) from by
      simpa using SpherePacking.Integration.im_neg_one_div_neg_ofReal_add_I (t := t)]
      using SpherePacking.Integration.one_half_lt_one_div_sq_add_one_of_mem_Ioo01 ht

/-- A uniform-in-`r` bound on the integrand `g r t` on `Ioo (0, 1)`. -/
public lemma g_norm_bound_uniform :
    ∃ C₀ > 0, ∀ r : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r) :=
  I24Common.g_norm_bound_uniform_of (fun r t ht => by
    rw [g, norm_mul, norm_mul, norm_mul, mul_assoc, mul_assoc, norm_mul, norm_mul, norm_neg,
      norm_one, one_mul]
    gcongr
    · rw [norm_pow, ← normSq_eq_norm_sq, normSq_apply, add_re, neg_re, ofReal_re, I_re, add_zero,
        mul_neg, neg_mul, neg_neg, add_im, neg_im, ofReal_im, neg_zero, I_im, zero_add, mul_one]
      nlinarith [ht.1, ht.2]
    · conv_rhs => rw [← one_mul (rexp _), ← one_mul (rexp _)]
      gcongr <;> apply le_of_eq
      · simpa [mul_assoc, mul_left_comm, mul_comm] using norm_exp_ofReal_mul_I (π * r)
      · simpa [mul_assoc, mul_left_comm, mul_comm] using norm_exp_ofReal_mul_I (-π * r * t)
      · simp [norm_exp]) im_parametrisation_lower

end Bounding

noncomputable section Schwartz_Decay

open SchwartzMap

/-- Specialization of `I24Common.coeff` to `shift = fun t => (1 : ℂ) - (t : ℂ)`. -/
@[expose] public def coeff : ℝ → ℂ := I24Common.coeff (fun t => (1 : ℂ) - (t : ℂ))

/-- The integrand for the `n`-th derivative, obtained by multiplying `g` by `(coeff t) ^ n`. -/
@[expose] public def gN (n : ℕ) (r t : ℝ) : ℂ := (coeff t) ^ n * g r t

/-- Uniform bound `‖coeff t‖ ≤ 2 * π` for `t ∈ Ioo (0, 1)`. -/
public lemma coeff_norm_le (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : ‖coeff t‖ ≤ 2 * π :=
  I24Common.coeff_norm_le (shift := fun t => (1 : ℂ) - (t : ℂ)) (fun t ht => by
    change ‖((1 : ℂ) - (t : ℂ))‖ ≤ 1
    rw [show ((1 : ℂ) - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
    exact (by grind only [= mem_Ioo, = abs.eq_1, = max_def] : |1 - t| ≤ 1)) t ht

/-- Expand `cexp ((r : ℂ) * coeff t)` into the product of exponentials used in `g`. -/
public lemma exp_r_mul_coeff (r t : ℝ) :
    cexp ((r : ℂ) * coeff t) =
      cexp (π * I * r) * cexp (-π * I * r * t) * cexp (-π * r : ℂ) := by
  simp [show coeff t = (π * I : ℂ) + (-π * I * (t : ℂ)) + (-π : ℂ) by
    simp [coeff, I24Common.coeff, sub_eq_add_neg, mul_add, mul_assoc, add_left_comm, add_comm],
    Complex.exp_add, add_assoc, mul_add, mul_left_comm, mul_comm]

/-- Schwartz-style decay estimate for the auxiliary integral `I₄'`. -/
public theorem decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₄' x‖ ≤ C :=
  MagicFunction.a.IntegralEstimates.decay_of_iteratedDeriv_eq_integral_pow_mul
    g_norm_bound_uniform coeff_norm_le
    (fun n => iteratedDeriv_eq_setIntegral_pow_mul_of_uniform_bound_ball_one
      (I := I₄') (coeff := coeff) (g := g)
      (A := fun t : ℝ => (-1 : ℂ) * φ₀'' (-1 / (-t + I)) * (-t + I) ^ 2)
      (hI := I₄'_eq_integral_g_Ioo) (hg_cont := fun r => by
        refine ((MagicFunction.a.RealIntegrands.Φ₄_contDiffOn (r := r)).continuousOn.mono
          fun _ hx => mem_Icc_of_Ioo hx).congr fun t ht => ?_
        have hz : z₄' t = (1 : ℂ) - t + I := z₄'_eq_of_mem (mem_Icc_of_Ioo ht)
        have hz_coeff : (π * I : ℂ) * (z₄' t : ℂ) = coeff t := by
          simp [coeff, I24Common.coeff, hz, sub_eq_add_neg, mul_add, mul_assoc, add_left_comm,
            add_comm]
        simp [MagicFunction.a.RealIntegrands.Φ₄, MagicFunction.a.ComplexIntegrands.Φ₄',
          MagicFunction.a.ComplexIntegrands.Φ₃', g,
          show z₄' t - 1 = (-t : ℂ) + I by simp [hz, sub_eq_add_neg, add_assoc, add_comm],
          show cexp (π * I * r * (z₄' t : ℂ)) =
              cexp (π * I * r) * cexp (-π * I * r * t) * cexp (-π * r : ℂ) by
            simpa [mul_assoc, show (r : ℂ) * coeff t = (π * I * r : ℂ) * (z₄' t : ℂ) by
              rw [← hz_coeff]; ring] using exp_r_mul_coeff (r := r) (t := t)]
        ac_rfl)
      (hcoeff_cont := I24Common.continuous_coeff (continuous_const.sub Complex.continuous_ofReal))
      (hg_bound := g_norm_bound_uniform) (hcoeff := coeff_norm_le)
      (hg_repr := fun r t => by rw [exp_r_mul_coeff]; simp [g]; ring) n)

end Schwartz_Decay
end MagicFunction.a.IntegralEstimates.I₄
