module
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
public import SpherePacking.Integration.UpperHalfPlaneComp
public import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Instances.Real.Lemmas
import SpherePacking.ForMathlib.DerivHelpers

/-! # Elementary exponential bounds, auxiliary integral bounds, and Schwartz decay lemmas.

This file collects:
* Auxiliary bounds on integrals over `(0, 1)` for integrands `(coeff t) ^ n * g r t`
  (`norm_pow_mul_mul_le`, `iteratedDeriv_bound_of_iteratedDeriv_eq_integral_pow_mul`,
  `integrable_pow_mul_of_volume_restrict_Ioo01`,
  `hasDerivAt_integral_pow_mul_of_uniform_bound_ball_one`,
  `iteratedDeriv_eq_setIntegral_pow_mul_of_uniform_bound_ball_one`);
* Elementary exponential bounds packaged as Schwartz decay lemmas
  (`pow_mul_exp_neg_pi_bounded`, `decay_of_bounding_uniform_norm_iteratedDeriv`,
  `decay_of_iteratedDeriv_eq_integral_pow_mul`);
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
