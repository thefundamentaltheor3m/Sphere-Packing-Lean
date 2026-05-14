module
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.IntegralEstimates.BoundingAux
public import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
public import Mathlib.Analysis.Calculus.ParametricIntegral
import SpherePacking.ForMathlib.DerivHelpers

/-! # Elementary exponential bounds, packaged as Schwartz decay lemmas. -/

namespace MagicFunction.a.IntegralEstimates

open scoped Real Topology
open Real Set Filter

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
