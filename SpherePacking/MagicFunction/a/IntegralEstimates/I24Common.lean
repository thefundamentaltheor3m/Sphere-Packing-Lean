module

public import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.Basic
public import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
public import SpherePacking.MagicFunction.a.IntegralEstimates.BoundingAux
public import SpherePacking.MagicFunction.a.IntegralEstimates.PowExpBounds
public import Mathlib.Analysis.Calculus.ParametricIntegral
import SpherePacking.ForMathlib.DerivHelpers

/-!
# Common skeleton for `I₂'`/`I₄'` integral estimates

Shared infrastructure for proving exponential bounds and Schwartz decay of iterated derivatives
of `I₂'` and `I₄'`. Both integrals have integrands of the form
`t ↦ prefactor * φ₀''(-1/(z + shift)) * (z + shift)^2 * cexp((π*I)*r*z)` where
`(z, shift, prefactor) ∈ {(z₂', 1, 1), (z₄', -1, -1)}`; after substituting `z = z_k' t`, the
coefficient has the form `coeff t = (-π) + (π*I) * (sign * (t - 1))` with `sign = ±1`.

The coefficient-bound and uniform-bound lemmas here are fully generic in `coeff` and `shift`; the
specialization files `I2.lean` and `I4.lean` provide the concrete integrand `g` and its
representation via `iteratedDeriv_eq_setIntegral_pow_mul_of_uniform_bound_ball_one`.
-/

namespace MagicFunction.a.IntegralEstimates.I24Common

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

/--
Uniform bound `‖coeff t‖ ≤ 2π` on `Ioo (0, 1)` given `‖shift t‖ ≤ 1` there.
-/
public lemma coeff_norm_le {shift : ℝ → ℂ} (hshift : ∀ t ∈ Ioo (0 : ℝ) 1, ‖shift t‖ ≤ 1) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) : ‖coeff shift t‖ ≤ 2 * π := by
  have hpi0 : (0 : ℝ) ≤ π := Real.pi_pos.le
  have hleft : ‖(-π : ℂ)‖ ≤ π := by simp [abs_of_nonneg hpi0]
  have hpiI : ‖(π * I : ℂ)‖ = π := by simp [abs_of_nonneg hpi0]
  have hmul : ‖(π * I : ℂ) * shift t‖ ≤ π := by
    calc
      ‖(π * I : ℂ) * shift t‖ = ‖(π * I : ℂ)‖ * ‖shift t‖ := by simp
      _ ≤ ‖(π * I : ℂ)‖ * 1 := mul_le_mul_of_nonneg_left (hshift t ht) (norm_nonneg _)
      _ = π := by rw [hpiI]; ring
  calc
    ‖coeff shift t‖ ≤ ‖(-π : ℂ)‖ + ‖(π * I : ℂ) * shift t‖ := norm_add_le _ _
    _ ≤ π + π := add_le_add hleft hmul
    _ = 2 * π := by ring

/--
Uniform `‖g r t‖ ≤ C₀ * exp(-π) * 2 * exp(-π * r)` bound on `Ioo (0, 1)`, derived from:
* a pointwise bound `‖g r t‖ ≤ ‖φ₀''(mob t)‖ * 2 * exp(-π * r)` (the `aux_1` lemma);
* a geometric fact `(mob t).im > 1/2` on `Ioo (0, 1)`.
-/
public lemma g_norm_bound_uniform_of {g : ℝ → ℝ → ℂ} {mob : ℝ → ℂ}
    (haux : ∀ r : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ‖g r t‖ ≤ ‖φ₀'' (mob t)‖ * 2 * rexp (-π * r))
    (hmob_im : ∀ t ∈ Ioo (0 : ℝ) 1, (1 / 2 : ℝ) < (mob t).im) :
    ∃ C₀ > 0, ∀ r : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀_le
  refine ⟨C₀, hC₀_pos, ?_⟩
  intro r t ht
  refine (haux r t ht).trans ?_
  gcongr
  have him : (1 / 2 : ℝ) < (mob t).im := hmob_im t ht
  have hpos : 0 < (mob t).im := one_half_pos.trans him
  have hz_half : (1 / 2 : ℝ) < (⟨mob t, hpos⟩ : ℍ).im := by simpa using him
  simpa [φ₀'', hpos] using
    norm_φ₀''_le_mul_exp_neg_pi_of_one_half_lt_im (C₀ := C₀) (hC₀_pos := hC₀_pos) (hC₀ := hC₀)
      (z := ⟨mob t, hpos⟩) hz_half

/--
Given a representation of `g r t` with suitable hypotheses, derive Schwartz-style decay
`‖x‖^k * ‖iteratedFDeriv n I x‖ ≤ C` on `[0, ∞)` from a uniform-in-`r` exponential bound on `g`.

The `hiteratedDeriv` hypothesis should express `iteratedDeriv n I` as the integral of
`coeff^n * g r t` over `Ioo (0, 1)`; the precise form is provided by the caller.
-/
public theorem decay_of_iteratedDeriv_eq_integral {I : ℝ → ℂ} {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ}
    (hg_bound : ∃ C₀ > 0, ∀ r : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r))
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hiteratedDeriv : ∀ n, iteratedDeriv n I =
      fun r : ℝ ↦ ∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ n * g r t) :
    ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I x‖ ≤ C := by
  intro k n
  have hbound : ∃ C₁ > 0, ∀ r : ℝ, ‖iteratedDeriv n I r‖ ≤ C₁ * rexp (-π * r) := by
    simpa using
      iteratedDeriv_bound_of_iteratedDeriv_eq_integral_pow_mul (I := I) (coeff := coeff) (g := g)
        (n := n) hg_bound hcoeff (hiteratedDeriv n)
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := hbound
  simpa using
    (decay_of_bounding_uniform_norm_iteratedDeriv (I := I) (n := n)
      ⟨C₁, hC₁_pos, fun x _ => by simpa using hC₁ x⟩ k)

end

end MagicFunction.a.IntegralEstimates.I24Common
