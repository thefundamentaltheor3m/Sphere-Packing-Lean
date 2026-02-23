/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

module
public import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.Basic
public import SpherePacking.MagicFunction.a.Integrability.RealIntegrands
public import SpherePacking.MagicFunction.a.IntegralEstimates.PowExpBounds
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.RealDeriv
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.MagicFunction.a.IntegralEstimates.BoundingAux

/-!
# Bounds for `I₄'`

This file proves the analytic estimates needed for the auxiliary integral `I₄'`: a representation
as an integral over `Ioo (0, 1)`, uniform exponential bounds, and Schwartz decay for iterated
derivatives in the parameter `r`.

## Main definitions
* `g`
* `coeff`, `gN`

## Main statements
* `I₄'_eq_integral_g_Ioo`
* `g_norm_bound_uniform`
* `decay'`
-/

namespace MagicFunction.a.IntegralEstimates.I₄

open scoped Function UpperHalfPlane Topology Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral

variable (r : ℝ)

section Setup

/-- The integrand on `Ioo (0, 1)` whose set integral is `I₄'`. -/
@[expose] public noncomputable def g : ℝ → ℝ → ℂ := fun r t ↦ -1
    * φ₀'' (-1 / (-t + I))
    * (-t + I) ^ 2
    * cexp (π * I * r)
    * cexp (-π * I * r * t)
    * cexp (-π * r)

/-- Rewrite `I₄' r` as a set integral of `g r` over `Ioo (0, 1)`. -/
public lemma I₄'_eq_integral_g_Ioo (r : ℝ) : I₄' r = ∫ t in Ioo (0 : ℝ) 1, g r t := by
  simp [I₄'_eq, intervalIntegral_eq_integral_uIoc, zero_le_one, g, integral_Ioc_eq_integral_Ioo]

end Setup

----------------------------------------------------------------

section Bounding

section Bounding_Integrand

lemma I₄'_bounding_aux_1 (r : ℝ) : ∀ t ∈ Ioo (0 : ℝ) 1, ‖g r t‖ ≤
    ‖φ₀'' (-1 / (-t + I))‖ * 2 * rexp (-π * r) := by
  intro t ht
  rw [g, norm_mul, norm_mul, norm_mul, mul_assoc, mul_assoc, norm_mul,
    norm_mul, norm_neg, norm_one, one_mul]
  gcongr
  · rw [norm_pow, ← normSq_eq_norm_sq, normSq_apply, add_re, neg_re, ofReal_re, I_re,
      add_zero, mul_neg, neg_mul, neg_neg, add_im, neg_im, ofReal_im, neg_zero, I_im, zero_add,
      mul_one]
    nlinarith [ht.1, ht.2]
  · conv_rhs => rw [← one_mul (rexp _), ← one_mul (rexp _)]
    gcongr <;> apply le_of_eq
    · simpa [mul_assoc, mul_left_comm, mul_comm] using norm_exp_ofReal_mul_I (π * r)
    · simpa [mul_assoc, mul_left_comm, mul_comm] using norm_exp_ofReal_mul_I (-π * r * t)
    · simp [norm_exp]

lemma im_parametrisation_eq : ∀ t ∈ Ioo (0 : ℝ) 1, (-1 / (-↑t + I)).im = 1 / (t ^ 2 + 1) :=
  fun t _ => by simpa using SpherePacking.Integration.im_neg_one_div_neg_ofReal_add_I (t := t)

/-- A uniform lower bound on the imaginary part of the parametrisation `t ↦ -1 / (-t + I)`. -/
public lemma im_parametrisation_lower : ∀ t ∈ Ioo (0 : ℝ) 1, 1 / 2 < (-1 / (-↑t + I)).im := by
  intro t ht
  simpa [im_parametrisation_eq t ht] using
    (SpherePacking.Integration.one_half_lt_one_div_sq_add_one_of_mem_Ioo01 ht)

end Bounding_Integrand

section Bounding_Integral

/-- A uniform-in-`r` bound on the integrand `g r t` on `Ioo (0, 1)`. -/
public lemma g_norm_bound_uniform :
    ∃ C₀ > 0, ∀ r : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀_le
  refine ⟨C₀, hC₀_pos, ?_⟩
  intro r t ht
  have h0 := I₄'_bounding_aux_1 r t ht
  refine h0.trans ?_
  gcongr
  have him : 1 / 2 < (-1 / (-↑t + I)).im := im_parametrisation_lower t ht
  have hpos : 0 < (-1 / (-↑t + I)).im := one_half_pos.trans him
  have hz_half : 1 / 2 < (⟨-1 / (-t + I), hpos⟩ : ℍ).im := by simpa using him
  simpa [φ₀'', hpos] using
    (norm_φ₀''_le_mul_exp_neg_pi_of_one_half_lt_im (C₀ := C₀) (hC₀_pos := hC₀_pos) (hC₀ := hC₀)
      (z := ⟨-1 / (-t + I), hpos⟩) hz_half)

end Bounding.Bounding_Integral
----------------------------------------------------------------

noncomputable section Schwartz_Decay

open SchwartzMap

section Higher_iteratedFDerivs

open scoped Topology

/--
The coefficient appearing in the exponent when rewriting `g r t` as
`A t * cexp ((r : ℂ) * coeff t)`.
-/
@[expose] public def coeff (t : ℝ) : ℂ :=
  (-π : ℂ) + (π * I) * (1 - (t : ℂ))

/-- Continuity of `coeff`. -/
public lemma continuous_coeff : Continuous coeff := by
  simpa [coeff] using
    (continuous_const.add (continuous_const.mul (continuous_const.sub Complex.continuous_ofReal)))

/-- A convenient expansion of `coeff t` as a sum. -/
public lemma coeff_eq_sum (t : ℝ) :
    coeff t = (π * I : ℂ) + (-π * I * (t : ℂ)) + (-π : ℂ) := by
  simp [coeff, sub_eq_add_neg, mul_add, mul_assoc, add_left_comm, add_comm]

/-- The integrand for the `n`-th derivative, obtained by multiplying `g` by `(coeff t) ^ n`. -/
@[expose] public def gN (n : ℕ) (r t : ℝ) : ℂ :=
  (coeff t) ^ n * g r t

/-- Uniform bound `‖coeff t‖ ≤ 2 * π` for `t ∈ Ioo (0, 1)`. -/
public lemma coeff_norm_le (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ‖coeff t‖ ≤ 2 * π := by
  have ht0 : 0 ≤ t := le_of_lt ht.1
  have ht1 : t ≤ 1 := le_of_lt ht.2
  have habs : |1 - t| ≤ 1 := by
    have hle' : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    have : 1 - t ≤ 1 := sub_le_self (1 : ℝ) ht0
    simpa [abs_of_nonneg hle'] using this
  have hsub : ‖(1 : ℂ) - (t : ℂ)‖ ≤ 1 := by
    have hnorm_sub : ‖(1 : ℂ) - (t : ℂ)‖ = |1 - t| := by
      simpa [Real.norm_eq_abs] using (Complex.norm_real (1 - t))
    simpa [hnorm_sub] using habs
  have hpi0 : (0 : ℝ) ≤ π := Real.pi_pos.le
  calc
    ‖coeff t‖ = ‖(-π : ℂ) + (π * I) * ((1 : ℂ) - (t : ℂ))‖ := by
      simp [coeff, sub_eq_add_neg, mul_add, mul_assoc]
    _ ≤ ‖(-π : ℂ)‖ + ‖(π * I) * ((1 : ℂ) - (t : ℂ))‖ := norm_add_le _ _
    _ ≤ π + π := by
      have hleft : ‖(-π : ℂ)‖ = π := by
        simp [Real.norm_eq_abs, abs_of_nonneg hpi0]
      have hleft' : ‖(-π : ℂ)‖ ≤ π := by simp [hleft]
      have hmul' : ‖(π * I) * ((1 : ℂ) - (t : ℂ))‖ ≤ π := by
        calc
          ‖(π * I) * ((1 : ℂ) - (t : ℂ))‖ = ‖(π * I : ℂ)‖ * ‖(1 : ℂ) - (t : ℂ)‖ := by simp
          _ ≤ ‖(π * I : ℂ)‖ * 1 := by
            exact mul_le_mul_of_nonneg_left hsub (norm_nonneg (π * I : ℂ))
          _ = π := by simp [hpi0]
      exact add_le_add hleft' hmul'
    _ = 2 * π := by ring

/-- Expand `cexp ((r : ℂ) * coeff t)` into the product of exponentials used in `g`. -/
public lemma exp_r_mul_coeff (r t : ℝ) :
    cexp ((r : ℂ) * coeff t) =
      cexp (π * I * r) * cexp (-π * I * r * t) * cexp (-π * r : ℂ) := by
  simp [coeff_eq_sum, Complex.exp_add, add_assoc, mul_add, mul_left_comm, mul_comm]

lemma iteratedDeriv_I₄'_eq_integral_gN (n : ℕ) :
    iteratedDeriv n I₄' = fun r : ℝ ↦ ∫ t in Ioo (0 : ℝ) 1, gN n r t := by
  have hg_cont (r : ℝ) : ContinuousOn (g r) (Ioo (0 : ℝ) 1) := by
    have hΦ : ContinuousOn (MagicFunction.a.RealIntegrands.Φ₄ (r := r)) (Ioo (0 : ℝ) 1) := by
      have h := (MagicFunction.a.RealIntegrands.Φ₄_contDiffOn (r := r)).continuousOn
      exact h.mono (by intro x hx; exact mem_Icc_of_Ioo hx)
    have hgEq : EqOn (g r) (MagicFunction.a.RealIntegrands.Φ₄ (r := r)) (Ioo (0 : ℝ) 1) := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioo ht
      have hz : z₄' t = (1 : ℂ) - t + I := z₄'_eq_of_mem ht'
      have hz_sub : z₄' t - 1 = (-t : ℂ) + I := by
        simp [hz, sub_eq_add_neg, add_assoc, add_comm]
      have hz_coeff : (π * I : ℂ) * (z₄' t : ℂ) = coeff t := by
        simp [coeff, hz, sub_eq_add_neg, mul_add, mul_assoc, add_left_comm, add_comm]
      have hexp' :
          cexp (π * I * r * (z₄' t : ℂ)) =
            cexp (π * I * r) * cexp (-π * I * r * t) * cexp (-π * r : ℂ) := by
        have harg : (r : ℂ) * coeff t = (π * I * r : ℂ) * (z₄' t : ℂ) := by
          rw [← hz_coeff]
          ring
        simpa [mul_assoc, harg] using (exp_r_mul_coeff (r := r) (t := t))
      -- Avoid rewriting `z₄' t` itself; only rewrite `z₄' t - 1` and the exponential.
      simp [MagicFunction.a.RealIntegrands.Φ₄, MagicFunction.a.ComplexIntegrands.Φ₄',
        MagicFunction.a.ComplexIntegrands.Φ₃', g, hz_sub, hexp']
      ac_rfl
    exact hΦ.congr hgEq
  let A : ℝ → ℂ := fun t : ℝ => (-1 : ℂ) * φ₀'' (-1 / (-t + I)) * (-t + I) ^ 2
  have hg_repr : ∀ r t, g r t = A t * cexp ((r : ℂ) * coeff t) := by
    intro r t
    have hexp := (exp_r_mul_coeff (r := r) (t := t)).symm
    simpa [A, g, mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z ↦ A t * z) hexp
  simpa [gN] using
    (iteratedDeriv_eq_setIntegral_pow_mul_of_uniform_bound_ball_one
      (I := I₄') (coeff := coeff) (g := g) (A := A) (hI := I₄'_eq_integral_g_Ioo)
      (hcoeff_cont := continuous_coeff) (hg_cont := hg_cont) (hg_bound := g_norm_bound_uniform)
      (hcoeff := coeff_norm_le) (hg_repr := hg_repr) n)

lemma iteratedDeriv_bound (n : ℕ) :
    ∃ C₁ > 0, ∀ r : ℝ, ‖iteratedDeriv n I₄' r‖ ≤ C₁ * rexp (-π * r) := by
  simpa using iteratedDeriv_bound_of_iteratedDeriv_eq_integral_pow_mul (I := I₄') (coeff := coeff)
    (g := g) (n := n) g_norm_bound_uniform coeff_norm_le
    (by simpa [gN] using (iteratedDeriv_I₄'_eq_integral_gN (n := n)))

/--
Schwartz-style decay estimate for `I₄'`: all iterated derivatives decay faster than any power.

The prime in the name indicates that this result is about the auxiliary integral `I₄'`.
-/
public theorem decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₄' x‖ ≤ C := by
  intro k n
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := iteratedDeriv_bound (n := n)
  simpa using
    (MagicFunction.a.IntegralEstimates.decay_of_bounding_uniform_norm_iteratedDeriv
      (I := I₄') (n := n) ⟨C₁, hC₁_pos, fun x _ => by simpa using hC₁ x⟩ k)

end Schwartz_Decay.Higher_iteratedFDerivs
end MagicFunction.a.IntegralEstimates.I₄
