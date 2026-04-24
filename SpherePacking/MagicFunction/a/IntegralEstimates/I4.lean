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
public import SpherePacking.MagicFunction.a.IntegralEstimates.I24Common
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

/-- A uniform lower bound on the imaginary part of the parametrisation `t ↦ -1 / (-t + I)`. -/
public lemma im_parametrisation_lower : ∀ t ∈ Ioo (0 : ℝ) 1, 1 / 2 < (-1 / (-↑t + I)).im := by
  intro t ht
  have him : (-1 / (-↑t + I)).im = 1 / (t ^ 2 + 1) := by
    simpa using SpherePacking.Integration.im_neg_one_div_neg_ofReal_add_I (t := t)
  simpa [him] using SpherePacking.Integration.one_half_lt_one_div_sq_add_one_of_mem_Ioo01 ht

end Bounding_Integrand

section Bounding_Integral

/-- A uniform-in-`r` bound on the integrand `g r t` on `Ioo (0, 1)`. -/
public lemma g_norm_bound_uniform :
    ∃ C₀ > 0, ∀ r : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r) :=
  I24Common.g_norm_bound_uniform_of I₄'_bounding_aux_1 im_parametrisation_lower

end Bounding.Bounding_Integral

noncomputable section Schwartz_Decay

open SchwartzMap

section Higher_iteratedFDerivs

open scoped Topology

/--
The coefficient appearing in the exponent when rewriting `g r t` as
`A t * cexp ((r : ℂ) * coeff t)`. This is the specialization of `I24Common.coeff`
to `shift = fun t => (1 : ℂ) - (t : ℂ)`.
-/
@[expose] public def coeff : ℝ → ℂ := I24Common.coeff (fun t => (1 : ℂ) - (t : ℂ))

/-- Continuity of `coeff`. -/
public lemma continuous_coeff : Continuous coeff :=
  I24Common.continuous_coeff (continuous_const.sub Complex.continuous_ofReal)

/-- A convenient expansion of `coeff t` as a sum. -/
public lemma coeff_eq_sum (t : ℝ) :
    coeff t = (π * I : ℂ) + (-π * I * (t : ℂ)) + (-π : ℂ) := by
  simp [coeff, I24Common.coeff, sub_eq_add_neg, mul_add, mul_assoc, add_left_comm, add_comm]

/-- The integrand for the `n`-th derivative, obtained by multiplying `g` by `(coeff t) ^ n`. -/
@[expose] public def gN (n : ℕ) (r t : ℝ) : ℂ :=
  (coeff t) ^ n * g r t

/-- Uniform bound `‖coeff t‖ ≤ 2 * π` for `t ∈ Ioo (0, 1)`. -/
public lemma coeff_norm_le (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ‖coeff t‖ ≤ 2 * π :=
  I24Common.coeff_norm_le (shift := fun t => (1 : ℂ) - (t : ℂ))
    (fun t ht => by
      change ‖((1 : ℂ) - (t : ℂ))‖ ≤ 1
      rw [show ((1 : ℂ) - (t : ℂ)) = ((1 - t : ℝ) : ℂ) from by push_cast; ring, Complex.norm_real]
      exact (by grind only [= mem_Ioo, = abs.eq_1, = max_def] : |1 - t| ≤ 1))
    t ht

/-- Expand `cexp ((r : ℂ) * coeff t)` into the product of exponentials used in `g`. -/
public lemma exp_r_mul_coeff (r t : ℝ) :
    cexp ((r : ℂ) * coeff t) =
      cexp (π * I * r) * cexp (-π * I * r * t) * cexp (-π * r : ℂ) := by
  simp [coeff_eq_sum, Complex.exp_add, add_assoc, mul_add, mul_left_comm, mul_comm]

lemma iteratedDeriv_I₄'_eq_integral_gN (n : ℕ) :
    iteratedDeriv n I₄' = fun r : ℝ ↦ ∫ t in Ioo (0 : ℝ) 1, gN n r t := by
  have hg_cont (r : ℝ) : ContinuousOn (g r) (Ioo (0 : ℝ) 1) := by
    refine ((MagicFunction.a.RealIntegrands.Φ₄_contDiffOn (r := r)).continuousOn.mono
      (fun _ hx => mem_Icc_of_Ioo hx)).congr fun t ht => ?_
    have hz : z₄' t = (1 : ℂ) - t + I := z₄'_eq_of_mem (mem_Icc_of_Ioo ht)
    have hz_coeff : (π * I : ℂ) * (z₄' t : ℂ) = coeff t := by
      simp [coeff, I24Common.coeff, hz, sub_eq_add_neg, mul_add, mul_assoc,
        add_left_comm, add_comm]
    have hexp' :
        cexp (π * I * r * (z₄' t : ℂ)) =
          cexp (π * I * r) * cexp (-π * I * r * t) * cexp (-π * r : ℂ) := by
      simpa [mul_assoc, show (r : ℂ) * coeff t = (π * I * r : ℂ) * (z₄' t : ℂ) by
        rw [← hz_coeff]; ring] using (exp_r_mul_coeff (r := r) (t := t))
    simp [MagicFunction.a.RealIntegrands.Φ₄, MagicFunction.a.ComplexIntegrands.Φ₄',
      MagicFunction.a.ComplexIntegrands.Φ₃', g,
      show z₄' t - 1 = (-t : ℂ) + I by simp [hz, sub_eq_add_neg, add_assoc, add_comm], hexp']
    ac_rfl
  let A : ℝ → ℂ := fun t : ℝ => (-1 : ℂ) * φ₀'' (-1 / (-t + I)) * (-t + I) ^ 2
  have hg_repr : ∀ r t, g r t = A t * cexp ((r : ℂ) * coeff t) := fun r t => by
    rw [exp_r_mul_coeff]; simp [A, g]; ring
  simpa [gN] using
    (iteratedDeriv_eq_setIntegral_pow_mul_of_uniform_bound_ball_one
      (I := I₄') (coeff := coeff) (g := g) (A := A) (hI := I₄'_eq_integral_g_Ioo)
      (hcoeff_cont := continuous_coeff) (hg_cont := hg_cont) (hg_bound := g_norm_bound_uniform)
      (hcoeff := coeff_norm_le) (hg_repr := hg_repr) n)

/--
Schwartz-style decay estimate for `I₄'`: all iterated derivatives decay faster than any power.

The prime in the name indicates that this result is about the auxiliary integral `I₄'`.
-/
public theorem decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₄' x‖ ≤ C :=
  MagicFunction.a.IntegralEstimates.decay_of_iteratedDeriv_eq_integral_pow_mul
    g_norm_bound_uniform coeff_norm_le
    (fun n => by simpa [gN] using iteratedDeriv_I₄'_eq_integral_gN (n := n))

end Schwartz_Decay.Higher_iteratedFDerivs
end MagicFunction.a.IntegralEstimates.I₄
