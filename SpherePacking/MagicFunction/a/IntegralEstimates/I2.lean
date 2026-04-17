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
# Bounds for `I₂'`

This file proves the analytic estimates needed for the auxiliary integral `I₂'`: a representation
as an integral over `Ioo (0, 1)`, uniform exponential bounds, and Schwartz decay for iterated
derivatives in the parameter `r`.

## Main definitions
* `g`
* `coeff`, `gN`

## Main statements
* `I₂'_eq_integral_g_Ioo`
* `g_norm_bound_uniform`
* `decay'`
-/

namespace MagicFunction.a.IntegralEstimates.I₂

open scoped Function UpperHalfPlane Topology Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral

variable (r : ℝ)

section Setup

/-- The integrand on `Ioo (0, 1)` whose set integral is `I₂'`. -/
@[expose] public noncomputable def g : ℝ → ℝ → ℂ := fun r t ↦
  φ₀'' (-1 / (t + I))
    * (t + I) ^ 2
    * cexp (-π * I * r)
    * cexp (π * I * r * t)
    * cexp (-π * r)

/-- Rewrite `I₂' r` as a set integral of `g r` over `Ioo (0, 1)`. -/
public lemma I₂'_eq_integral_g_Ioo (r : ℝ) : I₂' r = ∫ t in Ioo (0 : ℝ) 1, g r t := by
  simp [I₂'_eq, intervalIntegral_eq_integral_uIoc, zero_le_one, g, integral_Ioc_eq_integral_Ioo]

end Setup

----------------------------------------------------------------

section Bounding

section Bounding_Integrand

lemma I₂'_bounding_aux_1 (r : ℝ) : ∀ t ∈ Ioo (0 : ℝ) 1, ‖g r t‖ ≤
    ‖φ₀'' (-1 / (t + I))‖ * 2 * rexp (-π * r) := by
  intro t ht
  rw [g, norm_mul, norm_mul, norm_mul, mul_assoc, mul_assoc, norm_mul]
  gcongr
  · rw [norm_pow, ← normSq_eq_norm_sq, normSq_apply, add_re, ofReal_re, I_re, add_zero, add_im,
      ofReal_im, I_im, zero_add, mul_one]
    nlinarith [ht.1, ht.2]
  · conv_rhs => rw [← one_mul (rexp _), ← one_mul (rexp _)]
    gcongr <;> apply le_of_eq
    · calc
      _ = ‖cexp (((-π * r : ℝ) : ℂ) * I)‖ := by congr 2; push_cast; ac_rfl
      _ = 1 := norm_exp_ofReal_mul_I (-π * r)
    · calc
      _ = ‖cexp (((π * r * t : ℝ) : ℂ) * I)‖ := by congr 2; push_cast; ac_rfl
      _ = 1 := norm_exp_ofReal_mul_I (π * r * t)
    · rw [norm_exp]; norm_cast

lemma im_parametrisation_eq : ∀ t ∈ Ioo (0 : ℝ) 1, (-1 / (↑t + I)).im = 1 / (t ^ 2 + 1) :=
  fun t _ => by simpa using SpherePacking.Integration.im_neg_one_div_ofReal_add_I (t := t)

/-- A uniform lower bound on the imaginary part of the parametrisation `t ↦ -1 / (t + I)`. -/
public lemma im_parametrisation_lower : ∀ t ∈ Ioo (0 : ℝ) 1, 1 / 2 < (-1 / (↑t + I)).im := by
  intro t ht
  simpa [im_parametrisation_eq t ht] using
    (SpherePacking.Integration.one_half_lt_one_div_sq_add_one_of_mem_Ioo01 ht)

end Bounding_Integrand

section Bounding_Integral

/-- A uniform-in-`r` bound on the integrand `g r t` on `Ioo (0, 1)`. -/
public lemma g_norm_bound_uniform :
    ∃ C₀ > 0, ∀ r : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r) :=
  I24Common.g_norm_bound_uniform_of I₂'_bounding_aux_1 im_parametrisation_lower

end Bounding.Bounding_Integral
----------------------------------------------------------------

noncomputable section Schwartz_Decay

open SchwartzMap

section Higher_iteratedFDerivs

open scoped Topology

/--
The coefficient in the exponent when rewriting `g r t` as `A t * cexp ((r : ℂ) * coeff t)`.
This is the specialization of `I24Common.coeff` to `shift = fun t => (t : ℂ) - 1`.
-/
@[expose] public def coeff : ℝ → ℂ := I24Common.coeff (fun t => (t : ℂ) - 1)

/-- Continuity of `coeff`. -/
public lemma continuous_coeff : Continuous coeff :=
  I24Common.continuous_coeff (Complex.continuous_ofReal.sub continuous_const)

/-- A convenient expansion of `coeff t` as a sum. -/
public lemma coeff_eq_sum (t : ℝ) :
    coeff t = (-π * I : ℂ) + (π * I * (t : ℂ)) + (-π : ℂ) := by
  simp [coeff, I24Common.coeff, sub_eq_add_neg, mul_add, mul_assoc, add_left_comm, add_comm]

/-- The integrand for the `n`-th derivative, obtained by multiplying `g` by `(coeff t) ^ n`. -/
@[expose] public def gN (n : ℕ) (r t : ℝ) : ℂ :=
  (coeff t) ^ n * g r t

/-- Uniform bound `‖coeff t‖ ≤ 2 * π` for `t ∈ Ioo (0, 1)`. -/
public lemma coeff_norm_le (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ‖coeff t‖ ≤ 2 * π :=
  I24Common.coeff_norm_le (shift := fun t => (t : ℂ) - 1)
    (fun t ht => by
      have habs : |t - 1| ≤ 1 := by
        grind only [= mem_Ioo, = abs.eq_1, = max_def]
      change ‖((t : ℂ) - 1)‖ ≤ 1
      rw [show ((t : ℂ) - 1) = ((t - 1 : ℝ) : ℂ) from by push_cast; ring, Complex.norm_real]
      exact habs)
    t ht

/-- Expand `cexp ((r : ℂ) * coeff t)` into the product of exponentials used in `g`. -/
public lemma exp_r_mul_coeff (r t : ℝ) :
    cexp ((r : ℂ) * coeff t) =
      cexp (-π * I * r) * cexp (π * I * r * t) * cexp (-π * r : ℂ) := by
  simp [coeff_eq_sum, Complex.exp_add, add_assoc, mul_assoc, mul_add, mul_left_comm, mul_comm]

lemma iteratedDeriv_I₂'_eq_integral_gN (n : ℕ) :
    iteratedDeriv n I₂' = fun r : ℝ ↦ ∫ t in Ioo (0 : ℝ) 1, gN n r t := by
  have hg_cont (r : ℝ) : ContinuousOn (g r) (Ioo (0 : ℝ) 1) := by
    have hΦ : ContinuousOn (MagicFunction.a.RealIntegrands.Φ₂ (r := r)) (Ioo (0 : ℝ) 1) :=
      (MagicFunction.a.RealIntegrands.Φ₂_contDiffOn (r := r)).continuousOn.mono
        fun _ hx => mem_Icc_of_Ioo hx
    have hgEq : EqOn (g r) (MagicFunction.a.RealIntegrands.Φ₂ (r := r)) (Ioo (0 : ℝ) 1) := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioo ht
      have hz : z₂' t = (-1 : ℂ) + t + I := z₂'_eq_of_mem ht'
      have hz_add : z₂' t + 1 = t + I := by simp [hz, add_left_comm, add_comm]
      have hexparg :
          (π : ℂ) * I * (r : ℂ) * (z₂' t : ℂ) =
            (-π * I * r : ℂ) + (π * I * r * t : ℂ) + (-π * r : ℂ) := by
        rw [hz]; ring_nf; rw [I_sq]; ring
      have hexp' :
          cexp (π * I * r * (z₂' t : ℂ)) =
            cexp (-π * I * r) * cexp (π * I * r * t) * cexp (-π * r : ℂ) := by
        rw [show π * I * r * (z₂' t : ℂ) = (π : ℂ) * I * (r : ℂ) * (z₂' t : ℂ) from by ring,
          hexparg, Complex.exp_add, Complex.exp_add]
      -- Avoid rewriting `z₂' t` itself; only rewrite `z₂' t + 1` and the exponential.
      simp [MagicFunction.a.RealIntegrands.Φ₂, MagicFunction.a.ComplexIntegrands.Φ₂',
        MagicFunction.a.ComplexIntegrands.Φ₁', g, hz_add, hexp']
      ac_rfl
    exact hΦ.congr hgEq
  let A : ℝ → ℂ := fun t : ℝ => φ₀'' (-1 / (t + I)) * (t + I) ^ 2
  have hg_repr : ∀ r t, g r t = A t * cexp ((r : ℂ) * coeff t) := by
    intro r t
    simpa [A, g, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun z ↦ A t * z) (exp_r_mul_coeff (r := r) (t := t)).symm
  simpa [gN] using
    (iteratedDeriv_eq_setIntegral_pow_mul_of_uniform_bound_ball_one
      (I := I₂') (coeff := coeff) (g := g) (A := A) (hI := I₂'_eq_integral_g_Ioo)
      (hcoeff_cont := continuous_coeff) (hg_cont := hg_cont)
      (hg_bound := g_norm_bound_uniform) (hcoeff := coeff_norm_le) (hg_repr := hg_repr) n)

/--
Schwartz-style decay estimate for `I₂'`: all iterated derivatives decay faster than any power.

The prime in the name indicates that this result is about the auxiliary integral `I₂'`.
-/
public theorem decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₂' x‖ ≤ C :=
  MagicFunction.a.IntegralEstimates.decay_of_iteratedDeriv_eq_integral_pow_mul
    g_norm_bound_uniform coeff_norm_le
    (fun n => by simpa [gN] using iteratedDeriv_I₂'_eq_integral_gN (n := n))

end Schwartz_Decay.Higher_iteratedFDerivs
end I₂

end MagicFunction.a.IntegralEstimates
