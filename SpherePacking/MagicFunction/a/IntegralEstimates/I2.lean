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
    · rw [norm_exp]
      simp

lemma parametrisation_eq : ∀ t ∈ Ioo (0 : ℝ) 1,
    (-1 / (↑t + I)) = -t / (t ^ 2 + 1) + (1 / (t ^ 2 + 1) * I) := by
  intro t ht
  obtain ⟨ht₀, ht₁⟩ := ht
  calc
  _ = (-1 / (t + I)) * ((t - I) / (t - I)) := by
      conv_lhs => rw [← mul_one (-1 / (t + I))]
      congr; symm
      apply div_self
      intro h
      conv at h => rw [sub_eq_zero]
      -- This has to be the most ridiculous proof ever. It should never have to go down to 0 ≠ 1 :(
      have h₁ : (ofReal t).im = 0 := ofReal_im t
      have h₂ : (ofReal t).im = 1 := by rw [h]; exact I_im
      exact zero_ne_one ((h₁.symm).trans h₂)
  _ = _ := by
      conv_lhs => rw [div_mul_div_comm (-1) (t + I)]
      simp only [neg_mul, one_mul, neg_sub, div_mul_eq_mul_div, ← add_div]
      congr
      · ac_rfl
      · ring_nf
        rw [I_sq]
        ring

lemma im_parametrisation_eq : ∀ t ∈ Ioo (0 : ℝ) 1, (-1 / (↑t + I)).im = 1 / (t ^ 2 + 1) :=
  fun t _ => by simpa using SpherePacking.Integration.im_neg_one_div_ofReal_add_I (t := t)

/-- A uniform lower bound on the imaginary part of the parametrisation `t ↦ -1 / (t + I)`. -/
public lemma im_parametrisation_lower : ∀ t ∈ Ioo (0 : ℝ) 1, 1 / 2 < (-1 / (↑t + I)).im := by
  intro t ht
  simpa [im_parametrisation_eq t ht] using
    (SpherePacking.Integration.one_half_lt_one_div_sq_add_one_of_mem_Ioo01 ht)

lemma im_parametrisation_upper : ∀ t ∈ Ioo (0 : ℝ) 1, (-1 / (↑t + I)).im < 1 := by
  intro t ht
  have h : (1 : ℝ) < t ^ 2 + 1 := by nlinarith [sq_pos_of_pos ht.1]
  simpa [im_parametrisation_eq t ht] using (one_div_lt_one_div_of_lt one_pos h)

end Bounding_Integrand

section Bounding_Integral

/-- A uniform-in-`r` bound on the integrand `g r t` on `Ioo (0, 1)`. -/
public lemma g_norm_bound_uniform :
    ∃ C₀ > 0, ∀ r : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀_le
  refine ⟨C₀, hC₀_pos, ?_⟩
  intro r t ht
  have h0 := I₂'_bounding_aux_1 r t ht
  refine h0.trans ?_
  gcongr
  have him : 1 / 2 < (-1 / (↑t + I)).im := im_parametrisation_lower t ht
  have hpos : 0 < (-1 / (↑t + I)).im := one_half_pos.trans him
  have hz_half : 1 / 2 < (⟨-1 / (t + I), hpos⟩ : ℍ).im := by simpa using him
  simpa [φ₀'', hpos] using
    (norm_φ₀''_le_mul_exp_neg_pi_of_one_half_lt_im (C₀ := C₀) (hC₀_pos := hC₀_pos) (hC₀ := hC₀)
      (z := ⟨-1 / (t + I), hpos⟩) hz_half)

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
  (-π : ℂ) + (π * I) * ((t : ℂ) - 1)

/-- Continuity of `coeff`. -/
public lemma continuous_coeff : Continuous coeff := by
  have hsub : Continuous fun t : ℝ ↦ ((t : ℂ) - 1) :=
    Complex.continuous_ofReal.sub continuous_const
  have hmul : Continuous fun t : ℝ ↦ (π * I : ℂ) * (((t : ℂ) - 1)) :=
    continuous_const.mul hsub
  simpa [coeff] using (continuous_const.add hmul)

/-- A convenient expansion of `coeff t` as a sum. -/
public lemma coeff_eq_sum (t : ℝ) :
    coeff t = (-π * I : ℂ) + (π * I * (t : ℂ)) + (-π : ℂ) := by
  simp [coeff, sub_eq_add_neg, mul_add, mul_assoc, add_left_comm, add_comm]

/-- The integrand for the `n`-th derivative, obtained by multiplying `g` by `(coeff t) ^ n`. -/
@[expose] public def gN (n : ℕ) (r t : ℝ) : ℂ :=
  (coeff t) ^ n * g r t

/-- Uniform bound `‖coeff t‖ ≤ 2 * π` for `t ∈ Ioo (0, 1)`. -/
public lemma coeff_norm_le (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ‖coeff t‖ ≤ 2 * π := by
  have ht0 : 0 ≤ t := le_of_lt ht.1
  have ht1 : t ≤ 1 := le_of_lt ht.2
  have hsub : ‖(t : ℂ) - 1‖ ≤ 1 := by
    have habs : |t - 1| ≤ 1 := by
      have habs : |t - 1| = 1 - t := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          abs_of_nonpos (sub_nonpos.mpr ht1)
      simpa [habs] using sub_le_self (1 : ℝ) ht0
    have hnorm : ‖(t : ℂ) - 1‖ = |t - 1| := by
      simpa [Real.norm_eq_abs] using (Complex.norm_real (t - 1))
    simpa [hnorm] using habs
  have hmul : ‖(π * I) * ((t : ℂ) - 1)‖ ≤ π := by
    calc
      ‖(π * I) * ((t : ℂ) - 1)‖ = ‖(π * I : ℂ)‖ * ‖(t : ℂ) - 1‖ := by simp
      _ ≤ ‖(π * I : ℂ)‖ * 1 := mul_le_mul_of_nonneg_left hsub (norm_nonneg _)
      _ = π := by simp [Real.pi_pos.le]
  calc
    ‖coeff t‖ = ‖(-π : ℂ) + (π * I) * ((t : ℂ) - 1)‖ := rfl
    _ ≤ ‖(-π : ℂ)‖ + ‖(π * I) * ((t : ℂ) - 1)‖ := norm_add_le _ _
    _ ≤ π + π := by
      have hleft : ‖(-π : ℂ)‖ ≤ π :=
        le_of_eq (by simp [Real.pi_pos.le])
      exact add_le_add hleft hmul
    _ = 2 * π := by ring

/-- Expand `cexp ((r : ℂ) * coeff t)` into the product of exponentials used in `g`. -/
public lemma exp_r_mul_coeff (r t : ℝ) :
    cexp ((r : ℂ) * coeff t) =
      cexp (-π * I * r) * cexp (π * I * r * t) * cexp (-π * r : ℂ) := by
  simp [coeff_eq_sum, Complex.exp_add, add_assoc, mul_assoc, mul_add, mul_left_comm, mul_comm]

lemma iteratedDeriv_I₂'_eq_integral_gN (n : ℕ) :
    iteratedDeriv n I₂' = fun r : ℝ ↦ ∫ t in Ioo (0 : ℝ) 1, gN n r t := by
  have hg_cont (r : ℝ) : ContinuousOn (g r) (Ioo (0 : ℝ) 1) := by
    have hΦ : ContinuousOn (MagicFunction.a.RealIntegrands.Φ₂ (r := r)) (Ioo (0 : ℝ) 1) := by
      have h := (MagicFunction.a.RealIntegrands.Φ₂_contDiffOn (r := r)).continuousOn
      exact h.mono (by intro x hx; exact mem_Icc_of_Ioo hx)
    have hgEq : EqOn (g r) (MagicFunction.a.RealIntegrands.Φ₂ (r := r)) (Ioo (0 : ℝ) 1) := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioo ht
      have hz : z₂' t = (-1 : ℂ) + t + I := z₂'_eq_of_mem ht'
      have hz_add : z₂' t + 1 = t + I := by simp [hz, add_left_comm, add_comm]
      have hexparg :
          (π : ℂ) * I * (r : ℂ) * (z₂' t : ℂ) =
            (-π * I * r : ℂ) + (π * I * r * t : ℂ) + (-π * r : ℂ) := by
        simp [hz, mul_add, mul_left_comm, mul_comm]
        ring_nf
        simp [I_sq]
      have hexp :
          cexp ((π : ℂ) * I * (r : ℂ) * (z₂' t : ℂ)) =
            cexp (-π * I * r) * cexp (π * I * r * t) * cexp (-π * r : ℂ) := by
        calc
          cexp ((π : ℂ) * I * (r : ℂ) * (z₂' t : ℂ))
              = cexp ((-π * I * r : ℂ) + (π * I * r * t : ℂ) + (-π * r : ℂ)) := by
                simp [hexparg]
          _ = cexp ((-π * I * r : ℂ) + (π * I * r * t : ℂ)) * cexp (-π * r : ℂ) := by
                simpa [add_assoc] using
                  (Complex.exp_add ((-π * I * r : ℂ) + (π * I * r * t : ℂ)) (-π * r : ℂ))
          _ = (cexp (-π * I * r) * cexp (π * I * r * t)) * cexp (-π * r : ℂ) := by
                simp [Complex.exp_add]
          _ = cexp (-π * I * r) * cexp (π * I * r * t) * cexp (-π * r : ℂ) := by
                ac_rfl
      have hexp' :
          cexp (π * I * r * (z₂' t : ℂ)) =
            cexp (-π * I * r) * cexp (π * I * r * t) * cexp (-π * r : ℂ) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hexp
      -- Avoid rewriting `z₂' t` itself; only rewrite `z₂' t + 1` and the exponential.
      simp [MagicFunction.a.RealIntegrands.Φ₂, MagicFunction.a.ComplexIntegrands.Φ₂',
        MagicFunction.a.ComplexIntegrands.Φ₁', g, hz_add, hexp']
      ac_rfl
    exact hΦ.congr hgEq
  let A : ℝ → ℂ := fun t : ℝ => φ₀'' (-1 / (t + I)) * (t + I) ^ 2
  have hg_repr : ∀ r t, g r t = A t * cexp ((r : ℂ) * coeff t) := by
    intro r t
    have hexp := (exp_r_mul_coeff (r := r) (t := t)).symm
    simpa [A, g, mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z ↦ A t * z) hexp
  simpa [gN] using
    (iteratedDeriv_eq_setIntegral_pow_mul_of_uniform_bound_ball_one
      (I := I₂') (coeff := coeff) (g := g) (A := A) (hI := I₂'_eq_integral_g_Ioo)
      (hcoeff_cont := continuous_coeff) (hg_cont := hg_cont)
      (hg_bound := g_norm_bound_uniform) (hcoeff := coeff_norm_le) (hg_repr := hg_repr) n)

lemma iteratedDeriv_bound (n : ℕ) :
    ∃ C₁ > 0, ∀ r : ℝ, ‖iteratedDeriv n I₂' r‖ ≤ C₁ * rexp (-π * r) := by
  simpa using (iteratedDeriv_bound_of_iteratedDeriv_eq_integral_pow_mul
    (I := I₂') (coeff := coeff) (g := g) (n := n) g_norm_bound_uniform coeff_norm_le
    (by simpa [gN] using (iteratedDeriv_I₂'_eq_integral_gN (n := n))))

/--
Schwartz-style decay estimate for `I₂'`: all iterated derivatives decay faster than any power.

The prime in the name indicates that this result is about the auxiliary integral `I₂'`.
-/
public theorem decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₂' x‖ ≤ C := by
  intro k n
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := iteratedDeriv_bound (n := n)
  simpa using (MagicFunction.a.IntegralEstimates.decay_of_bounding_uniform_norm_iteratedDeriv
    (I := I₂') (n := n) ⟨C₁, hC₁_pos, fun x _ => hC₁ x⟩ k)

end Schwartz_Decay.Higher_iteratedFDerivs
end I₂

end MagicFunction.a.IntegralEstimates
