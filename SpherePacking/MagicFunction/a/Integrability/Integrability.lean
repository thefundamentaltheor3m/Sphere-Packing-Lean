/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.a.Basic

import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.IntegralEstimates.I1
public import SpherePacking.MagicFunction.a.IntegralEstimates.I2
public import SpherePacking.MagicFunction.a.IntegralEstimates.I3
public import SpherePacking.MagicFunction.a.IntegralEstimates.I4
public import SpherePacking.MagicFunction.a.IntegralEstimates.I5
public import SpherePacking.MagicFunction.a.IntegralEstimates.I6
public import SpherePacking.MagicFunction.a.Integrability.RealIntegrands
public import SpherePacking.Tactic.EndpointIntegrability.Tactic

/-!
# Integrability

In this file, we prove that the integrands `Φⱼ` are integrable. Each proof puts the continuity of
the integrand and, where the interval is not compact, a pointwise bound of it in the context, and
`endpoint_integrability` concludes.
-/

@[expose] public section

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound MagicFunction.a.RealIntegrands
  MagicFunction.a.ComplexIntegrands
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open scoped Function UpperHalfPlane

namespace MagicFunction.a.Integrability

/-- On the segments of `Φ₁`, `Φ₃` and `Φ₅`, the integrand is `I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2`
times the exponential of a point `w` of imaginary part `t`; for `r ≥ 0` it is bounded on
`Ioc 0 1`, since `-1 / (I * t)` has imaginary part `1 / t ≥ 1`. -/
private lemma norm_le_of_mem_Ioc : ∃ C₀, ∀ r ≥ (0 : ℝ), ∀ (w : ℂ), ∀ t ∈ Ioc (0 : ℝ) 1,
    w.im = t → ‖I * (φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (π * I * r * w))‖ ≤ C₀ := by
  obtain ⟨C₀, hC₀, h⟩ := norm_φ₀_le
  refine ⟨C₀, fun r hr w t ht hw ↦ ?_⟩
  obtain ⟨ht₀, ht₁⟩ := ht
  have him : (-1 / (I * t)).im = 1 / t := by
    field_simp
    simp [div_eq_mul_inv]
    field_simp
  have hhalf : 1 / 2 < (-1 / (I * t)).im := by
    rw [him, lt_div_iff₀ ht₀]
    linarith
  have hφ : ‖φ₀'' (-1 / (I * t))‖ ≤ C₀ := by
    have hpos : 0 < (-1 / (I * t)).im := by linarith
    rw [φ₀''_def hpos]
    refine (h ⟨_, hpos⟩ hhalf).trans (mul_le_of_le_one_right hC₀.le (Real.exp_le_one_iff.2 ?_))
    change -2 * π * (-1 / (I * t)).im ≤ 0
    rw [him]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [pi_pos]) (by positivity)
  have hpow : ‖(I * t) ^ 2‖ ≤ 1 := by
    rw [norm_pow, norm_mul, norm_I, one_mul, norm_real, norm_eq_abs, abs_of_pos ht₀]
    nlinarith
  have hexp : ‖cexp (π * I * r * w)‖ ≤ 1 := by
    rw [norm_exp]
    refine Real.exp_le_one_iff.2 ?_
    simp [hw]
    have := pi_pos
    positivity
  rw [norm_mul, norm_I, one_mul, norm_mul, norm_mul]
  calc ‖φ₀'' (-1 / (I * t))‖ * ‖(I * t) ^ 2‖ * ‖cexp (π * I * r * w)‖ ≤ C₀ * 1 * 1 := by
        gcongr
  _ = C₀ := by ring

theorem Φ₁_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₁ r)
    (Ioc (0 : ℝ) 1) volume := by
  have hc := (Φ₁_contDiffOn (r := r)).continuousOn
  obtain ⟨C₀, h⟩ := norm_le_of_mem_Ioc
  replace h : ∀ t ∈ Ioc (0 : ℝ) 1, ‖Φ₁ r t‖ ≤ C₀ := fun t ht ↦ by
    have hz := z₁'_eq_of_mem (mem_Icc_of_Ioc ht)
    rw [Φ₁, Φ₁', show z₁' t + 1 = I * t by rw [hz]; ring]
    exact h r hr _ t ht (by simp [hz])
  endpoint_integrability

theorem Φ₂_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₂ r)
    (Icc (0 : ℝ) 1) volume := by
  have hc := (Φ₂_contDiffOn (r := r)).continuousOn
  endpoint_integrability

theorem Φ₃_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₃ r)
    (Ioc (0 : ℝ) 1) volume := by
  have hc := (Φ₃_contDiffOn (r := r)).continuousOn
  obtain ⟨C₀, h⟩ := norm_le_of_mem_Ioc
  replace h : ∀ t ∈ Ioc (0 : ℝ) 1, ‖Φ₃ r t‖ ≤ C₀ := fun t ht ↦ by
    have hz := z₃'_eq_of_mem (mem_Icc_of_Ioc ht)
    rw [Φ₃, Φ₃', show z₃' t - 1 = I * t by rw [hz]; ring]
    exact h r hr _ t ht (by simp [hz])
  endpoint_integrability

theorem Φ₄_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₄ r)
    (Icc (0 : ℝ) 1) volume := by
  have hc := (Φ₄_contDiffOn (r := r)).continuousOn
  endpoint_integrability

theorem Φ₅_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₅ r)
    (Ioc (0 : ℝ) 1) volume := by
  have hc := (Φ₅_contDiffOn (r := r)).continuousOn
  obtain ⟨C₀, h⟩ := norm_le_of_mem_Ioc
  have hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖Φ₅ r t‖ ≤ C₀ := fun t ht ↦ by
    have hz := z₅'_eq_of_mem (mem_Icc_of_Ioc ht)
    rw [Φ₅, Φ₅', hz]
    exact h r hr _ t ht (by simp)
  endpoint_integrability

theorem Φ₆_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₆ r)
    (Ici (1 : ℝ)) volume := by
  have hc := (Φ₆_contDiffOn (r := r)).continuousOn
  obtain ⟨C₀, -, hC₀⟩ := IntegralEstimates.I₆.I₆'_bounding_aux_2 r
  replace hC₀ : ∀ t ∈ Ici (1 : ℝ), ‖Φ₆ r t‖ ≤ C₀ * rexp (-2 * π * t) * rexp (-π * r * t) := by
    intro t ht
    convert hC₀ t ht using 2
    simp only [Φ₆, Φ₆', z₆'_eq_of_mem ht, IntegralEstimates.I₆.g]
    rw [← mul_assoc]
    congr 2
    linear_combination (π * r * t : ℂ) * I_sq
  endpoint_integrability

end MagicFunction.a.Integrability
