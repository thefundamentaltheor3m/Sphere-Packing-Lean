/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import SpherePacking.MagicFunction.a.IntegralEstimates.I1
import SpherePacking.MagicFunction.a.IntegralEstimates.I2
import SpherePacking.MagicFunction.a.IntegralEstimates.I3
import SpherePacking.MagicFunction.a.IntegralEstimates.I4
import SpherePacking.MagicFunction.a.IntegralEstimates.I5
import SpherePacking.MagicFunction.a.IntegralEstimates.I6
import SpherePacking.MagicFunction.a.Integrability.RealIntegrands
import SpherePacking.MagicFunction.RealDecay
import SpherePacking.MagicFunction.Segments

/-! # Integrability

In this file, we prove that the integrands `Φⱼ` are integrable.
-/

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound MagicFunction.a.RealIntegrands
  MagicFunction.a.ComplexIntegrands MagicFunction.a.IntegralEstimates.I₆
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open scoped Function UpperHalfPlane

namespace MagicFunction.a.Integrability

/-! ### Helper lemmas for super-exponential decay -/

/-- For t ∈ (0, 1], exp(-2π/t) * t² is monotonically increasing and bounded by exp(-2π).
This is because exp(-2π/t) decays super-exponentially as t → 0, dominating the t² growth. -/
lemma exp_neg_two_pi_div_mul_sq_le {t : ℝ} (ht_pos : 0 < t) (ht_le : t ≤ 1) :
    rexp (-2 * π / t) * t ^ 2 ≤ rexp (-2 * π) := by
  -- From exp_neg_div_mul_inv_sq_le with c = 2π: exp(-2π/t) * t⁻² ≤ exp(-2π)
  -- So: exp(-2π/t) ≤ exp(-2π) * t²
  -- Hence: exp(-2π/t) * t² ≤ exp(-2π) * t⁴ ≤ exp(-2π)
  have hc : 2 ≤ 2 * π := by linarith [Real.two_le_pi]
  have h := exp_neg_div_mul_inv_sq_le (2 * π) t hc ht_pos ht_le
  -- h : exp(-2π/t) * t⁻¹² ≤ exp(-2π)
  -- Rewrite t⁻¹² = (t²)⁻¹
  have h_inv : t⁻¹ ^ 2 = (t ^ 2)⁻¹ := by rw [inv_pow]
  rw [h_inv] at h
  -- Now h : exp(-2π/t) * (t²)⁻¹ ≤ exp(-2π)
  -- Multiply both sides by t² to get: exp(-2π/t) ≤ exp(-2π) * t²
  have ht2_pos : 0 < t ^ 2 := by positivity
  have h' : rexp (-2 * π / t) ≤ rexp (-2 * π) * t ^ 2 := by
    have := mul_le_mul_of_nonneg_right h ht2_pos.le
    simp only [mul_assoc, inv_mul_cancel₀ (ne_of_gt ht2_pos), mul_one] at this
    convert this using 2 <;> ring
  -- Now multiply by t² again: exp(-2π/t) * t² ≤ exp(-2π) * t⁴
  have h_t4 : t ^ 4 ≤ 1 := by
    have h1 : t ^ 4 ≤ t ^ 2 := by
      have : t ^ 4 = t ^ 2 * t ^ 2 := by ring
      have : t ^ 2 ≤ 1 := by nlinarith
      nlinarith
    have h2 : t ^ 2 ≤ 1 := by nlinarith
    linarith
  calc rexp (-2 * π / t) * t ^ 2 ≤ (rexp (-2 * π) * t ^ 2) * t ^ 2 := by
          apply mul_le_mul_of_nonneg_right h' (sq_nonneg t)
    _ = rexp (-2 * π) * t ^ 4 := by ring
    _ ≤ rexp (-2 * π) * 1 := by gcongr
    _ = rexp (-2 * π) := mul_one _

/-- For t ∈ [1, ∞), the real integrand Φ₆ r t equals the g function from IntegralEstimates.I₆. -/
lemma Φ₆_eq_I₆_g (r : ℝ) (t : ℝ) (ht : t ∈ Ici 1) : Φ₆ r t = g r t := by
  unfold Φ₆ Φ₆' g
  simp only [z₆'_eq_of_mem ht]
  have h : (π : ℂ) * I * ↑r * (I * ↑t) = -((π : ℂ) * ↑r * ↑t) := by
    ring_nf
    simp only [I_sq]
    ring
  rw [h]
  ring

/-- Φ₁ equals Φ₅ times a unit-modulus phase factor cexp(-πIr).

The key insight is that z₁' t + 1 = I*t = z₅' t, so the φ₀'' and z² factors
are identical, and only the exponential differs by the phase cexp(-πIr). -/
lemma Φ₁_eq_Φ₅_mul_phase {r : ℝ} {t : ℝ} (ht : t ∈ Icc 0 1) :
    Φ₁ r t = Φ₅ r t * cexp (-π * I * r) := by
  simp only [Φ₁, Φ₅, Φ₁', Φ₅', z₁'_eq_of_mem ht, z₅'_eq_of_mem ht]
  -- z₁' t + 1 = -1 + I*t + 1 = I*t, and z₅' t = I*t
  have h_add : (-1 : ℂ) + I * ↑t + 1 = I * ↑t := by ring
  rw [h_add]
  -- The exponential factors: cexp(π*I*r*(-1 + I*t)) = cexp(-π*I*r) * cexp(-π*r*t)
  -- and cexp(π*I*r*(I*t)) = cexp(-π*r*t)
  have h_exp1 :
      cexp (↑π * I * ↑r * (-1 + I * ↑t)) = cexp (-↑π * I * ↑r) * cexp (-↑π * ↑r * ↑t) := by
    rw [← Complex.exp_add]
    congr 1
    have : I * I = (-1 : ℂ) := I_mul_I
    calc ↑π * I * ↑r * (-1 + I * ↑t) = -↑π * I * ↑r + ↑π * (I * I) * ↑r * ↑t := by ring
      _ = -↑π * I * ↑r + ↑π * (-1) * ↑r * ↑t := by rw [this]
      _ = -↑π * I * ↑r + (-↑π * ↑r * ↑t) := by ring
  have h_exp5 : cexp (↑π * I * ↑r * (I * ↑t)) = cexp (-↑π * ↑r * ↑t) := by
    congr 1
    have : I * I = (-1 : ℂ) := I_mul_I
    calc ↑π * I * ↑r * (I * ↑t) = ↑π * (I * I) * ↑r * ↑t := by ring
      _ = ↑π * (-1) * ↑r * ↑t := by rw [this]
      _ = -↑π * ↑r * ↑t := by ring
  rw [h_exp1, h_exp5]
  ring

/-- Φ₃ equals Φ₅ times a unit-modulus phase factor cexp(πIr).

The key insight is that z₃' t - 1 = I*t = z₅' t, so the φ₀'' and z² factors
are identical, and only the exponential differs by the phase cexp(πIr). -/
lemma Φ₃_eq_Φ₅_mul_phase {r : ℝ} {t : ℝ} (ht : t ∈ Icc 0 1) :
    Φ₃ r t = Φ₅ r t * cexp (π * I * r) := by
  simp only [Φ₃, Φ₅, Φ₃', Φ₅', z₃'_eq_of_mem ht, z₅'_eq_of_mem ht]
  -- z₃' t - 1 = 1 + I*t - 1 = I*t, and z₅' t = I*t
  have h_sub : (1 : ℂ) + I * ↑t - 1 = I * ↑t := by ring
  rw [h_sub]
  -- The exponential factors: cexp(π*I*r*(1 + I*t)) = cexp(π*I*r) * cexp(-π*r*t)
  -- and cexp(π*I*r*(I*t)) = cexp(-π*r*t)
  have h_exp3 : cexp (↑π * I * ↑r * (1 + I * ↑t)) = cexp (↑π * I * ↑r) * cexp (-↑π * ↑r * ↑t) := by
    rw [← Complex.exp_add]
    congr 1
    have : I * I = (-1 : ℂ) := I_mul_I
    calc ↑π * I * ↑r * (1 + I * ↑t) = ↑π * I * ↑r + ↑π * (I * I) * ↑r * ↑t := by ring
      _ = ↑π * I * ↑r + ↑π * (-1) * ↑r * ↑t := by rw [this]
      _ = ↑π * I * ↑r + (-↑π * ↑r * ↑t) := by ring
  have h_exp5 : cexp (↑π * I * ↑r * (I * ↑t)) = cexp (-↑π * ↑r * ↑t) := by
    congr 1
    have : I * I = (-1 : ℂ) := I_mul_I
    calc ↑π * I * ↑r * (I * ↑t) = ↑π * (I * I) * ↑r * ↑t := by ring
      _ = ↑π * (-1) * ↑r * ↑t := by rw [this]
      _ = -↑π * ↑r * ↑t := by ring
  rw [h_exp3, h_exp5]
  ring

/-- Norm bound for Φ₅: ‖Φ₅ r t‖ ≤ C₀ * exp(-2π) for t ∈ (0, 1] and r ≥ 0.

Uses:
1. `norm_φ₀''_cusp_bound`: ‖φ₀''(-1/(I*t))‖ ≤ C₀ * exp(-2π/t)
2. For r ≥ 0: exp(-π*r*t) ≤ 1
3. `exp_neg_two_pi_div_mul_sq_le`: exp(-2π/t) * t² ≤ exp(-2π)

From the definition, Φ₅ r t = I * φ₀''(-1/(I*t)) * (I*t)² * cexp(-π*r*t)
                            = -I * φ₀''(-1/(I*t)) * t² * cexp(-π*r*t)
so ‖Φ₅ r t‖ = ‖φ₀''(-1/(I*t))‖ * t² * exp(-π*r*t). -/
lemma norm_Φ₅_le {r : ℝ} (hr : r ≥ 0) :
    ∃ C₀ > 0, ∀ t : ℝ, t ∈ Ioc 0 1 → ‖Φ₅ r t‖ ≤ C₀ * rexp (-2 * π) := by
  obtain ⟨C₀, hC₀_pos, hC₀_bound⟩ := norm_φ₀''_cusp_bound
  refine ⟨C₀, hC₀_pos, fun t ht => ?_⟩
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioc ht
  -- Unfold Φ₅ and compute norm
  simp only [Φ₅, Φ₅', z₅'_eq_of_mem ht']
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I]
  -- (I*t)² = -t²
  have h_sq : (I * ↑t : ℂ) ^ 2 = -(↑t : ℂ) ^ 2 := by rw [mul_pow, I_sq]; ring
  rw [h_sq, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
  -- cexp(π*I*r*(I*t)) = cexp(-π*r*t)
  have h_exp : cexp (↑π * I * ↑r * (I * ↑t)) = cexp (-(↑π * ↑r * ↑t : ℂ)) := by
    congr 1
    have : I * I = (-1 : ℂ) := I_mul_I
    calc ↑π * I * ↑r * (I * ↑t) = ↑π * (I * I) * ↑r * ↑t := by ring
      _ = ↑π * (-1) * ↑r * ↑t := by rw [this]
      _ = -(↑π * ↑r * ↑t) := by ring
  rw [h_exp, Complex.norm_exp]
  simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  -- Now we have: 1 * ‖φ₀''(...)‖ * t² * exp(-π*r*t)
  rw [one_mul]
  -- Use the φ₀'' bound and the exp bound
  have h_φ : ‖φ₀'' (-1 / (I * ↑t))‖ ≤ C₀ * rexp (-2 * π / t) := hC₀_bound t ht.1 ht.2
  have h_exp_r : rexp (-(π * r * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simp only [neg_nonpos]
    apply mul_nonneg (mul_nonneg Real.pi_pos.le hr) ht.1.le
  have h_decay : rexp (-2 * π / t) * t ^ 2 ≤ rexp (-2 * π) :=
    exp_neg_two_pi_div_mul_sq_le ht.1 ht.2
  calc ‖φ₀'' (-1 / (I * ↑t))‖ * t ^ 2 * rexp (-(π * r * t))
      ≤ ‖φ₀'' (-1 / (I * ↑t))‖ * t ^ 2 := mul_le_of_le_one_right (by positivity) h_exp_r
    _ ≤ (C₀ * rexp (-2 * π / t)) * t ^ 2 := by gcongr
    _ = C₀ * (rexp (-2 * π / t) * t ^ 2) := by ring
    _ ≤ C₀ * rexp (-2 * π) := by gcongr

/-- Norm bound for Φ₁: ‖Φ₁ r t‖ ≤ C₀ * exp(-2π) for t ∈ (0, 1] and r ≥ 0.

Since Φ₁ = Φ₅ * (unit-modulus phase), we have ‖Φ₁‖ = ‖Φ₅‖. -/
lemma norm_Φ₁_le {r : ℝ} (hr : r ≥ 0) :
    ∃ C₀ > 0, ∀ t : ℝ, t ∈ Ioc 0 1 → ‖Φ₁ r t‖ ≤ C₀ * rexp (-2 * π) := by
  obtain ⟨C₀, hC₀_pos, hC₀_bound⟩ := norm_Φ₅_le hr
  refine ⟨C₀, hC₀_pos, fun t ht => ?_⟩
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioc ht
  rw [Φ₁_eq_Φ₅_mul_phase ht', norm_mul]
  -- The phase factor has unit modulus
  have h_phase : ‖cexp (-↑π * I * ↑r)‖ = 1 := by
    rw [Complex.norm_exp]
    -- re(-π * I * r) = 0 since I.re = 0
    have : (-↑π * I * ↑r).re = 0 := by simp [Complex.mul_re]
    rw [this, Real.exp_zero]
  rw [h_phase, mul_one]
  exact hC₀_bound t ht

/-- Norm bound for Φ₃: ‖Φ₃ r t‖ ≤ C₀ * exp(-2π) for t ∈ (0, 1] and r ≥ 0.

Since Φ₃ = Φ₅ * (unit-modulus phase), we have ‖Φ₃‖ = ‖Φ₅‖. -/
lemma norm_Φ₃_le {r : ℝ} (hr : r ≥ 0) :
    ∃ C₀ > 0, ∀ t : ℝ, t ∈ Ioc 0 1 → ‖Φ₃ r t‖ ≤ C₀ * rexp (-2 * π) := by
  obtain ⟨C₀, hC₀_pos, hC₀_bound⟩ := norm_Φ₅_le hr
  refine ⟨C₀, hC₀_pos, fun t ht => ?_⟩
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioc ht
  rw [Φ₃_eq_Φ₅_mul_phase ht', norm_mul]
  -- The phase factor has unit modulus
  have h_phase : ‖cexp (↑π * I * ↑r)‖ = 1 := by
    rw [Complex.norm_exp]
    -- re(π * I * r) = 0 since I.re = 0
    have : (↑π * I * ↑r).re = 0 := by simp [Complex.mul_re]
    rw [this, Real.exp_zero]
  rw [h_phase, mul_one]
  exact hC₀_bound t ht

/-- Φ₁ is integrable on (0, 1].

Uses `norm_Φ₁_le` to bound ‖Φ₁ r t‖ by a constant C₀ * exp(-2π), which is
integrable on the finite measure space (0, 1]. -/
theorem Φ₁_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₁ r)
    (Ioc (0 : ℝ) 1) volume := by
  -- Get the constant bound
  obtain ⟨C₀, _, hC₀_bound⟩ := norm_Φ₁_le hr
  -- The constant C₀ * exp(-2π) is integrable on Ioc 0 1 (finite measure)
  have h_const_int : IntegrableOn (fun _ : ℝ => C₀ * rexp (-2 * π)) (Ioc 0 1) volume := by
    refine integrableOn_const ?_ ?_
    · simp [Real.volume_Ioc]
    · exact ENNReal.coe_ne_top
  -- Apply Integrable.mono' with the constant bound
  refine Integrable.mono' h_const_int ?_ ?_
  · exact ContinuousOn.aestronglyMeasurable Φ₁_contDiffOn.continuousOn measurableSet_Ioc
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine ae_of_all _ fun t ht => ?_
    exact hC₀_bound t ht

theorem Φ₂_integrableOn {r : ℝ} (_hr : r ≥ 0) : IntegrableOn (Φ₂ r)
    (Icc (0 : ℝ) 1) volume :=
  Φ₂_contDiffOn.continuousOn.integrableOn_Icc

/-- Φ₃ is integrable on (0, 1].

Uses `norm_Φ₃_le` to bound ‖Φ₃ r t‖ by a constant C₀ * exp(-2π), which is
integrable on the finite measure space (0, 1]. -/
theorem Φ₃_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₃ r)
    (Ioc (0 : ℝ) 1) volume := by
  -- Get the constant bound
  obtain ⟨C₀, _, hC₀_bound⟩ := norm_Φ₃_le hr
  -- The constant C₀ * exp(-2π) is integrable on Ioc 0 1 (finite measure)
  have h_const_int : IntegrableOn (fun _ : ℝ => C₀ * rexp (-2 * π)) (Ioc 0 1) volume := by
    refine integrableOn_const ?_ ?_
    · simp [Real.volume_Ioc]
    · exact ENNReal.coe_ne_top
  -- Apply Integrable.mono' with the constant bound
  refine Integrable.mono' h_const_int ?_ ?_
  · exact ContinuousOn.aestronglyMeasurable Φ₃_contDiffOn.continuousOn measurableSet_Ioc
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine ae_of_all _ fun t ht => ?_
    exact hC₀_bound t ht

theorem Φ₄_integrableOn {r : ℝ} (_hr : r ≥ 0) : IntegrableOn (Φ₄ r)
    (Icc (0 : ℝ) 1) volume :=
  Φ₄_contDiffOn.continuousOn.integrableOn_Icc

/-- Φ₅ is integrable on (0, 1].

Uses `norm_Φ₅_le` to bound ‖Φ₅ r t‖ by a constant C₀ * exp(-2π), which is
integrable on the finite measure space (0, 1]. -/
theorem Φ₅_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₅ r)
    (Ioc (0 : ℝ) 1) volume := by
  -- Get the constant bound
  obtain ⟨C₀, hC₀_pos, hC₀_bound⟩ := norm_Φ₅_le hr
  -- The constant C₀ * exp(-2π) is integrable on Ioc 0 1 (finite measure)
  have h_const_int : IntegrableOn (fun _ : ℝ => C₀ * rexp (-2 * π)) (Ioc 0 1) volume := by
    refine integrableOn_const ?_ ?_
    · simp [Real.volume_Ioc]
    · exact ENNReal.coe_ne_top
  -- Apply Integrable.mono' with the constant bound
  -- (IntegrableOn is Integrable on restricted measure)
  refine Integrable.mono' h_const_int ?_ ?_
  · exact ContinuousOn.aestronglyMeasurable Φ₅_contDiffOn.continuousOn measurableSet_Ioc
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine ae_of_all _ fun t ht => ?_
    exact hC₀_bound t ht

theorem Φ₆_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₆ r)
    (Ici (1 : ℝ)) volume := by
  -- Get the bound and its integrability from IntegralEstimates.I₆
  obtain ⟨C₀, _, hC₀_bound⟩ := I₆'_bounding_aux_2 r
  have h_bound_int : IntegrableOn
      (fun t ↦ C₀ * rexp (-2 * π * t) * rexp (-π * r * t)) (Ici 1) volume :=
    Bound_integrableOn r C₀ hr
  -- Use Integrable.mono' with the bound
  refine Integrable.mono' h_bound_int ?_ ?_
  · exact ContinuousOn.aestronglyMeasurable Φ₆_contDiffOn.continuousOn measurableSet_Ici
  · rw [ae_restrict_iff' measurableSet_Ici]
    exact ae_of_all _ fun t ht ↦ (Φ₆_eq_I₆_g r t ht).symm ▸ hC₀_bound t ht

end MagicFunction.a.Integrability
