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
import SpherePacking.MagicFunction.a.Integrability.ProductIntegrability

/-! # Integrability

In this file, we prove that the integrands `Φⱼ` are integrable.
-/

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound MagicFunction.a.RealIntegrands
  MagicFunction.a.ComplexIntegrands MagicFunction.a.IntegralEstimates.I₆
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open scoped Function UpperHalfPlane

namespace MagicFunction.a.Integrability

/-! ### Helper lemmas for I² simplification and super-exponential decay -/

/-- Key identity: π * I * r * (I * t) = -π * r * t (since I² = -1). -/
private lemma pi_I_mul_I (r t : ℝ) : (↑π * I * ↑r * (I * ↑t) : ℂ) = -(↑π * ↑r * ↑t) := by
  ring_nf
  simp only [I_sq]
  ring

/-- Exponential form: cexp(π * I * r * (I * t)) = cexp(-π * r * t). -/
private lemma cexp_pi_I_mul_I (r t : ℝ) :
    cexp (↑π * I * ↑r * (I * ↑t)) = cexp (-(↑π * ↑r * ↑t : ℂ)) := by
  rw [pi_I_mul_I]

/-- Square of I*t: (I * t)² = -t² (since I² = -1). -/
private lemma I_mul_sq (t : ℝ) : (I * ↑t : ℂ) ^ 2 = -(↑t : ℂ) ^ 2 := by
  rw [mul_pow, I_sq]
  ring

/-- Norm of cexp of pure imaginary is 1 (special case: ±π * I * r). -/
private lemma norm_cexp_pi_I_mul (r : ℝ) : ‖cexp (↑π * I * ↑r)‖ = 1 := by
  have h : (↑π * I * ↑r : ℂ) = ↑(π * r) * I := by push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private lemma norm_cexp_neg_pi_I_mul (r : ℝ) : ‖cexp (-↑π * I * ↑r)‖ = 1 := by
  have h : (-↑π * I * ↑r : ℂ) = ↑(-(π * r)) * I := by push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- For t ∈ (0, 1], exp(-2π/t) * t² ≤ exp(-2π).
Uses exp(-2π/t) ≤ exp(-2π) from `exp_neg_div_le_of_le_one` and t² ≤ 1. -/
lemma exp_neg_two_pi_div_mul_sq_le {t : ℝ} (ht_pos : 0 < t) (ht_le : t ≤ 1) :
    rexp (-2 * π / t) * t ^ 2 ≤ rexp (-2 * π) := by
  have h_exp := exp_neg_div_le_of_le_one (2 * π) t (by linarith [Real.pi_pos]) ht_pos ht_le
  have h1 : rexp (-2 * π / t) ≤ rexp (-2 * π) := by convert h_exp using 2 <;> ring
  calc rexp (-2 * π / t) * t ^ 2 ≤ rexp (-2 * π) * t ^ 2 := by gcongr
    _ ≤ rexp (-2 * π) * 1 := by gcongr; nlinarith
    _ = rexp (-2 * π) := mul_one _

/-- For t ∈ [1, ∞), the real integrand Φ₆ r t equals the g function from IntegralEstimates.I₆. -/
lemma Φ₆_eq_I₆_g (r : ℝ) (t : ℝ) (ht : t ∈ Ici 1) : Φ₆ r t = g r t := by
  unfold Φ₆ Φ₆' g
  simp only [z₆'_eq_of_mem ht, pi_I_mul_I]
  ring_nf

/-- Φ₁ equals Φ₅ times a unit-modulus phase factor cexp(-πIr).
The key insight is that z₁' t + 1 = I*t = z₅' t. -/
lemma Φ₁_eq_Φ₅_mul_phase {r : ℝ} {t : ℝ} (ht : t ∈ Icc 0 1) :
    Φ₁ r t = Φ₅ r t * cexp (-π * I * r) := by
  simp only [Φ₁, Φ₅, Φ₁', Φ₅', z₁'_eq_of_mem ht, z₅'_eq_of_mem ht]
  have h_add : (-1 : ℂ) + I * ↑t + 1 = I * ↑t := by ring
  have h_exp1 : cexp (↑π * I * ↑r * (-1 + I * ↑t)) =
      cexp (-↑π * I * ↑r) * cexp (-↑π * ↑r * ↑t) := by
    rw [← Complex.exp_add]
    congr 1
    ring_nf
    simp only [I_sq]
    ring
  rw [h_add, h_exp1, cexp_pi_I_mul_I]
  ring

/-- Φ₃ equals Φ₅ times a unit-modulus phase factor cexp(πIr).
The key insight is that z₃' t - 1 = I*t = z₅' t. -/
lemma Φ₃_eq_Φ₅_mul_phase {r : ℝ} {t : ℝ} (ht : t ∈ Icc 0 1) :
    Φ₃ r t = Φ₅ r t * cexp (π * I * r) := by
  simp only [Φ₃, Φ₅, Φ₃', Φ₅', z₃'_eq_of_mem ht, z₅'_eq_of_mem ht]
  have h_sub : (1 : ℂ) + I * ↑t - 1 = I * ↑t := by ring
  have h_exp3 : cexp (↑π * I * ↑r * (1 + I * ↑t)) =
      cexp (↑π * I * ↑r) * cexp (-↑π * ↑r * ↑t) := by
    rw [← Complex.exp_add]
    congr 1
    ring_nf
    simp only [I_sq]
    ring
  rw [h_sub, h_exp3, cexp_pi_I_mul_I]
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
  simp only [Φ₅, Φ₅', z₅'_eq_of_mem ht']
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, I_mul_sq,
      norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1,
      cexp_pi_I_mul_I, Complex.norm_exp, one_mul]
  simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  have h_φ : ‖φ₀'' (-1 / (I * ↑t))‖ ≤ C₀ * rexp (-2 * π / t) := hC₀_bound t ht.1 ht.2
  have h_exp_r : rexp (-(π * r * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    apply neg_nonpos_of_nonneg
    exact mul_nonneg (mul_nonneg Real.pi_pos.le hr) ht.1.le
  calc ‖φ₀'' (-1 / (I * ↑t))‖ * t ^ 2 * rexp (-(π * r * t))
      ≤ ‖φ₀'' (-1 / (I * ↑t))‖ * t ^ 2 := mul_le_of_le_one_right (by positivity) h_exp_r
    _ ≤ (C₀ * rexp (-2 * π / t)) * t ^ 2 := by gcongr
    _ = C₀ * (rexp (-2 * π / t) * t ^ 2) := by ring
    _ ≤ C₀ * rexp (-2 * π) := by gcongr; exact exp_neg_two_pi_div_mul_sq_le ht.1 ht.2

/-- Norm bound for Φ₁: ‖Φ₁ r t‖ ≤ C₀ * exp(-2π) for t ∈ (0, 1] and r ≥ 0.

Since Φ₁ = Φ₅ * (unit-modulus phase), we have ‖Φ₁‖ = ‖Φ₅‖. -/
lemma norm_Φ₁_le {r : ℝ} (hr : r ≥ 0) :
    ∃ C₀ > 0, ∀ t : ℝ, t ∈ Ioc 0 1 → ‖Φ₁ r t‖ ≤ C₀ * rexp (-2 * π) := by
  obtain ⟨C₀, hC₀_pos, hC₀_bound⟩ := norm_Φ₅_le hr
  refine ⟨C₀, hC₀_pos, fun t ht => ?_⟩
  rw [Φ₁_eq_Φ₅_mul_phase (mem_Icc_of_Ioc ht), norm_mul, norm_cexp_neg_pi_I_mul, mul_one]
  exact hC₀_bound t ht

/-- Norm bound for Φ₃: ‖Φ₃ r t‖ ≤ C₀ * exp(-2π) for t ∈ (0, 1] and r ≥ 0.
Since Φ₃ = Φ₅ * (unit-modulus phase), we have ‖Φ₃‖ = ‖Φ₅‖. -/
lemma norm_Φ₃_le {r : ℝ} (hr : r ≥ 0) :
    ∃ C₀ > 0, ∀ t : ℝ, t ∈ Ioc 0 1 → ‖Φ₃ r t‖ ≤ C₀ * rexp (-2 * π) := by
  obtain ⟨C₀, hC₀_pos, hC₀_bound⟩ := norm_Φ₅_le hr
  refine ⟨C₀, hC₀_pos, fun t ht => ?_⟩
  rw [Φ₃_eq_Φ₅_mul_phase (mem_Icc_of_Ioc ht), norm_mul, norm_cexp_pi_I_mul, mul_one]
  exact hC₀_bound t ht

/-- Helper: A function bounded by a constant on Ioc 0 1 is integrable there. -/
private theorem integrableOn_Ioc_of_norm_le_const {f : ℝ → ℂ} {C : ℝ}
    (hf_cont : ContinuousOn f (Ioc 0 1))
    (hf_bound : ∀ t ∈ Ioc 0 1, ‖f t‖ ≤ C) : IntegrableOn f (Ioc 0 1) volume := by
  have h_const_int : IntegrableOn (fun _ : ℝ => C) (Ioc 0 1) volume :=
    integrableOn_const (by simp [Real.volume_Ioc]) ENNReal.coe_ne_top
  refine Integrable.mono' h_const_int ?_ ?_
  · exact hf_cont.aestronglyMeasurable measurableSet_Ioc
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact ae_of_all _ hf_bound

/-- Φ₁ is integrable on (0, 1]. -/
theorem Φ₁_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₁ r) (Ioc 0 1) volume := by
  obtain ⟨C₀, _, hC₀_bound⟩ := norm_Φ₁_le hr
  exact integrableOn_Ioc_of_norm_le_const Φ₁_contDiffOn.continuousOn hC₀_bound

theorem Φ₂_integrableOn {r : ℝ} (_hr : r ≥ 0) : IntegrableOn (Φ₂ r)
    (Icc (0 : ℝ) 1) volume :=
  Φ₂_contDiffOn.continuousOn.integrableOn_Icc

/-- Φ₃ is integrable on (0, 1]. -/
theorem Φ₃_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₃ r) (Ioc 0 1) volume := by
  obtain ⟨C₀, _, hC₀_bound⟩ := norm_Φ₃_le hr
  exact integrableOn_Ioc_of_norm_le_const Φ₃_contDiffOn.continuousOn hC₀_bound

theorem Φ₄_integrableOn {r : ℝ} (_hr : r ≥ 0) : IntegrableOn (Φ₄ r) (Icc 0 1) volume :=
  Φ₄_contDiffOn.continuousOn.integrableOn_Icc

/-- Φ₅ is integrable on (0, 1]. -/
theorem Φ₅_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₅ r) (Ioc 0 1) volume := by
  obtain ⟨C₀, _, hC₀_bound⟩ := norm_Φ₅_le hr
  exact integrableOn_Ioc_of_norm_le_const Φ₅_contDiffOn.continuousOn hC₀_bound

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
