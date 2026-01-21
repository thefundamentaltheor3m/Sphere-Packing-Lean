/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.Exponential

/-!
# Exponential Decay Integrability Lemmas (Tail Regime)

This file provides pure real analysis lemmas for integrability of exponentially
decaying functions in the tail regime (t → ∞), particularly polynomial × exponential
patterns.

These lemmas are designed to be reusable for contour integral analysis where:
- For r > 2, exponential decay beats polynomial growth in vertical ray integrands

## Main results

### Asymptotic behavior
- `tendsto_exp_neg_atTop`: exp(-a*t) → 0 as t → ∞ for a > 0
- `tendsto_mul_exp_neg_atTop`: t * exp(-a*t) → 0 as t → ∞ for a > 0
- `tendsto_sq_mul_exp_neg_atTop`: t² * exp(-a*t) → 0 as t → ∞ for a > 0

### Integrability
- `integrableOn_exp_mul_Ici`: exp(c*t) is integrable on [1,∞) for c < 0
- `integrableOn_mul_exp_neg_Ici`: t * exp(-a*t) is integrable on [1,∞) for a > 0
- `integrableOn_sq_mul_exp_neg_Ici`: t² * exp(-a*t) is integrable on [1,∞) for a > 0

## References

These patterns appear in the magic function integrability proofs for sphere packing,
specifically for vertical ray integrands in ContourEndpoints.lean.
-/

open MeasureTheory Set Filter Real

noncomputable section

/-! ## Integrability Lemmas -/

section Integrability

/-- exp(c*t) is integrable on [1,∞) for c < 0. -/
lemma integrableOn_exp_mul_Ici (c : ℝ) (hc : c < 0) :
    IntegrableOn (fun t => exp (c * t)) (Ici 1) volume :=
  (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_exp_mul_Ioi hc 1)

/-- t * exp(-a*t) → 0 as t → ∞ for a > 0. -/
lemma tendsto_mul_exp_neg_atTop (a : ℝ) (ha : 0 < a) :
    Tendsto (fun t => t * exp (-a * t)) atTop (nhds 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha
  simp only [rpow_one] at h
  exact h

/-- t² * exp(-a*t) → 0 as t → ∞ for a > 0. -/
lemma tendsto_sq_mul_exp_neg_atTop (a : ℝ) (ha : 0 < a) :
    Tendsto (fun t => t^2 * exp (-a * t)) atTop (nhds 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 a ha
  simp only [rpow_two] at h
  exact h

/-- exp(-a*t) → 0 as t → ∞ for a > 0. -/
lemma tendsto_exp_neg_atTop (a : ℝ) (ha : 0 < a) :
    Tendsto (fun t => exp (-a * t)) atTop (nhds 0) := by
  -- Use t^0 * exp(-at) → 0 from mathlib
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 a ha
  simp only [rpow_zero, one_mul] at h
  exact h

/-- t * exp(-a*t) is integrable on [1,∞) for a > 0. -/
lemma integrableOn_mul_exp_neg_Ici (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t => t * exp (-a * t)) (Ici 1) volume := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply integrable_of_isBigO_exp_neg (b := a / 2) (by linarith : 0 < a / 2)
  · apply Continuous.continuousOn
    exact continuous_id.mul (continuous_exp.comp (continuous_const.mul continuous_id))
  · -- t * exp(-at) = O(exp(-at/2)) as t → ∞
    -- Since t * exp(-at/2) → 0, eventually bounded by 1
    have h := tendsto_mul_exp_neg_atTop (a/2) (by linarith)
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N, hN⟩ := h 1 (by linarith)
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Filter.eventually_ge_atTop (max N 1)] with t ht
    have ht_ge_N : t ≥ N := le_of_max_le_left ht
    have ht_ge_1 : t ≥ 1 := le_of_max_le_right ht
    have ht_pos : 0 < t := by linarith
    simp only [one_mul, norm_mul, Real.norm_eq_abs]
    rw [abs_of_pos ht_pos, abs_of_pos (exp_pos _), abs_of_pos (exp_pos _)]
    have h1 := hN t ht_ge_N
    simp only [dist_zero_right, Real.norm_eq_abs] at h1
    rw [abs_of_pos (by positivity : 0 < t * exp (-(a/2) * t))] at h1
    calc t * exp (-a * t)
        = t * (exp (-(a/2) * t) * exp (-(a/2) * t)) := by rw [← exp_add]; ring_nf
      _ = (t * exp (-(a/2) * t)) * exp (-(a/2) * t) := by ring
      _ ≤ 1 * exp (-(a/2) * t) := by
          apply mul_le_mul_of_nonneg_right (le_of_lt h1) (exp_pos _).le
      _ = exp (-(a / 2) * t) := one_mul _

/-- t² * exp(-a*t) is integrable on [1,∞) for a > 0. -/
lemma integrableOn_sq_mul_exp_neg_Ici (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t => t^2 * exp (-a * t)) (Ici 1) volume := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply integrable_of_isBigO_exp_neg (b := a / 2) (by linarith : 0 < a / 2)
  · apply Continuous.continuousOn
    exact (continuous_pow 2).mul (continuous_exp.comp (continuous_const.mul continuous_id))
  · -- t² * exp(-at) = O(exp(-at/2)) as t → ∞
    have h := tendsto_sq_mul_exp_neg_atTop (a/2) (by linarith)
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N, hN⟩ := h 1 (by linarith)
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Filter.eventually_ge_atTop (max N 1)] with t ht
    have ht_ge_N : t ≥ N := le_of_max_le_left ht
    have ht_ge_1 : t ≥ 1 := le_of_max_le_right ht
    have ht_pos : 0 < t := by linarith
    simp only [one_mul, norm_mul, Real.norm_eq_abs]
    rw [abs_of_pos (sq_pos_of_pos ht_pos), abs_of_pos (exp_pos _), abs_of_pos (exp_pos _)]
    have h1 := hN t ht_ge_N
    simp only [dist_zero_right, Real.norm_eq_abs] at h1
    rw [abs_of_pos (by positivity : 0 < t^2 * exp (-(a/2) * t))] at h1
    calc t^2 * exp (-a * t)
        = t^2 * (exp (-(a/2) * t) * exp (-(a/2) * t)) := by rw [← exp_add]; ring_nf
      _ = (t^2 * exp (-(a/2) * t)) * exp (-(a/2) * t) := by ring
      _ ≤ 1 * exp (-(a/2) * t) := by
          apply mul_le_mul_of_nonneg_right (le_of_lt h1) (exp_pos _).le
      _ = exp (-(a / 2) * t) := one_mul _

end Integrability

/-! ## Near-Zero Regime (t → 0)

Lemmas for `exp(-c/t)` patterns near 0, where super-exponential decay dominates any polynomial.
These are essential for cusp-approaching contour segments (I₁, I₃, I₅) where we integrate
over (0,1] with z = -1/(it), so Im(z) = 1/t → ∞ as t → 0.
-/

section NearZero

/-! ### Comparison Lemmas -/

/-- exp(-c/t) ≤ exp(-c) for 0 < t ≤ 1 and c > 0.
    When 0 < t ≤ 1, we have 1/t ≥ 1, so c/t ≥ c, so -c/t ≤ -c. -/
lemma exp_neg_div_le_of_le_one (c t : ℝ) (hc : 0 < c) (ht_pos : 0 < t) (ht : t ≤ 1) :
    exp (-c / t) ≤ exp (-c) := by
  rw [exp_le_exp, neg_div, neg_le_neg_iff, le_div_iff₀ ht_pos]
  nlinarith

/-- For s ≥ 1, exp(-c*r/s) ≤ exp(c*|r|).
    This bounds a secondary exponential factor uniformly. -/
lemma exp_neg_mul_div_le_exp_abs (c r s : ℝ) (hc : 0 ≤ c) (hs : 1 ≤ s) :
    exp (-c * r / s) ≤ exp (c * |r|) := by
  apply exp_le_exp.mpr
  have h1 : -c * r / s ≤ |c * r| / s := by
    apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ s)
    simp only [neg_mul]; exact neg_le_abs _
  have h2 : |c * r| / s ≤ c * |r| := by
    rw [abs_mul, abs_of_nonneg hc]; exact div_le_self (by positivity) hs
  linarith

/-- exp(-c/t) * t⁻² ≤ exp(-c) for t ∈ (0,1] and c ≥ 2.
    The super-exponential decay dominates the polynomial singularity.
    Uses substitution u = 1/t and the inequality log(u) ≤ u - 1. -/
lemma exp_neg_div_mul_inv_sq_le (c t : ℝ) (hc : 2 ≤ c) (ht_pos : 0 < t) (ht : t ≤ 1) :
    exp (-c / t) * t⁻¹^2 ≤ exp (-c) := by
  have h_u_ge_1 : 1 ≤ t⁻¹ := one_le_inv_iff₀.mpr ⟨ht_pos, ht⟩
  -- Substitute u = 1/t, so u ≥ 1
  set u := t⁻¹ with hu_def
  have h_u_pos : 0 < u := by positivity
  -- The function is exp(-c*u) * u²
  have h_eq : exp (-c / t) * t⁻¹^2 = exp (-c * u) * u^2 := by
    simp only [hu_def, div_eq_mul_inv]
  rw [h_eq]
  -- For u ≥ 1, we need exp(-c*u) * u² ≤ exp(-c)
  -- Equivalently: u² ≤ exp(c(u-1))
  -- This follows from 2*log(u) ≤ c(u-1), which holds when c/2 ≥ 1
  have h_ineq : u^2 ≤ exp (c * (u - 1)) := by
    by_cases hu1 : u = 1
    · simp [hu1]
    · have hu1' : 1 < u := lt_of_le_of_ne h_u_ge_1 (Ne.symm hu1)
      -- log(u) ≤ u - 1 for u > 0, and (c/2)(u-1) ≥ u - 1 when c/2 ≥ 1
      have hlog : log u ≤ u - 1 := log_le_sub_one_of_pos h_u_pos
      have h5 : u - 1 ≤ (c / 2) * (u - 1) := by
        have hu_sub : 0 < u - 1 := by linarith
        have hc2 : 1 ≤ c / 2 := by linarith
        calc u - 1 = 1 * (u - 1) := by ring
          _ ≤ (c / 2) * (u - 1) := mul_le_mul_of_nonneg_right hc2 (le_of_lt hu_sub)
      have h6 : log u ≤ (c / 2) * (u - 1) := le_trans hlog h5
      have h7 : 2 * log u ≤ c * (u - 1) := by linarith
      calc u^2 = exp (log (u^2)) := by rw [exp_log]; positivity
        _ = exp (2 * log u) := by rw [log_pow]; ring_nf
        _ ≤ exp (c * (u - 1)) := exp_le_exp.mpr h7
  -- Now: exp(-c*u) * u² = exp(-c) * exp(-c(u-1)) * u² ≤ exp(-c) * 1
  have h_split : exp (-c * u) = exp (-c) * exp (-c * (u - 1)) := by
    rw [← exp_add]; ring_nf
  rw [h_split, mul_assoc]
  apply mul_le_of_le_one_right (exp_pos _).le
  -- Need: exp(-c(u-1)) * u² ≤ 1
  rw [mul_comm]
  have h_exp_pos : 0 < exp (c * (u - 1)) := exp_pos _
  calc u^2 * exp (-c * (u - 1))
      = u^2 / exp (c * (u - 1)) := by
        rw [div_eq_mul_inv, ← exp_neg]; ring_nf
    _ ≤ exp (c * (u - 1)) / exp (c * (u - 1)) :=
        div_le_div_of_nonneg_right h_ineq h_exp_pos.le
    _ = 1 := div_self (ne_of_gt h_exp_pos)

/-! ### Asymptotic Behavior -/

/-- exp(-c/t) → 0 as t → 0⁺ for c > 0.
    The super-exponential decay dominates any polynomial growth. -/
lemma exp_neg_div_tendsto_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun t => exp (-c / t)) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  -- As t → 0⁺, -c/t → -∞, so exp(-c/t) → 0
  have h1 : Tendsto (fun t => -c / t) (nhdsWithin 0 (Ioi 0)) atBot := by
    have h_inv : Tendsto (fun t : ℝ => t⁻¹) (nhdsWithin 0 (Ioi 0)) atTop :=
      tendsto_inv_nhdsGT_zero
    have h_eq : (fun t : ℝ => -c / t) = fun t => -c * t⁻¹ := by ext t; ring
    rw [h_eq]
    exact h_inv.const_mul_atTop_of_neg (neg_lt_zero.mpr hc)
  exact tendsto_exp_atBot.comp h1

/-- exp(-c/t) is always positive. -/
lemma exp_neg_div_pos (c t : ℝ) : 0 < exp (-c / t) := exp_pos _

/-! ### Integrability Lemmas -/

/-- t^(-2) * exp(c*t) is integrable on [1,∞) for c < 0.
    Polynomial decay × exponential decay is integrable. -/
lemma integrableOn_inv_sq_mul_exp_Ici (c : ℝ) (hc : c < 0) :
    IntegrableOn (fun t => t^(-2 : ℝ) * exp (c * t)) (Ici 1) volume := by
  -- For t ≥ 1: t^(-2) ≤ 1, so |t^(-2) * exp(c*t)| ≤ exp(c*t)
  have h_exp : IntegrableOn (fun t => exp (c * t)) (Ici 1) volume :=
    integrableOn_exp_mul_Ici c hc
  apply Integrable.mono h_exp (by measurability)
  rw [ae_restrict_iff' measurableSet_Ici]
  apply ae_of_all
  intro t ht
  simp only [mem_Ici] at ht
  have ht_pos : 0 < t := by linarith
  have h1 : t^(-2 : ℝ) ≤ 1 := by
    rw [rpow_neg ht_pos.le, rpow_two]
    exact inv_le_one_of_one_le₀ (by nlinarith : 1 ≤ t ^ 2)
  simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (rpow_pos_of_pos ht_pos _),
             abs_of_pos (exp_pos _)]
  exact mul_le_of_le_one_left (exp_pos _).le h1

/-- exp(-c/t) is integrable on (0, 1] for c > 0.
    Change of variables: u = 1/t transforms ∫₀¹ exp(-c/t) dt to ∫₁^∞ exp(-c*u) * u⁻² du.
    The latter is integrable since exp(-c*u) decays faster than u² grows. -/
lemma integrableOn_exp_neg_div_Ioc (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun t => exp (-c / t)) (Ioc 0 1) volume := by
  -- Strategy: bound exp(-c/t) ≤ exp(-c) on (0,1], then use finite measure
  have h_bound : ∀ t ∈ Ioc (0 : ℝ) 1, exp (-c / t) ≤ exp (-c) := fun t ht =>
    exp_neg_div_le_of_le_one c t hc ht.1 ht.2
  -- exp(-c) is a constant, and Ioc 0 1 has finite measure
  have h_const : IntegrableOn (fun (_ : ℝ) => exp (-c)) (Ioc 0 1) volume :=
    integrableOn_const (by simp [Real.volume_Ioc])
  apply Integrable.mono h_const (by measurability)
  rw [ae_restrict_iff' measurableSet_Ioc]
  apply ae_of_all
  intro t ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _), abs_of_pos (exp_pos _)]
  exact h_bound t ht

end NearZero

end
