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
    have ht_pos : 0 < t := lt_of_lt_of_le one_pos (le_of_max_le_right ht)
    simp only [one_mul, norm_mul, Real.norm_eq_abs, abs_of_pos ht_pos, abs_of_pos (exp_pos _)]
    have h1 := hN t (le_of_max_le_left ht)
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
    have ht_pos : 0 < t := lt_of_lt_of_le one_pos (le_of_max_le_right ht)
    simp only [one_mul, norm_mul, Real.norm_eq_abs, abs_of_pos (sq_pos_of_pos ht_pos),
      abs_of_pos (exp_pos _)]
    have h1 := hN t (le_of_max_le_left ht)
    simp only [dist_zero_right, Real.norm_eq_abs] at h1
    rw [abs_of_pos (by positivity : 0 < t^2 * exp (-(a/2) * t))] at h1
    calc t^2 * exp (-a * t)
        = t^2 * (exp (-(a/2) * t) * exp (-(a/2) * t)) := by rw [← exp_add]; ring_nf
      _ = (t^2 * exp (-(a/2) * t)) * exp (-(a/2) * t) := by ring
      _ ≤ 1 * exp (-(a/2) * t) := by
          apply mul_le_mul_of_nonneg_right (le_of_lt h1) (exp_pos _).le
      _ = exp (-(a / 2) * t) := one_mul _

end Integrability

end
