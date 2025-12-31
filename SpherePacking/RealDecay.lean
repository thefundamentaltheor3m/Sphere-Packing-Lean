/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Exponential

/-!
# Exponential Decay Integrability Lemmas

This file provides pure real analysis lemmas for integrability of exponentially
decaying functions, particularly for `exp(-c/t)` patterns near 0 and polynomial ×
exponential patterns at infinity.

These lemmas are designed to be reusable for contour integral analysis where:
- Near-0 regime (t→0): Super-exponential decay `exp(-c/t)` dominates any polynomial
- Tail regime (t→∞): For r > 2, exponential decay beats polynomial growth

## Main results

### Comparison lemmas
- `exp_neg_div_le_of_one_le`: exp(-c/t) ≤ exp(-c) for t ≥ 1
- `exp_neg_mul_div_le_exp_abs`: exp(-c*r/s) ≤ exp(c*|r|) for s ≥ 1

### Asymptotic behavior
- `exp_neg_div_tendsto_zero`: exp(-c/t) → 0 as t → 0⁺

## References

These patterns appear in the magic function integrability proofs for sphere packing.
See also `SpherePacking.MagicFunction.a.IntegralEstimates` for applications.
-/

open MeasureTheory Set Filter Real

noncomputable section

/-! ## Comparison Lemmas -/

section Comparison

/-- exp(-c/t) ≤ exp(-c) for 0 < t ≤ 1 and c > 0.
    When 0 < t ≤ 1, we have 1/t ≥ 1, so c/t ≥ c, so -c/t ≤ -c. -/
lemma exp_neg_div_le_of_le_one (c t : ℝ) (hc : 0 < c) (ht_pos : 0 < t) (ht : t ≤ 1) :
    exp (-c / t) ≤ exp (-c) := by
  apply exp_le_exp.mpr
  have h : c ≤ c / t := by
    rw [le_div_iff₀ ht_pos]
    calc c * t ≤ c * 1 := by nlinarith
      _ = c := mul_one c
  have : -c / t ≤ -c := by
    rw [neg_div]
    exact neg_le_neg h
  exact this

/-- For s ≥ 1, exp(-c*r/s) ≤ exp(c*|r|).
    This bounds a secondary exponential factor uniformly. -/
lemma exp_neg_mul_div_le_exp_abs (c r s : ℝ) (hc : 0 ≤ c) (hs : 1 ≤ s) :
    exp (-c * r / s) ≤ exp (c * |r|) := by
  apply exp_le_exp.mpr
  have h_pos : 0 < s := by linarith
  have h1 : -c * r / s ≤ |c * r| / s := by
    apply div_le_div_of_nonneg_right _ h_pos.le
    have : -c * r = -(c * r) := by ring
    rw [this]
    exact neg_le_abs (c * r)
  have h2 : |c * r| / s ≤ |c * r| := div_le_self (abs_nonneg _) hs
  have h3 : |c * r| = c * |r| := by rw [abs_mul, abs_of_nonneg hc]
  linarith

end Comparison

/-! ## Asymptotic Behavior -/

section Asymptotics

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
    exact h_inv.const_mul_atTop_of_neg (neg_neg_of_pos hc)
  exact tendsto_exp_atBot.comp h1

/-- exp(-c/t) is always positive. -/
lemma exp_neg_div_pos (c t : ℝ) : 0 < exp (-c / t) := exp_pos _

end Asymptotics

end

