/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

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
  simpa [rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha

/-- t² * exp(-a*t) → 0 as t → ∞ for a > 0. -/
lemma tendsto_sq_mul_exp_neg_atTop (a : ℝ) (ha : 0 < a) :
    Tendsto (fun t => t^2 * exp (-a * t)) atTop (nhds 0) := by
  simpa [rpow_two] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 a ha

/-- exp(-a*t) → 0 as t → ∞ for a > 0. -/
lemma tendsto_exp_neg_atTop (a : ℝ) (ha : 0 < a) :
    Tendsto (fun t => exp (-a * t)) atTop (nhds 0) := by
  simpa [rpow_zero] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 a ha

/-- t * exp(-a*t) is integrable on [1,∞) for a > 0. -/
lemma integrableOn_mul_exp_neg_Ici (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t => t * exp (-a * t)) (Ici 1) volume := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (by norm_num) le_rfl ha
  simp only [rpow_one] at h
  exact h.mono_set (Set.Ioi_subset_Ioi zero_le_one)

/-- t² * exp(-a*t) is integrable on [1,∞) for a > 0. -/
lemma integrableOn_sq_mul_exp_neg_Ici (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t => t^2 * exp (-a * t)) (Ici 1) volume := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 2) (p := 1) (by norm_num) le_rfl ha
  simp only [rpow_one, rpow_two] at h
  exact h.mono_set (Set.Ioi_subset_Ioi zero_le_one)

end Integrability

end
