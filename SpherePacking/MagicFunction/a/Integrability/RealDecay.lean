/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
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

/-!
# Exponential Decay Integrability Lemmas (Tail Regime)

This file provides pure real analysis lemmas for integrability of exponentially
decaying functions in the tail regime (t → ∞), particularly polynomial × exponential
patterns.

These lemmas are designed to be reusable for contour integral analysis where:
- For r > 2, exponential decay beats polynomial growth in vertical ray integrands

## Main results

### Asymptotic behavior
- `tendsto_const_mul_rpow_mul_exp_neg_atTop`: C · t^n · exp(-a·t) → 0 as t → ∞ for a > 0

### Integrability
- `integrableOn_exp_mul_Ici`: exp(c*t) is integrable on [1,∞) for c < 0
- `integrableOn_mul_exp_neg_Ici`: t * exp(-a*t) is integrable on [1,∞) for a > 0
- `integrableOn_sq_mul_exp_neg_Ici`: t² * exp(-a*t) is integrable on [1,∞) for a > 0

## References

These patterns appear in the magic function integrability proofs for sphere packing,
specifically for vertical ray integrands in ContourEndpoints.lean.
-/

@[expose] public section

open MeasureTheory Set Filter Real

noncomputable section

/-! ## Integrability Lemmas -/

section Integrability

/-- exp(c*t) is integrable on [1,∞) for c < 0. -/
lemma integrableOn_exp_mul_Ici (c : ℝ) (hc : c < 0) :
    IntegrableOn (fun t ↦ exp (c * t)) (Ici 1) volume :=
  (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_exp_mul_Ioi hc 1)

/-- `C · t^n · exp(-a·t) → 0` as `t → ∞` for `a > 0` and any real power `n`. -/
lemma tendsto_const_mul_rpow_mul_exp_neg_atTop (C a n : ℝ) (ha : 0 < a) :
    Tendsto (fun t ↦ C * t ^ n * exp (-a * t)) atTop (nhds 0) := by
  simpa [mul_assoc] using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero n a ha).const_mul C

/-- t * exp(-a*t) is integrable on [1,∞) for a > 0. -/
lemma integrableOn_mul_exp_neg_Ici (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t ↦ t * exp (-a * t)) (Ici 1) volume := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simpa [rpow_one] using (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1)
    (by norm_num) le_rfl ha).mono_set (Set.Ioi_subset_Ioi zero_le_one)

/-- t² * exp(-a*t) is integrable on [1,∞) for a > 0. -/
lemma integrableOn_sq_mul_exp_neg_Ici (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t ↦ t^2 * exp (-a * t)) (Ici 1) volume := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simpa [rpow_one, rpow_two] using (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 2) (p := 1)
    (by norm_num) le_rfl ha).mono_set (Set.Ioi_subset_Ioi zero_le_one)

end Integrability

/-! ## Comparison Lemmas (Cusp Regime) -/

section NearZero

/-- `exp (-c/t) * t⁻² ≤ exp (-c)` for `t ∈ (0, 1]` and `c ≥ 2`: the super-exponential decay
as `t → 0⁺` dominates the quadratic pole. Proved by substituting `u = 1/t ≥ 1` and using
`log u ≤ u - 1`. -/
lemma exp_neg_div_mul_inv_sq_le (c t : ℝ) (hc : 2 ≤ c) (ht_pos : 0 < t) (ht : t ≤ 1) :
    exp (-c / t) * t⁻¹ ^ 2 ≤ exp (-c) := by
  have h_u_ge_1 : 1 ≤ t⁻¹ := one_le_inv_iff₀.mpr ⟨ht_pos, ht⟩
  set u := t⁻¹ with hu_def
  have h_u_pos : 0 < u := by positivity
  have h_eq : exp (-c / t) * t⁻¹ ^ 2 = exp (-c * u) * u ^ 2 := by
    simp only [hu_def, div_eq_mul_inv]
  rw [h_eq]
  have h_ineq : u ^ 2 ≤ exp (c * (u - 1)) := by
    rcases eq_or_lt_of_le h_u_ge_1 with h | h
    · simp [← h]
    · have hlog : log u ≤ u - 1 := log_le_sub_one_of_pos h_u_pos
      have h7 : 2 * log u ≤ c * (u - 1) := by nlinarith
      calc u ^ 2 = exp (log (u ^ 2)) := by rw [exp_log]; positivity
        _ = exp (2 * log u) := by rw [log_pow]; ring_nf
        _ ≤ exp (c * (u - 1)) := exp_le_exp.mpr h7
  have h_split : exp (-c * u) = exp (-c) * exp (-c * (u - 1)) := by rw [← exp_add]; ring_nf
  rw [h_split, mul_assoc]
  refine mul_le_of_le_one_right (exp_pos _).le ?_
  rw [neg_mul, exp_neg, inv_mul_le_one₀ (exp_pos _)]
  exact h_ineq

end NearZero

end
