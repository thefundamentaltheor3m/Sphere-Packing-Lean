module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Helpers for `intervalIntegral`

This file contains small reusable rewrite/substitution lemmas for interval integrals that occur in
multiple special-value computations across dimensions.
-/

namespace SpherePacking.ForMathlib

open scoped Interval
open MeasureTheory intervalIntegral

/-- Change of variables `t ↦ 1 - t` for `∫_0^1`, giving `∫ f (1 - t) = ∫ f t`. -/
public lemma intervalIntegral_comp_one_sub_eq {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β]
    [CompleteSpace β] (f : ℝ → β) :
    (∫ t : ℝ in (0 : ℝ)..1, f (1 - t)) = ∫ t : ℝ in (0 : ℝ)..1, f t := by
  simp

/-- A variant of `intervalIntegral_comp_one_sub_eq` with a prefactor `(-1 : ℂ)`. -/
public lemma intervalIntegral_neg_one_mul_comp_one_sub_eq_neg (f : ℝ → ℂ) :
    (∫ t : ℝ in (0 : ℝ)..1, (-1 : ℂ) * f (1 - t)) = -∫ t : ℝ in (0 : ℝ)..1, f t := by
  rw [neg_eq_neg_one_mul]
  simp [intervalIntegral_comp_one_sub_eq (f := f)]

end SpherePacking.ForMathlib
