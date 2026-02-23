module
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable


/-!
# Big O

This file proves results such as `linear_bigO`, `linear_bigO_pow`, `linear_bigO_nat`.
-/

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open EisensteinSeries UpperHalfPlane TopologicalSpace Set Metric Filter Function Complex

/-- A cofinite `BigO` estimate for `n ↦ (m * z + n)⁻¹` on the integer variable `n`. -/
public lemma linear_bigO (m : ℤ) (z : ℍ) : (fun (n : ℤ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    fun n => (|(n : ℝ)|⁻¹) := by
  simpa [abs_inv] using
    (EisensteinSeries.linear_inv_isBigO_right (c := m) (z := (z : ℂ))).norm_right

/-- A cofinite `BigO` estimate for powers of `n ↦ (m * z + n)⁻¹`. -/
public lemma linear_bigO_pow (m : ℤ) (z : ℍ) (k : ℕ) :
    (fun (n : ℤ) => ((((m : ℂ) * z + n)) ^ k )⁻¹) =O[cofinite]
    fun n => ((|(n : ℝ)| ^ k)⁻¹) := by
  simpa [inv_pow] using (Asymptotics.IsBigO.pow (linear_bigO m z) k)

/-- A cofinite `BigO` estimate for `n ↦ (m * z + n)⁻¹` on the natural variable `n`. -/
public lemma linear_bigO_nat (m : ℤ) (z : ℍ) :
    (fun (n : ℕ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite] fun n => (|(n : ℝ)|⁻¹) := by
  refine
    ((linear_bigO m z).comp_tendsto Nat.cast_injective.tendsto_cofinite).congr' ?_ ?_
  all_goals exact Filter.Eventually.of_forall fun n => by simp [Function.comp]

/-- A cofinite `BigO` estimate for `n ↦ (n * z + m)⁻¹` (integer variable on the left). -/
public lemma linear_bigO' (m : ℤ) (z : ℍ) : (fun (n : ℤ) => ((n : ℂ) * z + m)⁻¹) =O[cofinite]
    fun n => (|(n : ℝ)|⁻¹) := by
  simpa [Real.norm_eq_abs, abs_inv] using
    (linear_inv_isBigO_left (d := m) (z := (z : ℂ)) (ne_zero z)).norm_right
