module
public import SpherePacking.ModularForms.SummableLemmas.Cotangent

/-!
# Rewriting `ℤ` sums in terms of `ℕ+`

This file provides a rearrangement lemma that rewrites a `ℤ`-indexed sum as a `ℕ+`-indexed sum,
specialized to the expressions appearing in cotangent and Eisenstein series computations.

## Main statements
* `sum_int_pnat2_pnat`
-/

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open ArithmeticFunction

lemma summable_pnats (f : ℕ → ℂ) : Summable (fun n : ℕ+ => f n) ↔ Summable f := by
  simpa using (nat_pos_tsum2' (f := f)).trans (summable_nat_add_iff (f := f) 1)

private lemma diff_right_congr (z : ℍ) (d : ℕ+) (b : ℕ+) :
    ((z : ℂ))⁻¹ *
        (1 / (-(d : ℂ) / ↑z - ↑↑b) + 1 / (-↑d / ↑z + ↑↑b)) =
      1 / ((b : ℂ) * ↑z - ↑↑d) - 1 / (↑↑b * ↑z + ↑↑d) := by
  have hz := ne_zero z
  grind

theorem summable_diff_right_a (z : ℍ) (d : ℕ+) :
  Summable fun n : ℕ ↦ 1 / ((n : ℂ) * ↑z - ↑↑d) - 1 / (↑↑n * ↑z + ↑↑d) := by
  rw [← summable_pnats]
  exact ((summable_diff z d).mul_left ((z : ℂ))⁻¹).congr (diff_right_congr z d)

theorem summable_diff_right (z : ℍ) (d : ℕ+) :
  Summable fun m : ℤ ↦ 1 / ((m : ℂ) * ↑z - ↑↑d) - 1 / (↑m * ↑z + ↑↑d) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · apply summable_diff_right_a
  · rw [← summable_pnats]
    have h := (summable_diff z d).mul_left ((z : ℂ))⁻¹
    refine h.congr ?_
    intro b
    have hz := ne_zero z
    simp at *
    grind

lemma sum_int_pnatt (z : ℍ) (d : ℕ+) :
  2/ d + ∑' (m : ℤ), (1 / ((m : ℂ) * ↑z - d) - 1 / (↑m * ↑z + d)) = ∑' m : ℕ+,
    ((1 / ((m : ℂ) * ↑z - d) + 1 / (-↑m * ↑z + -d)) - (1 / ((m : ℂ) * ↑z + d)) - 1 / (-↑m * ↑z + d))
      := by
  have hs := summable_diff_right z d
  rw [int_tsum_pNat _ hs]
  simp only [Int.cast_zero, zero_mul, zero_sub, one_div, zero_add, Int.cast_natCast, Int.cast_neg,
    neg_mul]
  ring_nf
  rw [← Summable.tsum_add]
  · congr
    funext m
    ring
  · have H := (summable_int_iff_summable_nat_and_neg.mp hs).1
    have v : Summable fun (n : ℕ) ↦ (-↑(d : ℂ) + (n : ℂ) * ↑z)⁻¹ - (↑↑d + (n : ℂ)* ↑z)⁻¹ := by
      apply H.congr
      intro b
      simp [one_div]
      ring_nf
    apply v.subtype
  · have H := (summable_int_iff_summable_nat_and_neg.mp hs).2
    have v : Summable fun (n : ℕ) ↦ ( - ↑(d : ℂ)- z * ((n : ℂ)))⁻¹ - (↑↑d - z * ((n : ℂ)))⁻¹ := by
      apply H.congr
      intro b
      simp [one_div, sub_eq_add_neg, add_comm, mul_comm]
    apply v.subtype

/-- Rewrite the `ℤ` sum `∑ (1/(m z - d) - 1/(m z + d))` as a `ℕ+` sum of symmetric differences. -/
public lemma sum_int_pnat2_pnat (z : ℍ) (d : ℕ+) :
  ∑' (m : ℤ), (1 / ((m : ℂ) * ↑z - d) - 1 / (↑m * ↑z + d)) = -2/d + ∑' m : ℕ+,
    ((1 / ((m : ℂ) * ↑z - d) + 1 / (-↑m * ↑z + -d)) - (1 / ((m : ℂ) * ↑z + d)) - 1 / (-↑m * ↑z + d))
      := by
  rw [← sum_int_pnatt]
  ring
