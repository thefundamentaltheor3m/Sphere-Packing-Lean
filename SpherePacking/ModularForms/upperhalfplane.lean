import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Data.Real.StarOrdered

open  UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical


lemma pnat_div_upper (n : ℕ+) (z : ℍ) : 0 < (-(n : ℂ) / z).im := by
  norm_cast
  rw [div_im]
  simp only [Int.cast_neg, Int.cast_natCast, neg_im, natCast_im, neg_zero, coe_re, zero_mul,
    zero_div, neg_re, natCast_re, coe_im, neg_mul, zero_sub, Left.neg_pos_iff, gt_iff_lt]
  rw [@div_neg_iff]
  right
  simp only [Left.neg_neg_iff, Nat.cast_pos, PNat.pos, mul_pos_iff_of_pos_left, Complex.normSq_pos,
    ne_eq]
  refine ⟨z.2, ne_zero z⟩

lemma pos_nat_div_upper (n : ℤ) (hn : 0 < n) (z : ℍ) : 0 < (-(n : ℂ) / z).im := by
  norm_cast
  rw [div_im]
  simp [Int.cast_neg, Int.cast_natCast, neg_im, natCast_im, neg_zero, coe_re, zero_mul,
    zero_div, neg_re, natCast_re, coe_im, neg_mul, zero_sub, Left.neg_pos_iff, gt_iff_lt]
  rw [div_neg_iff]
  right
  simp [Left.neg_neg_iff, Nat.cast_pos, PNat.pos, mul_pos_iff_of_pos_left, Complex.normSq_pos,
    ne_eq]
  have hnr : 0 < (n : ℝ) := by simp [hn]
  refine ⟨by apply mul_pos hnr z.2; , ne_zero z⟩
