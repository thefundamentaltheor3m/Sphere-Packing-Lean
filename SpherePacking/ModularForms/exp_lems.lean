import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


open UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

theorem exp_upperHalfPlane_lt_one (z : ℍ) :
    Complex.abs (Complex.exp (2 * ↑π * Complex.I * z)) < 1 := by
  simp only [abs_exp, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
    Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, coe_re, coe_im,
    zero_sub, Real.exp_lt_one_iff, Left.neg_neg_iff]
  positivity

theorem exp_upperHalfPlane_lt_one_nat (z : ℍ) (n : ℕ) :
    Complex.abs (Complex.exp (2 * ↑π * Complex.I * (n+1) * z)) < 1 := by
  simp [abs_exp, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
    Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, coe_re, coe_im,
    zero_sub, Real.exp_lt_one_iff, Left.neg_neg_iff]
  positivity
