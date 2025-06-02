import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


open UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

theorem exp_upperHalfPlane_lt_one (z : ℍ) :
    ‖(Complex.exp (2 * ↑π * Complex.I * z))‖ < 1 := by
  simp only [norm_exp, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
    Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, coe_re, coe_im,
    zero_sub, Real.exp_lt_one_iff, Left.neg_neg_iff]
  positivity

theorem exp_upperHalfPlane_lt_one_nat (z : ℍ) (n : ℕ) :
    ‖(Complex.exp (2 * ↑π * Complex.I * (n+1) * z))‖ < 1 := by
  simp [norm_exp, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
    Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, coe_re, coe_im,
    zero_sub, Real.exp_lt_one_iff, Left.neg_neg_iff]
  positivity

lemma exp_periodo (z : ℍ) (n : ℕ) :
  cexp (2 * ↑π * Complex.I * ↑↑n * (1 + ↑z)) = cexp (2 * ↑π * Complex.I * ↑↑n * ↑z) := by
  rw [mul_add]
  have :=  exp_periodic.nat_mul n
  rw [Periodic] at this
  have ht := this (2 * π * Complex.I * n * z)
  rw [← ht]
  congr 1
  ring
