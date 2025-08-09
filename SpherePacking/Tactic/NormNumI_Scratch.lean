import Mathlib.Analysis.CStarAlgebra.Classes

open Complex

-- [TODO] move all this metaprogramming stuff elsewhere!!
-- example (a b c:ℂ) : a / (b * c) = (a/b) * c⁻¹ := by rw [@div_mul_eq_div_div]; exact?
-- Before we can prove the main result, we prove some auxiliary results.
lemma congr_aux_1' (x : ℝ) :
    -1 / (↑x - 1 + I * ↑x + 1) = (I - 1) / (2 * ↑x) := by
  trans - 1 / ((1 + I) * x)
  · congr 1
    ring
  obtain rfl | hx := eq_or_ne x 0
  · simp
  have : (x:ℂ) ≠ 0 := mod_cast hx
  have : 1 + I ≠ 0 := sorry -- ought to be by done by a norm_num extension
  field_simp
  linear_combination - x * I_sq

-- #check Mathlib.Meta.NormNum.Result
-- open Lean Mathlib.Meta.NormNum Qq in
-- /-- Evaluates the `Int.lcm` function. -/
-- @[norm_num HAdd.hAdd _ _]
-- def Tactic.NormNum.evalComplexAdd : NormNumExt where eval {u α} e := do
-- let .app (.app _ (x : Q(ℂ))) (y : Q(ℂ)) ← Meta.whnfR e | failure
-- haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℂ := ⟨⟩
-- let i : Q(DivisionRing ℂ) := q(NormedDivisionRing.toDivisionRing)
-- let ⟨ex, p⟩ ← deriveRat x i
-- let ⟨ey, q⟩ ← deriveRat y i
-- -- let ⟨ed, pf⟩ := proveIntLCM ex ey
-- return (_ : Result e)

set_option push_neg.use_distrib true in
lemma _root_.Complex.ne_iff (a b : ℂ) : a ≠ b ↔ (a.re ≠ b.re ∨ a.im ≠ b.im) := by
  rw [ne_eq, Complex.ext_iff]; push_neg; rfl

example (z : ℂ) :z = ⟨z.re,z.im⟩ := by rw [Complex.eta]
example : 1 + I ≠ 0 := by rw [Complex.ne_iff]; norm_num

example : 1 = 3 * I ^ 2 + 4 := by
  refine Eq.trans ((Complex.eta _)).symm ?_
  refine Eq.trans ?_ (Complex.eta _)
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.I_re,
    Complex.I_im, pow_succ, pow_zero]
  simp only [one_re, one_im, Complex.re_ofNat, Complex.im_ofNat]
  norm_num1
  rfl

example : -2 = (I - 1) * (1 + I) := by
  refine Eq.trans ((Complex.eta _)).symm ?_
  refine Eq.trans ?_ (Complex.eta _)
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
    one_re, one_im, Complex.re_ofNat, Complex.im_ofNat]
  norm_num1
  rfl

lemma congr_aux_1'' (x : ℝ) :
    -1 / (↑x - 1 + I * ↑x + 1) = (I - 1) / (2 * ↑x) := by
  trans - 1 / ((1 + I) * x)
  · congr 1
    ring
  obtain rfl | hx := eq_or_ne x 0
  · simp
  rw [div_mul_eq_div_div]
  rw [div_mul_eq_div_div]
  congr! 1
  conv_lhs => norm_num1
  have : 1 + I ≠ 0 := sorry -- ought to be by done by a norm_num extension
  field_simp
  linear_combination - I_sq
