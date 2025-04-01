/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Bhavik Mehta

M4R File
-/

import Mathlib

import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.MagicFunction.a.Basic
import SpherePacking.Tactic.NormNumI

/-! # Constructing Upper-Bounds for I₁

The purpose of this file is to construct bounds on the integral `I₁` that is part of the definition
of the function `a`. We follow the proof of Proposition 7.8 in the blueprint.
-/

open MagicFunction.a.Parametrisations MagicFunction.a.Real_Integrals
  MagicFunction.a.Radial_Functions
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter
open scoped Function

namespace MagicFunction.a.IntegralEstimates.I1

noncomputable section Change_of_Variables

variable (r : ℝ)

/-! We begin by performing changes of variables. -/
-- #check intervalIntegral.integral_comp_smul_deriv
-- #check MeasureTheory.integral_image_eq_integral_abs_deriv_smul

def f : ℝ → ℝ := fun t ↦ 1 / (2 * t)

def f' : ℝ → ℝ := fun t ↦ -1 / (2 * t ^ 2)

end Change_of_Variables

----------------------------------------------------------------

noncomputable section Computing_g

lemma z₁'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₁' t = -1 * (1 - t) + I * t := by
  rw [z₁', IccExtend_of_mem zero_le_one z₁ ht, z₁]

lemma z₁'_eq_of_mem' {t : ℝ} (ht : t ∈ Icc 0 1) : z₁' t = t * (I + 1) - 1 := by
  rw [z₁'_eq_of_mem ht]
  ring

lemma I₁'_eq (r : ℝ) : I₁' r =
    ∫ t in Ioo (0 : ℝ) 1, (1 + I) -- Added factor due to variable change!!
      * φ₀'' ((I - 1) * (1 / (2 * t)))
      * (t * (I + 1)) ^ 2
      * cexp (π * I * r ^ 2 * (t * (I + 1) - 1)) := by
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp
  rw [z₁'_eq_of_mem' (Ioo_subset_Icc_self ht), sub_add_cancel]
  congr! 4
  · have : t ≠ 0 := ht.1.ne'
    have h2 : (t : ℂ) ≠ 0 := by simp [this]
    field_simp [h2]
    linear_combination -t * I_sq
  · norm_cast
    simp

-- define g to be the rhs of this multiplied by the absolute value of the derivative of (f⁻¹)'
-- (except change all the f t to x)
lemma I₁'_eq' (r : ℝ) : I₁' r =
    ∫ t in Ioo (0 : ℝ) 1,
        (1 + I)
      * φ₀'' ((I - 1) * (f t))
      * ((I + 1) / (2 * f t)) ^ 2
      * cexp (π * I * r ^ 2 * ((I + 1) / (2 * f t) - 1)) := by
  have : ∀ x : ℂ, ∀ t ≠ 0, x / (2 * f t) = t * x := by
    intro x t ht
    rw [f]
    field_simp
    ring
  rw [I₁'_eq]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp
  congr 2
  · simp [f]
  · rw [this _ _ ht.1.ne']
  · congr 2
    rw [this _ _ ht.1.ne']

-- def I₁' (x : ℝ) := ∫ t in Ioo (0 : ℝ) 1, (1 + I) -- Added factor due to variable change!!
--   * φ₀'' (-1 / ((z₁' t) + (1 : ℂ)))
--   * ((z₁' t) + (1 : ℂ)) ^ 2
--   * cexp (π * I * |x| ^ 2 * (z₁' t))

-- lemma g_comp_f {r t : ℝ} :
--     g r (f t) = (I + 1) * φ₀'' ((I - 1) / (2 * t)) * sorry * cexp sorry := by
--   rw [f, g]
--   congr 1
--   · sorry
--   · sorry

-- private lemma calc_aux_3' (r : ℝ) : ∫ (t : ℝ) in Ioo 0 1, |f' t| • (g r (f t)) = I₁' r := by
--   rw [I₁']
--   apply setIntegral_congr_ae₀ nullMeasurableSet_Ioo
--   apply ae_of_all
--   intro x hx

end Computing_g

-- The above is courtesy Bhavik
----------------------------------------------------------------

noncomputable section Setting_Up_Change_of_Variables

def g : ℝ → ℝ → ℂ := fun r s ↦
  (I + 1)
  * φ₀'' ((I - 1) * s)
  * ((I + 1) / (2 * s)) ^ 2 *
    (1 / (2 * s ^ 2))
  * cexp (I * π * |r| ^ 2 *
    (-1 +
      (1 / (2 * s)) *
        (I + 1)))

lemma aux_measurable : MeasurableSet ((Ioo 0 1) : Set ℝ) := measurableSet_Ioo

#check hasDerivWithinAt_zpow
lemma aux_hasDeriv (x : ℝ) (hx : x ∈ Ioo 0 1) : HasDerivWithinAt f (f' x) (Ioo 0 1) x := by
  have hf : f = fun t ↦ (1 / 2) * t ^ (-1 : ℤ) := by
    ext x
    simp (disch := field_simp_discharge) only [Int.reduceNeg, zpow_neg, zpow_one, inv_eq_one_div,
      mul_div_assoc', mul_one, div_div]
    rfl
  have hf' : f' = fun t ↦ (1 / 2) * (-1 * t ^ (-2 : ℤ)) := by
    ext x
    simp (disch := field_simp_discharge) only [Int.reduceNeg, zpow_neg, inv_eq_one_div, neg_mul,
      one_mul, neg_div', mul_div_assoc', mul_neg, mul_one, div_div]
    rfl
  rw [hf, hf']
  apply HasDerivWithinAt.const_mul
  norm_cast
  exact hasDerivWithinAt_zpow (-1 : ℤ) x (Or.inl (ne_of_gt hx.1)) (Ioo 0 1)

lemma aux_injOn : InjOn f (Ioo 0 1) := by
  intro _ _ _ _ hf
  simp only [f, one_div, mul_inv_rev, mul_eq_mul_right_iff, inv_inj, inv_eq_zero,
    OfNat.ofNat_ne_zero, or_false] at hf
  exact hf

end Setting_Up_Change_of_Variables

----------------------------------------------------------------

noncomputable section Changing_Variables

lemma Changing_Domain_of_Integration (r : ℝ) :
    ∫ (s : ℝ) in Ioi ((1 / 2) : ℝ), (g r s) = ∫ (s : ℝ) in f '' (Ioo (0 : ℝ) (1 : ℝ)), (g r s) := by
  congr
  ext x
  constructor <;> intro hx
  · use 1 / (2 * x)
    simp only [mem_Ioi, mem_Ioo] at hx ⊢
    constructor
    · refine ⟨by positivity, ?_⟩
      rw [one_div, mul_inv_rev, inv_mul_lt_one₀ (by positivity), ← one_div]
      exact hx
    field_simp [f]
  · obtain ⟨y, hy₁, hy₂⟩ := hx
    rw [← hy₂, f]
    simp only [one_div, mul_inv_rev, mem_Ioi, inv_pos, Nat.ofNat_pos, lt_mul_iff_one_lt_left]
    exact one_lt_inv_iff₀.mpr hy₁

lemma Changing_Variables (r : ℝ) : ∫ (s : ℝ) in f '' (Ioo (0 : ℝ) (1 : ℝ)), (g r s) =
    ∫ (t : ℝ) in Ioo 0 1, |f' t| • (g r (f t)) :=
  integral_image_eq_integral_abs_deriv_smul aux_measurable aux_hasDeriv aux_injOn (g r)

end Changing_Variables

----------------------------------------------------------------

section Showing_Equality_to_I₁

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

#check Mathlib.Meta.NormNum.Result
-- open Lean Mathlib.Meta.NormNum Qq in
-- /-- Evaluates the `Int.lcm` function. -/
-- @[norm_num HAdd.hAdd _ _]
-- def Tactic.NormNum.evalComplexAdd : NormNumExt where eval {u α} e := do
--   let .app (.app _ (x : Q(ℂ))) (y : Q(ℂ)) ← Meta.whnfR e | failure
--   haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℂ := ⟨⟩
--   let i : Q(DivisionRing ℂ) := q(NormedDivisionRing.toDivisionRing)
--   let ⟨ex, p⟩ ← deriveRat x i
--   let ⟨ey, q⟩ ← deriveRat y i
--   -- let ⟨ed, pf⟩ := proveIntLCM ex ey
--   return (_ : Result e)

set_option push_neg.use_distrib true in
lemma _root_.Complex.ne_iff (a b : ℂ) : a ≠ b ↔ (a.re ≠ b.re ∨ a.im ≠ b.im) := by rw [ne_eq, Complex.ext_iff]; push_neg; rfl

example (z:ℂ) :z = ⟨z.re,z.im⟩ := by rw [Complex.eta]
example : 1 + I ≠ 0 := by rw [Complex.ne_iff]; norm_num

example : 1  = 3 * I ^ 2 + 4 := by
  refine Eq.trans ((Complex.eta _)).symm ?_
  refine Eq.trans ?_ (Complex.eta _)
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, pow_succ, pow_zero]
  simp only [one_re, one_im, zero_re, zero_im, Complex.re_ofNat, Complex.im_ofNat]
  norm_num1
  rfl

example : -2 = (I - 1) * (1 + I) := by
  refine Eq.trans ((Complex.eta _)).symm ?_
  refine Eq.trans ?_ (Complex.eta _)
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
    one_re, one_im, zero_re, zero_im, Complex.re_ofNat, Complex.im_ofNat]
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

lemma congr_aux_1 (x : ℝ) :
    -1 / (↑x - 1 + I * ↑x + 1) = (I - 1) / (2 * ↑x) := calc
  _ = -1 / (x + I * x) := by
    congr 1
    ring
  _ = (-1 * (1 - I)) / ((x + I * x) * (1 - I)) := by
    symm
    apply mul_div_mul_right
    intro hcontra
    rw [sub_eq_zero] at hcontra
    have : (ofReal 1).im = I.im := congrArg im hcontra
    simp at this
  _ = (I - 1) / (2 * x) := by
    congr 1
    · ring
    · ring_nf
      rw [I_sq]
      ring

-- Now, the main result of this section.

lemma I₁_Expression (r : ℝ) : ∫ (t : ℝ) in Ioo 0 1, |f' t| • (g r (f t)) = I₁' r := by
  rw [I₁'_eq']
  apply setIntegral_congr_ae₀ nullMeasurableSet_Ioo
  apply ae_of_all
  intro x hx
  -- field_simp [f, g, f']
  have habs : |-1 / (2 * x ^ 2)| = 1 / (2 * x ^ 2) := by
    suffices : -1 / (2 * x ^ 2) < 0
    · rw [abs_of_neg this]
      field_simp
    rw [neg_div]
    simp only [one_div, mul_inv_rev, Left.neg_neg_iff, inv_pos, Nat.ofNat_pos,
      mul_pos_iff_of_pos_right]
    exact pow_pos hx.1 2
  simp only [f', g, f, habs, real_smul]
  have hrearrange_LHS : -- Break product of 2 things into product of 4 things
    ofReal (1 / (2 * x ^ 2))
    * ((I + 1)
    * φ₀'' ((I - 1) * ↑(1 / (2 * x)))
    * ((I + 1) / (2 * ↑(1 / (2 * x)))) ^ 2 * (1 / (2 * ↑(1 / (2 * x)) ^ 2))
    * cexp (I * ↑π * ↑|r| ^ 2 * (-1 + 1 / (2 * ↑(1 / (2 * x))) * (I + 1))))
      = (I + 1)
      * φ₀'' ((I - 1) * ↑(1 / (2 * x)))
      * (ofReal (1 / (2 * x ^ 2)) * ((I + 1) / (2 * ↑(1 / (2 * x)))) ^ 2 * (1 / (2 * ↑(1 / (2 * x)) ^ 2)))
      * cexp (I * ↑π * ↑|r| ^ 2 * (-1 + 1 / (2 * ↑(1 / (2 * x))) * (I + 1)))
    := by ring
  rw [hrearrange_LHS]
  congr 2
  · congr 1
    ring
  · field_simp
    ring_nf
    congr 2 <;> field_simp [hx.1.ne'] <;> ring
  · rw [mul_comm I π]
    norm_cast
    rw [_root_.sq_abs r]
    congr
    field_simp
    ring

end Showing_Equality_to_I₁

----------------------------------------------------------------

section Bounding

-- Now that we have `MagicFunction.a.IntegralEstimates.I1.I₁_Expression`, we can bound `I₁`.

-- #check I₁_Expression



end Bounding
