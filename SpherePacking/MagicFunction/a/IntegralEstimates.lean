/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

import Mathlib

import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.MagicFunction.a.Basic

/-! # Constructing Upper-Bounds for I₁, I₂, I₃ and I₄

The purpose of this file is to construct bounds on the integrals `I₁`, `I₂`, `I₃` and `I₄` that
make up the function `a`. We follow the proof of Proposition 7.8 in the blueprint.
-/

open MagicFunction Complex Real Set MeasureTheory MeasureTheory.Measure Filter
open scoped Function

-- namespace MagicFunction

noncomputable section I₁

variable (r : ℝ)

/-! We begin by performing changes of variables. -/
-- #check intervalIntegral.integral_comp_smul_deriv
#check MeasureTheory.integral_image_eq_integral_abs_deriv_smul

/- 1. (z + 1) ↦ -1 / (z + 1) -/
private def f : ℝ → ℝ := fun t ↦ 1 / (2 * t)

private def f' : ℝ → ℝ := fun t ↦ -1 / (2 * t ^ 2)

private def g : ℝ → ℝ → ℂ := fun r s ↦ (I + 1)
    * φ₀'' ((I - 1) * s)
      * ((I + 1) / (2 * s)) ^ 2 * (1 / (2 * s ^ 2))
        * cexp (I * π * r ^ 2 * (-1 + (1 / (2 * s)) * (I + 1)))

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
    have h3 : I + 1 ≠ 0 := by
      intro h
      simpa using congr(($h).re)
    field_simp [h2, h3]
    ring_nf
    simp
    ring
  · norm_cast
    simp

-- define g to be the rhs of this divided by |f' x|
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


-- sure (but re-parametrise later into rectangular...)

private lemma aux_measurable : MeasurableSet ((Ioo 0 1) : Set ℝ) := measurableSet_Ioo

private lemma aux_hasDeriv (x : ℝ) (hx : x ∈ Ioo 0 1) : HasDerivWithinAt f (f' x) (Ioo 0 1) x := by
  sorry

private lemma aux_injOn : InjOn f (Ioo 0 1) := by
  intro _ _ _ _ hf
  simp only [f, one_div, mul_inv_rev, mul_eq_mul_right_iff, inv_inj, inv_eq_zero,
    OfNat.ofNat_ne_zero, or_false] at hf
  exact hf

private lemma calc_aux_1 (r : ℝ) :
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

private lemma calc_aux_2 (r : ℝ) : ∫ (s : ℝ) in f '' (Ioo (0 : ℝ) (1 : ℝ)), (g r s) =
    ∫ (t : ℝ) in Ioo 0 1, |f' t| • (g r (f t)) :=
  integral_image_eq_integral_abs_deriv_smul aux_measurable aux_hasDeriv aux_injOn (g r)

-- Before we can prove the main result, we prove some auxiliary results.

private lemma congr_aux_1 (x : ℝ) :
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

-- private lemma congr_aux_2 (x : ℝ) :
--     I * ↑x ^ 4 * (↑x)⁻¹ ^ 2 * 16 + I ^ 2 * ↑x ^ 4 * (↑x)⁻¹ ^ 2 * 8 + ↑x ^ 4 * (↑x)⁻¹ ^ 2 * 8 =
--     I * ↑x ^ 2 * 32 + I ^ 2 * ↑x ^ 2 * 16 + ↑x ^ 2 * 16 := by
--   field_simp
--   sorry

-- Now, the main result of this section.

private lemma calc_aux_3 (r : ℝ) : ∫ (t : ℝ) in Ioo 0 1, |f' t| • (g r (f t)) = I₁' r := by
  rw [I₁']
  apply setIntegral_congr_ae₀ nullMeasurableSet_Ioo
  apply ae_of_all
  intro x hx
  -- field_simp [f, g, f']
  simp (disch := field_simp_discharge) only [f', g, f, ofReal_div, ofReal_one, ofReal_mul,
    ofReal_ofNat, mul_div_assoc', mul_one, div_div_eq_mul_div, div_pow, neg_mul, one_mul,
    div_mul_eq_mul_div, div_div, mul_div_cancel_left₀, real_smul, div_eq_iff]
  have hz₁ : z₁' x = z₁ ⟨x, (mem_Icc_of_Ioo hx)⟩ :=
    IccExtend_of_mem z₁'.proof_1 z₁ (mem_Icc_of_Ioo hx)
  simp only [hz₁, z₁]
  have habs : |-1 / (2 * x ^ 2)| = 1 / (2 * x ^ 2) := by
    suffices : -1 / (2 * x ^ 2) < 0
    · rw [abs_of_neg this]
      field_simp
    rw [neg_div]
    simp only [one_div, mul_inv_rev, Left.neg_neg_iff, inv_pos, Nat.ofNat_pos,
      mul_pos_iff_of_pos_right]
    exact pow_pos hx.1 2
  rw [habs]
  have hrearrange_LHS : -- Break product of 2 things into product of 4 things
      ofReal (1 / (2 * x ^ 2))
        * ((I + 1)
          * φ₀'' ((I - 1) / (2 * ↑x))
            * ((I + 1) * (2 * ↑x)) ^ 2
              * -(2 * ↑x) ^ 2
                * cexp (I * ↑π * ↑r ^ 2 * (-1 + ↑x * (I + 1))))
      = (I + 1)
      * (φ₀'' ((I - 1) / (2 * ↑x)))
      * (((I + 1) * (2 * ↑x)) ^ 2 * (-(2 * ↑x)) ^ 2 * ofReal (1 / (2 * x ^ 2)))
      * cexp (I * ↑π * ↑r ^ 2 * (-1 + ↑x * (I + 1)))
    := by sorry
  have hrearrange_RHS : -- Break product of 5 things into product of 4 things
      (1 + I)
      * φ₀'' (-1 / (-1 * (1 - ↑x) + I * ↑x + 1))
      * (-1 * (1 - ↑x) + I * ↑x + 1) ^ 2
      * cexp (↑π * I * ↑|r| ^ 2 * (-1 * (1 - ↑x) + I * ↑x))
      * (2 ^ 2 * 2 ^ 2)
      = (1 + I)
      * φ₀'' (-1 / (-1 * (1 - ↑x) + I * ↑x + 1))
      * ((-1 * (1 - ↑x) + I * ↑x + 1) ^ 2 * 16)
      * cexp (↑π * I * ↑|r| ^ 2 * (-1 * (1 - ↑x) + I * ↑x))
    := by ring
  stop
  rw [hrearrange_LHS, hrearrange_RHS]
  congr 1
  · congr 1 <;> field_simp
    · left
      congr 1
      symm
      sorry
    · ring_nf
      -- WHOOPSIE. This is WRONG! Something from an earlier step?
      -- field_simp
      sorry
  · ring_nf
    -- I suspect this is wrong too, and that this combined with the previous step is what is right.
    sorry
  -- [TODO] Create congr lemmas for the above goals

end I₁
