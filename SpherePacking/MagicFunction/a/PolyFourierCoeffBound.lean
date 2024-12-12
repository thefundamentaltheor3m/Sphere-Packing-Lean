/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

import SpherePacking.ModularForms.Eisenstein
import SpherePacking.ForMathlib.tprod
import Mathlib

open Filter Complex Real BigOperators Asymptotics

private noncomputable def fouterm (coeff : ℤ → ℂ) (x : ℂ) (i : ℤ) : ℂ :=
  (coeff i) * cexp (π * I * i * x)

variable (z : ℂ) (hz : 1 / 2 < z.im)
variable (c : ℤ → ℂ) (n₀ : ℤ) (hn₀ : ∀ (n : ℤ), n < n₀ → c n = 0)
variable (hcsum : Summable (fouterm c z))
variable (k : ℕ) (hpoly : c =O[atTop] fun n => n ^ k)
variable (f : ℂ → ℂ) (hf : ∀ x : ℂ, f x = ∑' (n : ℤ), (fouterm c x n))

-- private noncomputable def f (x : ℂ) : ℂ := ∑' (n : ℤ), (fouterm c x n)

-- local notation "f" => fun (x : ℂ) => ∑' (n : ℤ), (fouterm c x n)
-- #check f z

noncomputable def BoundConstntOfPolyFourierCoeff : ℝ :=
  (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) / 2)) /
  (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24)

#check BoundConstntOfPolyFourierCoeff

section calc_aux

-- These could even go in Mathlib... they look useful (if a bit random)

private lemma aux_1 (x : ℂ) : abs (cexp (I * x)) = rexp (-x.im) := by
  have h₁ : I * (↑x.im * I) = -x.im := by rw [mul_comm, mul_assoc, Complex.I_mul_I, mul_neg_one]
  rw [← x.re_add_im, mul_add, h₁, Complex.abs_exp]
  simp

-- Below was written by Bhavik
private lemma aux_2 (x : ℂ) : 1 - Real.exp x.re ≤ Complex.abs (1 - cexp x) := calc
  abs (1 - cexp x) ≥ |Complex.abs 1 - abs (cexp x)| := abs.abs_abv_sub_le_abv_sub _ _
  _ = |1 - rexp x.re| := by simp [Complex.abs_exp]
  _ ≥ _ := le_abs_self _

include hcsum in
private lemma aux_3 : Summable fun i ↦ ‖c i * cexp (↑π * I * (↑i - ↑n₀) * z)‖ := by
  rw [summable_norm_iff]
  simp only [mul_sub, sub_mul, Complex.exp_sub, div_eq_mul_inv, ← mul_assoc]
  apply Summable.mul_right (cexp (↑π * I * ↑n₀ * z))⁻¹
  exact hcsum

include hcsum in
private lemma aux_4 : Summable fun i ↦ Complex.abs (c i) *
    Complex.abs (cexp (↑π * I * (↑i - ↑n₀) * z)) := by
  simp_rw [← map_mul, ← Complex.norm_eq_abs]; exact aux_3 z c n₀ hcsum

lemma aux_5 : Complex.abs (∏' (n : ℕ+), (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24) =
  ∏' (n : ℕ+), Complex.abs (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24 := by
  simp only [← abs_pow]
  apply Complex.abs_tprod -- ℕ+ (fun n => (1 - cexp (2 * ↑π * I * n * z)) ^ 24)
  sorry


lemma aux_6 : 0 ≤ ∏' (n : ℕ+), Complex.abs (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24 := by
  rw [← aux_5 z]
  exact AbsoluteValue.nonneg Complex.abs (∏' (n : ℕ+), (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24)

lemma aux_7 (a b : ℤ) :
    Complex.abs (cexp (↑π * I * (a - b) * z)) ≤ rexp (-π * (a - b) * z.im) := by
  rw [mul_comm (π : ℂ) I, mul_assoc, mul_assoc, aux_1 (↑π * ((a - b) * z))]
  refine exp_le_exp.2 ?_
  simp; linarith

lemma aux_8 : 0 < ∏' (n : ℕ+), (1 - rexp (2 * π * ↑↑n * z.im)) ^ 24 := by
  -- suffices hsuff₁ : 0 < ∏' (n : ℕ+), Complex.abs (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24
  -- · refine gt_of_ge_of_gt ?_ hsuff₁
  --   rw [ge_iff_le]
  --   apply?
  --   sorry
  -- refine LE.le.lt_of_ne (aux_6 z) ?_
  -- rw [← aux_5 z]
  -- intro hcontra
  -- symm at hcontra
  -- rw [← Complex.norm_eq_abs, norm_eq_zero] at hcontra
  sorry

lemma aux_ring (i : ℤ) : (I * ↑π * (↑i - ↑n₀) * z) = I * ((↑π * (↑i - ↑n₀)) * z) := by ring

lemma aux_9 (i : ℤ) :
    ‖c i * cexp (↑π * I * (↑i - ↑n₀) * z)‖ = ‖c i‖ * rexp (-π * (↑i - ↑n₀) * z.im) := by
  rw [Complex.norm_eq_abs, Complex.norm_eq_abs, map_mul, mul_comm (↑π) (I)]
  rw [aux_ring, aux_1]
  congr; simp

include hcsum in
lemma aux_10 : Summable fun n ↦ Complex.abs (c n) * rexp (-π * (↑n - ↑n₀) * z.im) := by
  simp only [← Complex.norm_eq_abs, ← aux_9, aux_ring]
  exact aux_3 z c n₀ hcsum

lemma aux_11 : 0 < ∏' (n : ℕ+), (1 - rexp (-π * ↑↑n)) ^ 24 := by
  sorry

lemma aux_misc (x : UpperHalfPlane) : abs (cexp (I * x)) ≤ rexp (x.im) := by
  rw [aux_1 x]
  refine exp_le_exp.2 ?_
  rw [UpperHalfPlane.coe_im, neg_le_self_iff]
  exact le_of_lt x.2

end calc_aux

section calc_steps

-- include z hz c n₀ hn₀ hcsum k hpoly

include hf in
private lemma step_1 :
    abs ((f z) / (Δ ⟨z, by linarith⟩)) = abs (
      (∑' (n : ℤ), c n * cexp (π * I * n * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)
    ) := by simp_rw [DiscriminantProductFormula, hf, fouterm, UpperHalfPlane.coe]

private lemma step_2 :
    abs ((∑' (n : ℤ), c n * cexp (π * I * n * z)) /
    (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) =
    abs ((cexp (π * I * n₀ * z) * ∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
    (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by
  apply congr_arg Complex.abs
  apply congr_arg (fun x => x /
    (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24))
  rw [← tsum_mul_left]
  apply congr_arg; ext n; ring_nf
  rw [mul_assoc (c n) (cexp _), ← Complex.exp_add]
  congr
  ring

private lemma step_3 :
    abs ((cexp (π * I * n₀ * z) * ∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
    (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) =
    abs ((cexp (π * I * n₀ * z) / cexp (2 * π * I * z)) *
    (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
    (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by field_simp

private lemma step_4 :
    abs ((cexp (π * I * n₀ * z) / cexp (2 * π * I * z)) *
    (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
    (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) =
    abs ((cexp (π * I * (n₀ - 2) * z)) *
    (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
    (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by
  rw [mul_sub, sub_mul, ← Complex.exp_sub]
  congr 6
  ac_rfl

private lemma step_5 :
    abs ((cexp (π * I * (n₀ - 2) * z)) *
    (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
    (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) =
    abs (cexp (π * I * (n₀ - 2) * z)) *
    abs (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
    Complex.abs (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  simp only [map_div₀, map_mul]

private lemma step_6 :
    abs (cexp (π * I * (n₀ - 2) * z)) *
    abs (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
    Complex.abs (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24) =
    abs (cexp (π * I * (n₀ - 2) * z)) *
    abs (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
    ∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24 := by congr; exact aux_5 z

private lemma step_7 :
    abs (cexp (π * I * (n₀ - 2) * z)) * abs (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
    ∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24 ≤
    rexp (-π * (n₀ - 2) * z.im) * abs (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
    (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · exact aux_6 z
  · exact aux_7 z n₀ 2

include hcsum in
private lemma step_8 :
    rexp (-π * (n₀ - 2) * z.im) * abs (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
    (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * abs (cexp (π * I * (n - n₀) * z))) /
    (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · exact aux_6 z
  · calc
    _ ≤ ∑' (n : ℤ), Complex.abs ((c n) * (cexp (↑π * I * (↑n - ↑n₀) * z))) := by
      simp_rw [← Complex.norm_eq_abs]
      refine norm_tsum_le_tsum_norm ?_
      exact aux_3 z c n₀ hcsum
    _ = ∑' (n : ℤ), Complex.abs (c n) * Complex.abs (cexp (↑π * I * (↑n - ↑n₀) * z)) :=
      by simp only [map_mul]

include hcsum in
private lemma step_9 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * abs (cexp (π * I * (n - n₀) * z))) /
    (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) * z.im)) /
    (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · exact aux_6 z
  · have h₁ : ∀ (n : ℤ), Complex.abs (c n) * Complex.abs (cexp (↑π * I * (↑n - ↑n₀) * z)) ≤
        Complex.abs (c n) * rexp (-π * (n - n₀) * z.im) := by
      intro n
      gcongr
      exact aux_7 z n n₀
    apply tsum_le_tsum h₁ (aux_4 z c n₀ hcsum)
    exact aux_10 z c n₀ hcsum

private lemma step_10 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) * z.im)) /
    (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) * z.im)) /
    (∏' (n : ℕ+), (1 - rexp (2 * π * n * z.im)) ^ 24) := by
  gcongr
  · apply mul_nonneg (exp_nonneg (-π * (↑n₀ - 2) * z.im))
    apply tsum_nonneg
    intro i
    exact mul_nonneg (AbsoluteValue.nonneg Complex.abs (c i)) (exp_nonneg _)
  · exact aux_8 z
  · sorry

include hz hn₀ hcsum hpoly in
private lemma step_11 :
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) * z.im)) /
  (∏' (n : ℕ+), (1 - rexp (2 * π * n * z.im)) ^ 24) ≤
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) / 2)) /
  (∏' (n : ℕ+), (1 - rexp (2 * π * n * z.im)) ^ 24) := by
  gcongr
  · exact le_of_lt (aux_8 z)
  · refine tsum_le_tsum ?_ ?_ ?_
    · intro i
      if hi : i < n₀ then
      · specialize hn₀ i hi
        simp [hn₀]
      else
      · simp [AbsoluteValue.nonneg Complex.abs (c i)]
        gcongr -- Bad idea: it goes way too far! exp
        simp only [div_eq_mul_inv,
          mul_comm (-((π * (↑i - ↑n₀)))) (2⁻¹),
          ← neg_mul_eq_mul_neg,
          neg_le_neg_iff,
          mul_comm (π * (↑i - ↑n₀)) (z.im)]
        gcongr
        · rw [not_lt] at hi
          apply mul_nonneg pi_nonneg
          rw [sub_nonneg, Int.cast_le]
          exact hi
        · rw [inv_eq_one_div]
          exact le_of_lt hz
    · exact aux_10 z c n₀ hcsum
    · simp only [div_eq_mul_inv]
      -- *This is where we use the fact that c is eventually polynomial in n.*
      sorry

private lemma step_12 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) / 2)) /
    (∏' (n : ℕ+), (1 - rexp (2 * π * n * z.im)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) / 2)) /
    (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) := by
  gcongr
  · -- This allows us to get rid of the numerators
    apply mul_nonneg
    · exact exp_nonneg _
    · apply tsum_nonneg
      intro i
      exact mul_nonneg (AbsoluteValue.nonneg Complex.abs (c i)) (exp_nonneg _)
  · -- ⊢ The denominator of the RHS is positive (and by the next case, that of the LHS is too)
    -- The following idea is WRONG! tprod_pos_of_pos isn't true: consider fun (n : ℕ) => 1 / 2
    exact aux_11
  · -- ⊢ The denominator of the RHS is ≤ the denominator of the LHS
    -- apply tprod_le_tprod -- But state it without OrderedCommMonoid (or just ℝ) and sorry
    -- Remember that we need each term to be nonneg
    apply tprod_le_of_nonneg
    · sorry
    · sorry
    · sorry

private lemma step_13 :
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) / 2)) /
  (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) =
  (BoundConstntOfPolyFourierCoeff c n₀) * rexp (-π * (n₀ - 2) * z.im) := by
  rw [BoundConstntOfPolyFourierCoeff, mul_div_assoc, mul_comm]



end calc_steps

include f hf z hz c n₀ hn₀ hcsum k hpoly in
theorem BoundedRatioWithDiscOfPolyFourierCoeff : abs ((f z) / (Δ ⟨z, by linarith⟩)) ≤
  (BoundConstntOfPolyFourierCoeff c n₀) * rexp (-π * (n₀ - 2) * z.im) := calc
  _ = abs ((∑' (n : ℤ), c n * cexp (π * I * n * z)) / (cexp (2 * π * I * z) * ∏' (n : ℕ+),
      (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_1 z hz c f hf
  _ = abs ((cexp (π * I * n₀ * z) * ∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_2 z c n₀
  _ = abs ((cexp (π * I * n₀ * z) / cexp (2 * π * I * z)) *
      (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
      (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_3 z c n₀
  _ = abs ((cexp (π * I * (n₀ - 2) * z)) *
      (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
      (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_4 z c n₀
  _ = abs (cexp (π * I * (n₀ - 2) * z)) *
      abs (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
      Complex.abs (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24) := step_5 z c n₀
  _ = abs (cexp (π * I * (n₀ - 2) * z)) * abs (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
      ∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24 := step_6 z c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * abs (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
      (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) := step_7 z c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * abs (cexp (π * I * (n - n₀) * z))) /
      (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) := step_8 z c n₀ hcsum
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) * z.im)) /
      (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) := step_9 z c n₀ hcsum
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) * z.im)) /
      (∏' (n : ℕ+), (1 - rexp (2 * π * n * z.im)) ^ 24) := step_10 z c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) / 2)) /
      (∏' (n : ℕ+), (1 - rexp (2 * π * n * z.im)) ^ 24) := step_11 z hz c n₀ hn₀ hcsum k hpoly
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) / 2)) /
      (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) := step_12 z c n₀
  _ = (BoundConstntOfPolyFourierCoeff c n₀) * rexp (-π * (n₀ - 2) * z.im) := step_13 z c n₀


#check BoundedRatioWithDiscOfPolyFourierCoeff
