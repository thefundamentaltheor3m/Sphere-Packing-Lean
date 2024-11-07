/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

import SpherePacking.ModularForms.Eisenstein
import Mathlib

open Filter Complex Real BigOperators

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
  Complex.abs (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24) := by simp only [map_div₀, map_mul]

private lemma step_6 :
  abs (cexp (π * I * (n₀ - 2) * z)) *
  abs (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
  Complex.abs (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24) =
  abs (cexp (π * I * (n₀ - 2) * z)) *
  abs (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
  ∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24 := by
  congr
  -- Not quite sure how to go from here. Doesn't seem to be in the library.
  -- Here's one approach, but I suspect it's not the best...

  sorry

private lemma step_7 :
  abs (cexp (π * I * (n₀ - 2) * z)) * abs (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
  ∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24 ≤
  rexp (-π * (n₀ - 2) * z.im) * abs (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
  (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) := by

  sorry

include hcsum in
private lemma step_8 :
    rexp (-π * (n₀ - 2) * z.im) * abs (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
    (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * abs (cexp (π * I * (n - n₀) * z))) /
    (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · -- tprod of nonneg is nonneg!
    sorry
  · calc
    _ ≤ ∑' (n : ℤ), Complex.abs ((c n) * (cexp (↑π * I * (↑n - ↑n₀) * z))) := by
      -- refine tsum_le_abs ?_
      simp_rw [← Complex.norm_eq_abs]
      refine norm_tsum_le_tsum_norm ?_
      exact aux_3 z c n₀ hcsum
    _ = ∑' (n : ℤ), Complex.abs (c n) * Complex.abs (cexp (↑π * I * (↑n - ↑n₀) * z)) := by simp only [map_mul]

include hcsum in
private lemma step_9 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * abs (cexp (π * I * (n - n₀) * z))) /
    (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) * z.im)) /
    (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · sorry
  · have h₁ : ∀ (n : ℤ), Complex.abs (c n) * Complex.abs (cexp (↑π * I * (↑n - ↑n₀) * z)) ≤
        Complex.abs (c n) * rexp (-π * (n - n₀) * z.im) := by
      sorry
    apply tsum_le_tsum h₁ (aux_4 z c n₀ hcsum)
    sorry

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
  · sorry
  · sorry

private lemma step_11 :
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) * z.im)) /
  (∏' (n : ℕ+), (1 - rexp (2 * π * n * z.im)) ^ 24) ≤
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) / 2)) /
  (∏' (n : ℕ+), (1 - rexp (2 * π * n * z.im)) ^ 24) := by
  sorry

private lemma step_12 :
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) / 2)) /
  (∏' (n : ℕ+), (1 - rexp (2 * π * n * z.im)) ^ 24) ≤
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) / 2)) /
  (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) := by
  sorry

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
      (∏' (n : ℕ+), (1 - rexp (2 * π * n * z.im)) ^ 24) := step_11 z c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) / 2)) /
      (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) := step_12 z c n₀
  _ = (BoundConstntOfPolyFourierCoeff c n₀) * rexp (-π * (n₀ - 2) * z.im) := step_13 z c n₀


#check BoundedRatioWithDiscOfPolyFourierCoeff
