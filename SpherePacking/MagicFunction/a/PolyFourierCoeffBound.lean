/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

import SpherePacking.ModularForms.Eisenstein
import SpherePacking.ForMathlib.tprod
import SpherePacking.ForMathlib.SpecificLimits
import Mathlib

/-

This file contains the proof of Lemma 7.4 in the blueprint, which gives an upper-bound on the ratio
between any function whose Fourier coefficients are O(n^k) and its discriminant.

# TODO:
The only `sorry`s are in the section `calc_aux`, which consists of auxiliary lemmas that are used in
various `calc_steps` lemmas, which in turn make up the proof of the main theorem. Below, we give a
comprehensive list of things to be done, including but not limited to the `sorry`s in this file.
- [ ] `aux_5`: prove `fun i ↦ (1 - cexp (2 * ↑π * I * ↑↑i * z)) ^ 24` is Multipliable
- [ ] `aux_8` and `aux_11`: prove `0 < ∏' (n : ℕ+), (1 - rexp (-2 * π * ↑↑n * z.im)) ^ 24` and
      `0 < ∏' (n : ℕ+), (1 - rexp (-π * ↑↑n)) ^ 24` using the specific properties of the function
      `fun (n : ℕ+) ↦ (1 - rexp (-n * k))` for some parameter `k : ℝ` (there's no general
      `tprod_pos` result for the positivity of infinite products)
- [ ] `aux_11`: prove `0 < ∏' (n : ℕ+), (1 - rexp (-π * ↑↑n)) ^ 24` in similar fashion
- [ ] `step_10`, `step_12`: prove `tprod_le_tprod` in SpherePacking.ForMathlib.tprod
- [ ] `step_11`: prove `summable_real_norm_mul_geometric_of_norm_lt_one` in
      SpherePacking.ForMathlib.SpecificLimits

-/

open Filter Complex Real BigOperators Asymptotics

private noncomputable def fouterm (coeff : ℤ → ℂ) (x : ℂ) (i : ℤ) : ℂ :=
  (coeff i) * cexp (π * I * i * x)

variable (z : ℂ) (hz : 1 / 2 < z.im)
variable (c : ℤ → ℂ) (n₀ : ℤ) -- (hn₀ : ∀ (n : ℤ), n < n₀ → c n = 0)
variable (hcsum : Summable fun (i : ℕ) ↦ (fouterm c z (i + n₀)))
variable (k : ℕ) (hpoly : (fun (n : ℕ) ↦ c (n + n₀)) =O[atTop] (fun (n : ℕ) ↦ (n ^ k : ℝ)))
variable (f : ℂ → ℂ) (hf : ∀ x : ℂ, f x = ∑' (n : ℕ), (fouterm c x (n + n₀)))

noncomputable def DivDiscBound : ℝ :=
  (∑' (n : ℕ), abs (c (n + n₀)) * rexp (-π * n / 2)) /
  (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24)

-- #check DivDiscBound

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
private lemma aux_3 : Summable fun (i : ℕ) ↦ ‖c (i + n₀) * cexp (↑π * I * i * z)‖ := by
  rw [summable_norm_iff]
  have h₁ := Summable.mul_right (cexp (↑π * I * ↑n₀ * z))⁻¹ hcsum
  simp [fouterm, mul_add, add_mul, Complex.exp_add] at h₁
  have h₂ : ∀ (i : ℕ), c (↑i + n₀) * (cexp (↑π * I * ↑i * z) * cexp (↑π * I * ↑n₀ * z)) *
      (cexp (↑π * I * ↑n₀ * z))⁻¹ = c (↑i + n₀) * cexp (↑π * I * ↑i * z) := by
    intro i; field_simp; ac_rfl
  simp only [h₂] at h₁
  exact h₁

include hcsum in
private lemma aux_4 : Summable fun (i : ℕ) ↦ Complex.abs (c (i + n₀)) *
    Complex.abs (cexp (↑π * I * ↑i * z)) := by
  simp_rw [← map_mul, ← Complex.norm_eq_abs]; exact aux_3 z c n₀ hcsum

lemma aux_5 : Complex.abs (∏' (n : ℕ+), (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24) =
  ∏' (n : ℕ+), Complex.abs (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24 := by
  simp only [← abs_pow]
  apply Complex.abs_tprod -- ℕ+ (fun n => (1 - cexp (2 * ↑π * I * n * z)) ^ 24)
  sorry


lemma aux_6 : 0 ≤ ∏' (n : ℕ+), Complex.abs (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24 := by
  rw [← aux_5 z]
  exact AbsoluteValue.nonneg Complex.abs (∏' (n : ℕ+), (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24)

lemma aux_7 (a : ℤ) :
    Complex.abs (cexp (↑π * I * a * z)) ≤ rexp (-π * a * z.im) := by
  rw [mul_comm (π : ℂ) I, mul_assoc, mul_assoc, aux_1 (↑π * (a * z))]
  refine exp_le_exp.2 ?_
  simp; linarith

lemma aux_8 : 0 < ∏' (n : ℕ+), (1 - rexp (-2 * π * ↑↑n * z.im)) ^ 24 := by
  sorry

lemma aux_ring (i : ℕ) : (I * ↑π * ↑i * z) = I * ((↑π * ↑i) * z) := by ring

lemma aux_9 (i : ℕ) :
    ‖c (i + n₀) * cexp (↑π * I * ↑i * z)‖ = ‖c (i + n₀)‖ * rexp (-π * ↑i * z.im) := by
  rw [Complex.norm_eq_abs, Complex.norm_eq_abs, map_mul, mul_comm (↑π) (I)]
  rw [aux_ring, aux_1]
  congr; simp

include hcsum in
lemma aux_10 : Summable fun (n : ℕ) ↦ Complex.abs (c (n + n₀)) * rexp (-π * ↑n * z.im) := by
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

include hf in
private lemma step_1 :
    abs ((f z) / (Δ ⟨z, by linarith⟩)) = abs (
      (∑' (n : ℕ), c (n + n₀) * cexp (π * I * (n + n₀) * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)
    ) := by simp [DiscriminantProductFormula, hf, fouterm, UpperHalfPlane.coe]

private lemma step_2 :
    abs ((∑' (n : ℕ), c (n + n₀) * cexp (π * I * (n + n₀) * z)) /
    (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) =
    abs ((cexp (π * I * n₀ * z) * ∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by
  congr
  rw [← tsum_mul_left]
  congr
  ext n; ring_nf
  rw [mul_assoc (c (n + n₀)) (cexp _), ← Complex.exp_add]
  congr 2
  ring

private lemma step_3 :
    abs ((cexp (π * I * n₀ * z) * ∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) =
    abs ((cexp (π * I * n₀ * z) / cexp (2 * π * I * z)) *
    (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by field_simp

private lemma step_4 :
    abs ((cexp (π * I * n₀ * z) / cexp (2 * π * I * z)) *
    (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) =
    abs ((cexp (π * I * (n₀ - 2) * z)) *
    (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by
  rw [mul_sub, sub_mul, ← Complex.exp_sub]
  congr 6
  ac_rfl

private lemma step_5 :
    abs ((cexp (π * I * (n₀ - 2) * z)) *
    (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) =
    abs (cexp (π * I * (n₀ - 2) * z)) *
    abs (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    Complex.abs (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  simp only [map_div₀, map_mul]

private lemma step_6 :
    abs (cexp (π * I * (n₀ - 2) * z)) *
    abs (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    Complex.abs (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24) =
    abs (cexp (π * I * (n₀ - 2) * z)) *
    abs (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    ∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24 := by congr; exact aux_5 z

private lemma step_7 :
    abs (cexp (π * I * (n₀ - 2) * z)) * abs (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    ∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24 ≤
    rexp (-π * (n₀ - 2) * z.im) * abs (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · exact aux_6 z
  · norm_cast
    exact aux_7 z (n₀ - 2)

include hcsum in
private lemma step_8 :
    rexp (-π * (n₀ - 2) * z.im) * abs (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), abs (c (n + n₀)) * abs (cexp (π * I * n * z))) /
    (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · exact aux_6 z
  · calc
    _ ≤ ∑' (n : ℕ), Complex.abs ((c (n + n₀)) * (cexp (↑π * I * ↑n * z))) := by
      simp_rw [← Complex.norm_eq_abs]
      refine norm_tsum_le_tsum_norm ?_
      exact aux_3 z c n₀ hcsum
    _ = ∑' (n : ℕ), Complex.abs (c (n + n₀)) * Complex.abs (cexp (↑π * I * ↑n * z)) :=
      by simp only [map_mul]

include hcsum in
private lemma step_9 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), abs (c (n + n₀)) * abs (cexp (π * I * n * z))) /
    (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), abs (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · exact aux_6 z
  · have h₁ : ∀ (n : ℕ), Complex.abs (c (n + n₀)) * Complex.abs (cexp (↑π * I * ↑n * z)) ≤
        Complex.abs (c (n + n₀)) * rexp (-π * n * z.im) := by
      intro n
      gcongr
      exact aux_7 z n
    apply tsum_le_tsum h₁ (aux_4 z c n₀ hcsum)
    exact aux_10 z c n₀ hcsum

include hz in
private lemma step_10 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), abs (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), abs (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := by
  gcongr
  · apply mul_nonneg (exp_nonneg (-π * (↑n₀ - 2) * z.im))
    apply tsum_nonneg
    intro i
    exact mul_nonneg (AbsoluteValue.nonneg Complex.abs (c (i + n₀))) (exp_nonneg _)
  · exact aux_8 z
  · apply tprod_le_of_nonneg
    · intro n; simp
      have :
        (1 - rexp (-(2 * π * ↑↑n * z.im))) ^ 24 = ((1 - rexp (-(2 * π * ↑↑n * z.im))) ^ 12) ^ 2 :=
        by ring_nf
      rw [this]
      exact sq_nonneg ((1 - rexp (-(2 * π * ↑↑n * z.im))) ^ 12)
    · intro n; simp
      gcongr
      · simp; positivity
      · have hre : -(2 * π * n * z.im) = (2 * π * I * n * z).re := by field_simp
        rw [hre]
        exact aux_2 (2 * π * I * n * z)

-- set_option maxHeartbeats 100000 in
include hz hcsum hpoly in
private lemma step_11 :
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), abs (c (n + n₀)) * rexp (-π * n * z.im)) /
  (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) ≤
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), abs (c (n + n₀)) * rexp (-π * n / 2)) /
  (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := by
  gcongr
  · exact le_of_lt (aux_8 z)
  · refine tsum_le_tsum ?_ ?_ ?_
    · intro i
      gcongr
      rw [neg_mul, neg_mul, neg_div, neg_le_neg_iff, div_eq_mul_inv, inv_eq_one_div]
      gcongr
    · exact aux_10 z c n₀ hcsum
    · simp only [div_eq_mul_inv]
      -- **This is where we use the fact that c is eventually polynomial in n.**
      have hnorm : ‖(rexp (-π * 2⁻¹) : ℂ)‖ < 1 := by
        rw [Complex.norm_real]
        simp; positivity
      have h₁ : ∀ (n : ℕ), rexp (-π * n * 2⁻¹) = (rexp (-π * 2⁻¹)) ^ n := by
        intro n; symm
        calc (rexp (-π * 2⁻¹)) ^ n
        _ = rexp ((-π * 2⁻¹) * n) := by
          have := (Real.exp_mul (-π * 2⁻¹) n).symm
          norm_cast at this
        _ = rexp (-π * ↑n * 2⁻¹) := by congr 1; ring
      have h₂ : ∀ (n : ℕ), ‖c (↑n + n₀)‖ * rexp (-π * 2⁻¹) ^ n =
          ‖c (↑n + n₀) * rexp (-π * 2⁻¹) ^ n‖ := fun n => by
        rw [norm_mul, neg_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
      simp only [h₁, ← Complex.norm_eq_abs, h₂]
      norm_cast at hpoly
      exact summable_real_norm_mul_geometric_of_norm_lt_one hnorm hpoly

include hz in
private lemma step_12 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), abs (c (n + n₀)) * rexp (-π * n / 2)) /
    (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), abs (c (n + n₀)) * rexp (-π * n / 2)) /
    (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) := by
  gcongr
  · -- This allows us to get rid of the numerators
    apply mul_nonneg
    · exact exp_nonneg _
    · apply tsum_nonneg
      intro i
      exact mul_nonneg (AbsoluteValue.nonneg Complex.abs (c (i + n₀))) (exp_nonneg _)
  · exact aux_11
  · apply tprod_le_of_nonneg
    · intro n; simp
      have : (1 - rexp (-(π * ↑↑n))) ^ 24 = ((1 - rexp (-(π * ↑↑n))) ^ 12) ^ 2 := by ring
      rw [this]
      exact sq_nonneg ((1 - rexp (-(π * ↑↑n))) ^ 12)
    · intro n; simp
      suffices : 1 - rexp (-(π * ↑↑n)) < 1 - rexp (-2 * π * ↑↑n * z.im)
      · apply le_of_lt
        have h₁ : 0 ≤ 1 - rexp (-(π * ↑↑n)) := by norm_num; positivity
        have h₂ : 0 ≤ 1 - rexp (-2 * π * ↑↑n * z.im) := by linarith
        have h₃ : 24 ≠ 0 := by positivity
        have h₄ : (1 - rexp (-(2 * π * ↑↑n * z.im))) ^ 24 = (1 - rexp (-2 * π * ↑↑n * z.im)) ^ 24 :=
          by ring_nf
        rw [h₄]
        exact (pow_lt_pow_iff_left₀ h₁ h₂ h₃).mpr this
      gcongr; simp; ring_nf
      calc π * ↑↑n
      _ ≤ π * ↑↑n * 1 := by rw [mul_one]
      _ < π * ↑↑n * z.im * 2 := by
        rw [mul_assoc (π * ↑↑n), mul_lt_mul_left (by positivity)]
        linarith

private lemma step_13 :
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), abs (c (n + n₀)) * rexp (-π * n / 2)) /
  (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) =
  (DivDiscBound c n₀) * rexp (-π * (n₀ - 2) * z.im) := by
  rw [DivDiscBound, mul_div_assoc, mul_comm]

end calc_steps

section main_theorem

include f hf z hz c n₀ hcsum k hpoly in
theorem DivDiscBoundOfPolyFourierCoeff : abs ((f z) / (Δ ⟨z, by linarith⟩)) ≤
  (DivDiscBound c n₀) * rexp (-π * (n₀ - 2) * z.im) := calc
  _ = abs ((∑' (n : ℕ), c (n + n₀) * cexp (π * I * (n + n₀) * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+),
      (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_1 z hz c n₀ f hf
  _ = abs ((cexp (π * I * n₀ * z) * ∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_2 z c n₀
  _ = abs ((cexp (π * I * n₀ * z) / cexp (2 * π * I * z)) *
      (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_3 z c n₀
  _ = abs ((cexp (π * I * (n₀ - 2) * z)) *
      (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_4 z c n₀
  _ = abs (cexp (π * I * (n₀ - 2) * z)) *
      abs (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      Complex.abs (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24) := step_5 z c n₀
  _ = abs (cexp (π * I * (n₀ - 2) * z)) * abs (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      ∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24 := step_6 z c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * abs (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) := step_7 z c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), abs (c (n + n₀)) * abs (cexp (π * I * n * z))) /
      (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) := step_8 z c n₀ hcsum
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), abs (c (n + n₀)) * rexp (-π * n * z.im)) /
      (∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24) := step_9 z c n₀ hcsum
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), abs (c (n + n₀)) * rexp (-π * n * z.im)) /
      (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := step_10 z hz c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), abs (c (n + n₀)) * rexp (-π * n / 2)) /
      (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := step_11 z hz c n₀ hcsum k hpoly
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), abs (c (n + n₀)) * rexp (-π * n / 2)) /
      (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) := step_12 z hz c n₀
  _ = (DivDiscBound c n₀) * rexp (-π * (n₀ - 2) * z.im) := step_13 z c n₀

-- #check DivDiscBoundOfPolyFourierCoeff

end main_theorem

section Corollaries

end Corollaries
