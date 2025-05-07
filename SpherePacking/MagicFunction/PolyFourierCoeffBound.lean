/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

import SpherePacking.ForMathlib.Fourier
import SpherePacking.ForMathlib.SpecificLimits
import SpherePacking.ForMathlib.tprod
import SpherePacking.ModularForms.Eisenstein


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
open scoped UpperHalfPlane

private noncomputable def fouterm (coeff : ℤ → ℂ) (x : ℂ) (i : ℤ) : ℂ :=
  (coeff i) * cexp (π * I * i * x)

variable (z : ℍ) (hz : 1 / 2 < z.im)
variable (c : ℤ → ℂ) (n₀ : ℤ) (hcn₀ : c n₀ ≠ 0) -- (hn₀ : ∀ (n : ℤ), n < n₀ → c n = 0)
variable (hcsum : Summable fun (i : ℕ) ↦ (fouterm c z (i + n₀)))
variable (k : ℕ) (hpoly : c =O[atTop] (fun n ↦ (n ^ k : ℝ)))
--  Change to just `c n` is polynomial. Should work!
variable (f : ℍ → ℂ) (hf : ∀ x : ℍ, f x = ∑' (n : ℕ), (fouterm c x (n + n₀)))

noncomputable def DivDiscBound : ℝ :=
  (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
  (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24)

-- #check DivDiscBound

section hpoly_aux

include hpoly in
theorem hpoly' : (fun (n : ℕ) ↦ c (n + n₀)) =O[atTop] (fun (n : ℕ) ↦ (n ^ k : ℝ)) := by
  simp [isBigO_iff] at hpoly ⊢
  obtain ⟨C, m, hCa⟩ := hpoly
  use C
  use (m - n₀).toNat
  sorry

end hpoly_aux

section calc_aux

-- These could even go in Mathlib... they look useful (if a bit random)

private lemma aux_1 (x : ℂ) : norm (cexp (I * x)) = rexp (-x.im) := by
  have h₁ : I * (↑x.im * I) = -x.im := by rw [mul_comm, mul_assoc, Complex.I_mul_I, mul_neg_one]
  rw [← x.re_add_im, mul_add, h₁, Complex.norm_exp]
  simp

-- Below was written by Bhavik
private lemma aux_2 (x : ℂ) : 1 - Real.exp x.re ≤ norm (1 - cexp x) := calc
  norm (1 - cexp x) ≥ |‖(1 : ℂ)‖ - norm (cexp x)| := abs_norm_sub_norm_le 1 (cexp x)
  _ = |1 - rexp x.re| := by simp [Complex.norm_exp]
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
private lemma aux_4 : Summable fun (i : ℕ) ↦ norm (c (i + n₀)) *
    norm (cexp (↑π * I * ↑i * z)) := by
  simp_rw [← norm_mul]; exact aux_3 z c n₀ hcsum

lemma aux_5 (z : ℍ) : norm (∏' (n : ℕ+), (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24) =
  ∏' (n : ℕ+), norm (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24 := by
  simp only [← norm_pow]
  apply Multipliable.norm_tprod -- ℕ+ (fun n => (1 - cexp (2 * ↑π * I * n * z)) ^ 24)
  apply MultipliableDeltaProductExpansion_pnat z


lemma aux_6 (z : ℍ) : 0 ≤ ∏' (n : ℕ+), norm (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24 := by
  rw [← aux_5 z]
  exact norm_nonneg _

lemma aux_7 (a : ℤ) :
    norm (cexp (↑π * I * a * z)) ≤ rexp (-π * a * z.im) := by
  rw [mul_comm (π : ℂ) I, mul_assoc, mul_assoc, aux_1 (↑π * (a * z))]
  refine exp_le_exp.2 ?_
  simp; linarith

include hz in
lemma aux_8 : 0 < ∏' (n : ℕ+), (1 - rexp (-2 * π * ↑↑n * z.im)) ^ 24 := by
  sorry

lemma aux_ring (i : ℕ) : (I * ↑π * ↑i * z) = I * ((↑π * ↑i) * z) := by ring

lemma aux_9 (i : ℕ) :
    ‖c (i + n₀) * cexp (↑π * I * ↑i * z)‖ = ‖c (i + n₀)‖ * rexp (-π * ↑i * z.im) := by
  rw [norm_mul, mul_comm (↑π) (I)]
  rw [aux_ring, aux_1]
  congr; simp

include hcsum in
lemma aux_10 : Summable fun (n : ℕ) ↦ norm (c (n + n₀)) * rexp (-π * ↑n * z.im) := by
  simp only [← aux_9, aux_ring]
  exact aux_3 z c n₀ hcsum

lemma aux_11 : 0 < ∏' (n : ℕ+), (1 - rexp (-π * ↑↑n)) ^ 24 := by
  sorry

lemma aux_misc (x : ℍ) : norm (cexp (I * x)) ≤ rexp (x.im) := by
  rw [aux_1 x]
  refine exp_le_exp.2 ?_
  rw [UpperHalfPlane.coe_im, neg_le_self_iff]
  exact le_of_lt x.2

end calc_aux

section calc_steps

include hf in
private lemma step_1 :
    norm ((f z) / (Δ z)) = norm (
      (∑' (n : ℕ), c (n + n₀) * cexp (π * I * (n + n₀) * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)
    ) := by simp [DiscriminantProductFormula, hf, fouterm, UpperHalfPlane.coe];

private lemma step_2 :
    norm ((∑' (n : ℕ), c (n + n₀) * cexp (π * I * (n + n₀) * z)) /
    (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) =
    norm ((cexp (π * I * n₀ * z) * ∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by
  congr
  rw [← tsum_mul_left]
  congr
  ext n; ring_nf
  rw [mul_assoc (c (n + n₀)) (cexp _), ← Complex.exp_add]
  congr 2
  ring

private lemma step_3 :
    norm ((cexp (π * I * n₀ * z) * ∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) =
    norm ((cexp (π * I * n₀ * z) / cexp (2 * π * I * z)) *
    (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by field_simp

private lemma step_4 :
    norm ((cexp (π * I * n₀ * z) / cexp (2 * π * I * z)) *
    (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) =
    norm ((cexp (π * I * (n₀ - 2) * z)) *
    (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by
  rw [mul_sub, sub_mul, ← Complex.exp_sub]
  congr 6
  ac_rfl

private lemma step_5 :
    norm ((cexp (π * I * (n₀ - 2) * z)) *
    (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) =
    norm (cexp (π * I * (n₀ - 2) * z)) *
    norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    norm (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  simp only [norm_div, norm_mul]

private lemma step_6  :
    norm (cexp (π * I * (n₀ - 2) * z)) *
    norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    norm (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24) =
    norm (cexp (π * I * (n₀ - 2) * z)) *
    norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    ∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24 := by congr; exact aux_5 z

private lemma step_7 :
    norm (cexp (π * I * (n₀ - 2) * z)) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    ∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24 ≤
    rexp (-π * (n₀ - 2) * z.im) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · exact aux_6 z
  · norm_cast
    exact aux_7 z (n₀ - 2)

include hcsum in
private lemma step_8  :
    rexp (-π * (n₀ - 2) * z.im) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * norm (cexp (π * I * n * z))) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · exact aux_6 z
  · calc
    _ ≤ ∑' (n : ℕ), norm ((c (n + n₀)) * (cexp (↑π * I * ↑n * z))) := by
      refine norm_tsum_le_tsum_norm ?_
      exact aux_3 z c n₀ hcsum
    _ = ∑' (n : ℕ), norm (c (n + n₀)) * norm (cexp (↑π * I * ↑n * z)) :=
      by simp only [norm_mul]

include hcsum in
private lemma step_9 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * norm (cexp (π * I * n * z))) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · exact aux_6 z
  · have h₁ : ∀ (n : ℕ), norm (c (n + n₀)) * norm (cexp (↑π * I * ↑n * z)) ≤
        norm (c (n + n₀)) * rexp (-π * n * z.im) := by
      intro n
      gcongr
      exact aux_7 z n
    apply Summable.tsum_le_tsum h₁ (aux_4 z c n₀ hcsum)
    exact aux_10 z c n₀ hcsum

include hz in
private lemma step_10 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := by
  gcongr
  · exact aux_8 z hz
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
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
  (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) ≤
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
  (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := by
  gcongr
  · exact le_of_lt (aux_8 z hz)
  · refine Summable.tsum_le_tsum ?_ ?_ ?_
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
        rw [norm_mul, neg_mul, norm_pow, Complex.norm_real]
        simp
      simp only [h₁, h₂]
      -- norm_cast at hpoly
      have := hpoly' c n₀ k hpoly
      norm_cast at this
      exact summable_real_norm_mul_geometric_of_norm_lt_one hnorm this

include hz in
private lemma step_12 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
    (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
    (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) := by
  gcongr
  · -- This allows us to get rid of the numerators
    exact aux_11
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
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
  (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) =
  (DivDiscBound c n₀) * rexp (-π * (n₀ - 2) * z.im) := by
  rw [DivDiscBound, mul_div_assoc, mul_comm]

end calc_steps

section main_theorem

/-
This section contains the proof of the main result of this file.
-/

include f hf z hz c n₀ hcsum k hpoly in
theorem DivDiscBoundOfPolyFourierCoeff : norm ((f z) / (Δ z)) ≤
  (DivDiscBound c n₀) * rexp (-π * (n₀ - 2) * z.im) := calc
  _ = norm ((∑' (n : ℕ), c (n + n₀) * cexp (π * I * (n + n₀) * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+),
      (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_1 z c n₀ f hf
  _ = norm ((cexp (π * I * n₀ * z) * ∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_2 z c n₀
  _ = norm ((cexp (π * I * n₀ * z) / cexp (2 * π * I * z)) *
      (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_3 z c n₀
  _ = norm ((cexp (π * I * (n₀ - 2) * z)) *
      (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_4 z c n₀
  _ = norm (cexp (π * I * (n₀ - 2) * z)) *
      norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      norm (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24) := step_5 z c n₀
  _ = norm (cexp (π * I * (n₀ - 2) * z)) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      ∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24 := step_6 z c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := step_7 z c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * norm (cexp (π * I * n * z))) /
      (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := step_8 z c n₀ hcsum
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
      (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := step_9 z c n₀ hcsum
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
      (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := step_10 z hz c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
      (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := step_11 z hz c n₀ hcsum k hpoly
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
      (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) := step_12 z hz c n₀
  _ = (DivDiscBound c n₀) * rexp (-π * (n₀ - 2) * z.im) := step_13 z c n₀

-- #check DivDiscBoundOfPolyFourierCoeff

end main_theorem

section positivity

-- Note that this proof does NOT use our custom `summable_norm_pow_mul_geometric_of_norm_lt_one`
-- for functions with real inputs (see SpherePacking.ForMathlib.SpecificLimits).
include hpoly hcn₀ in
theorem DivDiscBound_pos : 0 < DivDiscBound c n₀ := by
  rw [DivDiscBound]
  apply div_pos
  · refine Summable.tsum_pos ?_ ?_ 0 ?_
    · have h₁ (n : ℕ) : norm (c (↑n + n₀)) * rexp (-π * ↑n / 2) =
          ‖(c (↑n + n₀)) * rexp (-π * ↑n / 2)‖ := by
        rw [norm_mul]
        norm_cast
        simp
      simp only [h₁, summable_norm_iff]
      have h₂ : (fun (n : ℕ) ↦ c (↑n + n₀) * rexp (-π * ↑n / 2)) =O[atTop]
          (fun (n : ℕ) ↦ (n ^ k) * rexp (-π * ↑n / 2)) := by
        refine IsBigO.mul (hpoly' c n₀ k hpoly) ?_
        norm_cast
        exact isBigO_refl _ atTop
      refine summable_of_isBigO_nat ?_ h₂
      have h₃ (n : ℕ) : rexp (-π * ↑n / 2) = (rexp (-π / 2)) ^ n := by
        symm; calc (rexp (-π / 2)) ^ n
        _ = rexp ((-π / 2) * n) := by
          rw [(Real.exp_mul (-π / 2) n)]
          norm_cast
        _ = rexp (-π * ↑n / 2) := by ring_nf
      simp only [h₃]
      rw [← summable_norm_iff]
      refine summable_norm_pow_mul_geometric_of_norm_lt_one k ?_
      simp [neg_div, pi_pos]
    · intro i
      positivity
    · simp [hcn₀]
  · sorry
    -- Use new result that Δ(iz) > 0 [TODO: BUMP]
    -- calc 0
    -- _ < ∏' (n : ℕ+), (1 - rexp (-2 * π * ↑↑n * (1 / 2 * I).im)) ^ 24 := aux_8 (1 / 2 * I) (by sorry)
    -- _ = ∏' (n : ℕ+), (1 - rexp (-π * ↑↑n)) ^ 24 := by
    --   congr
    --   ext n
    --   congr 3
    --   simp
    --   ring

end positivity

open ArithmeticFunction Nat

section sigma

/-
Recall that σₖ(n) = ∑ {d | n}, d ^ k. In this section, we prove that for all n,
σₖ(n) = O(n ^ (k + 1)).
-/

theorem ArithmeticFunction.sigma_asymptotic (k : ℕ) :
    (fun n ↦ (σ k n : ℝ)) =O[atTop] (fun n ↦ (n ^ (k + 1) : ℝ)) := by
  rw [isBigO_iff]
  use 1
  simp only [Real.norm_natCast, norm_pow, one_mul, eventually_atTop, ge_iff_le]
  use 1
  intro n hn
  rw [sigma_apply]
  norm_cast
  calc ∑ d ∈ n.divisors, d ^ k
  _ ≤ ∑ d ∈ n.divisors, n ^ k := by
      apply Finset.sum_le_sum
      intro d hd
      refine pow_le_pow ?_ hn le_rfl
      exact Nat.divisor_le hd
  _ ≤ n * n ^ k := by
      rw [Finset.sum_const, smul_eq_mul]
      gcongr
      exact Nat.card_divisors_le_self n
  _ = n ^ (k + 1) := by ring

theorem ArithmeticFunction.sigma_asymptotic' (k : ℕ) :
    (fun n ↦ (σ k n : ℂ)) =O[atTop] (fun n ↦ (n ^ (k + 1) : ℂ)) := by
  have (n : ℕ) : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
  simp only [this]
  rw [isBigO_ofReal_left]
  norm_cast
  simp only [Nat.cast_pow]
  exact ArithmeticFunction.sigma_asymptotic k

end sigma

section Corollaries

theorem norm_φ₀_le : ∃ C₀ > 0, ∀ z : ℍ, 1 / 2 < z.im →
    norm (φ₀ z) ≤ C₀ * rexp (-2 * π * z.im) := by
  -- This is a reasonable thing to do because all inputs are in nonnegative
  let c : ℤ → ℂ := fun n ↦ n * (σ 3 n.toNat)
  let d : ℕ → ℂ := fun n ↦ n * (σ 3 n)
  have hcd (n : ℕ) : c n = d n := by congr
  have hdpoly : d =O[atTop] (fun n ↦ (n ^ 5 : ℂ)) := by
    have h₁ (n : ℕ) : n ^ 5 = n * n ^ 4 := by exact Nat.pow_succ'
    norm_cast
    simp only [h₁]
    push_cast
    refine IsBigO.mul (isBigO_refl _ atTop) ?_
    have h := ArithmeticFunction.sigma_asymptotic' 3
    simp only [Nat.reduceAdd] at h
    norm_cast at h ⊢
  have hcpoly : c =O[atTop] (fun n ↦ (n ^ 5 : ℝ)) := by
    -- Use `Asymptotics.IsBigO.congr'` to relate properties of c to properties of d
    simp only [isBigO_iff, norm_pow, Complex.norm_natCast, eventually_atTop,
      ge_iff_le] at hdpoly ⊢
    obtain ⟨R, m, hR⟩ := hdpoly
    use R, m
    intro n hn
    have hnnonneg : 0 ≤ n := calc 0
      _ ≤ (m : ℤ) := by positivity
      _ ≤ ↑n := hn
    have hnnat : n.toNat = n := by
      simp only [Int.ofNat_toNat, sup_eq_left, hnnonneg]
    have hmnnat : m ≤ n.toNat := by
      zify
      rw [hnnat]
      exact hn
    specialize hR n.toNat hmnnat
    rw [← hcd, hnnat] at hR
    calc norm (c n)
    _ ≤ R * n.toNat ^ 5 := hR
      -- rwa [Real.norm_natCast] at hR
    _ = R * |↑n| ^ 5 := by
      simp only [mul_eq_mul_left_iff, Nat.cast_nonneg, norm_nonneg, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, pow_left_inj₀]
      norm_cast
      left
      rw [cast_pow, hnnat]
      simp [hnnonneg, abs_of_nonneg]
  use DivDiscBound c 4
  constructor
  · rw [gt_iff_lt]
    refine DivDiscBound_pos c 4 ?_ 5 hcpoly
    have : c 4 = 4 * (σ 3 4) := rfl
    rw [this]
    simp only [ne_eq, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, cast_eq_zero, false_or]
    have : ¬((σ 3) 4 = 0) ↔ ¬ (∑ d ∈ divisors 4, d ^ 3 = 0) := by rfl
    rw [this]
    simp only [Finset.sum_eq_zero_iff, mem_divisors, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, and_true, pow_eq_zero_iff, not_forall, Classical.not_imp]
    exact ⟨2, (by norm_num), (by norm_num)⟩
  · simp only [φ₀]
    intro z hz
    calc _ ≤ _ := DivDiscBoundOfPolyFourierCoeff z hz c 4 ?_ 5 hcpoly
          (fun z ↦ ((E₂ z) * (E₄ z) - (E₆ z)) ^ 2) ?_
      _ = _ := by congr 2; ring
    ·
      sorry
    · -- This is where I need to use Bhavik's result

      sorry
    -- · sorry
    -- · sorry

end Corollaries
