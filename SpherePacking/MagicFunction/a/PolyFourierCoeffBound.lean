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

variable {z : ℂ} (hz : 1 / 2 < z.im)
variable (c : ℤ → ℂ) (n₀ : ℤ) (hn₀ : ∀ (n : ℤ), n < n₀ → c n = 0)
variable (hcsum : Summable (fouterm c z))
variable {k : ℕ} (hpoly : c =O[atTop] fun n => n ^ k)

-- private noncomputable def f (x : ℂ) : ℂ := ∑' (n : ℤ), (fouterm c x n)

local notation "f" => fun (x : ℂ) => ∑' (n : ℤ), (fouterm c x n)
#check f z

noncomputable def BoundConstntOfPolyFourierCoeff : ℝ :=
  (∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) / 2)) /
  (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24)

#check BoundConstntOfPolyFourierCoeff

section calc_steps

-- include z hz c n₀ hn₀ hcsum k hpoly

private lemma step_1 : abs ((f z) / (Δ ⟨z, by linarith⟩)) = abs (
    (∑' (n : ℤ), c n * cexp (π * I * n * z)) /
    (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)
  ) := by simp_rw [DiscriminantProductFormula, fouterm, UpperHalfPlane.coe]

private lemma step_2 : abs ((∑' (n : ℤ), c n * cexp (π * I * n * z)) /
  (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) =
  abs (cexp (π * I * (n₀ - 2) * z)) * abs (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
  ∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24 := sorry

private lemma step_3_aux_1 : abs (cexp (π * I * (n₀ - 2) * z)) ≤ rexp (-π * (n₀ - 2) * z.im) := by
  sorry

-- Below was written by Bhavik
private lemma step_3_aux_2 (x : ℂ) : 1 - Real.exp x.re ≤ Complex.abs (1 - cexp x) := calc
  abs (1 - cexp x) ≥ |Complex.abs 1 - abs (cexp x)| := abs.abs_abv_sub_le_abv_sub _ _
  _ = |1 - rexp x.re| := by simp [Complex.abs_exp]
  _ ≥ _ := le_abs_self _

private lemma step_3 : abs (cexp (π * I * (n₀ - 2) * z)) *
  abs (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
  ∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24 ≤  rexp (-π * (n₀ - 2) * z.im) *
  ∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) * z.im) /
  ∏' (n : ℕ+), (1 - rexp (2 * π * n * z.im)) ^ 24 := sorry

end calc_steps

include z hz c n₀ hn₀ hcsum k hpoly in
theorem BoundedRatioWithDiscOfPolyFourierCoeff : abs ((f z) / (Δ ⟨z, by linarith⟩)) ≤
  (BoundConstntOfPolyFourierCoeff c n₀) * rexp (-π * (n₀ - 2) * z.im) := calc
  _ = abs ((∑' (n : ℤ), c n * cexp (π * I * n * z)) / (cexp (2 * π * I * z) * ∏' (n : ℕ+),
      (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_1 hz c
  _ = abs (cexp (π * I * (n₀ - 2) * z)) * abs (∑' (n : ℤ), c n * cexp (π * I * (n - n₀) * z)) /
      ∏' (n : ℕ+), abs (1 - cexp (2 * π * I * n * z)) ^ 24 := step_2 c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * ∑' (n : ℤ), abs (c n) * rexp (-π * (n - n₀) * z.im) /
      ∏' (n : ℕ+), (1 - rexp (2 * π * n * z.im)) ^ 24 := step_3 c n₀
  _ ≤ (BoundConstntOfPolyFourierCoeff c n₀) * rexp (-π * (n₀ - 2) * z.im) := sorry


#check BoundedRatioWithDiscOfPolyFourierCoeff
