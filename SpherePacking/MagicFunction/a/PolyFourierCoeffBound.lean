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

include z hz c n₀ hn₀ hcsum k hpoly

private lemma step_1 : abs ((f z) / (Δ ⟨z, by linarith⟩)) = abs (
    (∑' (n : ℤ), c n * cexp (π * I * n * z)) /
    cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24
  ) := sorry

end calc_steps

include z hz c n₀ hn₀ hcsum k hpoly in
theorem BoundedRatioWithDiscOfPolyFourierCoeff : abs ((f z) / (Δ ⟨z, by linarith⟩)) ≤
  (BoundConstntOfPolyFourierCoeff c n₀) * rexp (-π * (n₀ - 2) * z.im):=
  sorry

#check BoundedRatioWithDiscOfPolyFourierCoeff
