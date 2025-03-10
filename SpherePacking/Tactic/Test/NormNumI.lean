import SpherePacking.Tactic.NormNumI


set_option trace.debug true

open Complex

example : (1:ℂ) = 1 + 0 * I := by norm_numI
example : (I:ℂ) = 0 + 1 * I := by norm_numI
example : (1.5:ℂ) = 3 / 2 + 0 * I := by norm_numI

example : 0 + (1:ℂ) = 1 := by norm_numI
example : (1.0:ℂ) + 0 = 1 := by norm_numI
example : (1.0:ℂ) + 0.5 = 3/2 := by norm_numI
example : I + (3/2:ℂ) = 3/2 + I := by norm_numI

example : 1 * (2:ℂ) = 2 := by norm_numI

example : (1 + I) * (1 + I * I * I) = 2 := by norm_numI

example : (1 + 3.5 + I) * (1 + I) = 7 / 2 + 11 / 2 * I := by norm_numI

example : (3 + 4.5 * I)⁻¹ * (3 + 4.5 * I) = 1 := by norm_numI

example : -1 / (1 + I) = (I - 1) / 2 := by
  conv =>
    enter [2, 1]
  sorry
