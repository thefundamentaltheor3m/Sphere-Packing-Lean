import SpherePacking.Tactic.NormNumI
import Mathlib.Tactic.NormNum


open Complex ComplexConjugate

example : (1:ℂ) = 1 + 0 * I := by norm_num1
example : (I:ℂ) = 0 + 1 * I := by norm_num1
example : (1.5:ℂ) = 3 / 2 + 0 * I := by norm_num1
example : 0 + (1:ℂ) = 1 := by norm_num1
example : (1.0:ℂ) + 0 = 1 := by norm_num1
example : (1.0:ℂ) + 0.5 = 3/2 := by norm_num1
example : I + (3/2:ℂ) = 3/2 + I := by norm_num1
example : 1 * (2:ℂ) = 2 := by norm_num1
example : (1 + I) * (1 + I * I * I) = 2 := by norm_num1
example : (1 + 3.5 + I) * (1 + I) = 7 / 2 + 11 / 2 * I := by norm_num1
example : (3 + 4.5 * I)⁻¹ * (3 + 4.5 * I) = 1 := by norm_num1
example : -1 / (1 + I) = (I - 1) / 2 := by norm_num1
-- example : (1:ℂ) = ⟨1, 0⟩ := by norm_num1
example : (I:ℂ) = 0 + 1 * I := by norm_num1
example : (1.5:ℂ) = ⟨3 / 2, 0⟩ := by conv_lhs => norm_numI
example : 0 + (1:ℂ) = 1 := by norm_num1
example : (1.0:ℂ) + 0 = 1 := by norm_num1
example : (1.0:ℂ) + 0.5 = 3/2 := by norm_num1
example : I + (3/2:ℂ) = 3/2 + I := by norm_num1

example : 2 * (2.5:ℂ) = 5 := by norm_num1
example : (1 + I) * (1 + I * I * I) = 2 := by norm_num1
example : (1 + 3.5 + I) * (1 + I) = 7 / 2 + 11 / 2 * I := by norm_num1
example : (3 + 4 * I)⁻¹ * (3 + 4 * I) = 1 := by norm_num1
example : -1 / (1 + I) = (I - 1) / 2 := by norm_num1
example : (1 + I) * (1 - I) = 2 := by norm_num1
example : (1 + 2 * I) - (1 + 2 * I) = 0 := by norm_num1
example : (conj (3 + 4 * I) : ℂ) * (3 + 4 * I) = 25 := by norm_num1
example : (3 + I : ℂ) ^ 2 = 8 + 6 * I := by norm_num1
example : (3 : ℂ) ^ 2 + (4 : ℂ) ^ 2 = 25 := by norm_num1

example : 3 + I ≠ I ^ 2 := by norm_num1
example : I ^ 2 ≠ 3 := by norm_num1
example : 1 + I ≠ 0 := by norm_num1
example : 1 + I ≠ 1 + 2 * I := by norm_num1

example : re ((1 + 3 * I)⁻¹) = 0.1 := by norm_num1
example : im ((1 + 3 * I)⁻¹) = -0.3 := by norm_num1
example : 10 * re ((1 + 3 * I)⁻¹) = 1 := by norm_num1

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : I^3 + I = 1 := by norm_num1

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : 1 + I = 1 + 2 * I := by norm_num1

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : 2 * I ≠ 2 * I := by norm_num1

/--
error: unsolved goals
x : ℂ
⊢ x * I ≠ 0
-/
#guard_msgs in
-- this crashes if atom identification is buggy
example (x : ℂ) : x * I ≠ 0 := by norm_num1
