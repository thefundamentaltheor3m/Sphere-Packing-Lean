import SpherePacking.Tactic.NormNumI
import Mathlib.Tactic.NormNum


set_option trace.debug true

open Complex ComplexConjugate

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

example : -1 / (1 + I) = (I - 1) / 2 := by norm_numI

example : (1:ℂ) = ⟨1, 0⟩ := by norm_numI
example : (I:ℂ) = 0 + 1 * I := by norm_numI
example : (1.5:ℂ) = ⟨3 / 2, 0⟩ := by conv_lhs => norm_numI

example : 0 + (1:ℂ) = 1 := by norm_numI
example : (1.0:ℂ) + 0 = 1 := by norm_numI
example : (1.0:ℂ) + 0.5 = 3/2 := by norm_numI
example : I + (3/2:ℂ) = 3/2 + I := by norm_numI

example : 2 * (2.5:ℂ) = 5 := by norm_numI

example : (1 + I) * (1 + I * I * I) = 2 := by norm_numI

example : (1 + 3.5 + I) * (1 + I) = 7 / 2 + 11 / 2 * I := by norm_numI

example : (3 + 4 * I)⁻¹ * (3 + 4 * I) = 1 := by norm_numI

example : -1 / (1 + I) = (I - 1) / 2 := by norm_numI

example : (1 + I) * (1 - I) = 2 := by norm_numI

example : (1 + 2 * I) - (1 + 2 * I) = 0 := by norm_numI

example : (conj (3 + 4 * I) : ℂ) * (3 + 4 * I) = 25 := by norm_numI

example : (3 + I : ℂ)^2 = 8 + 6 * I := by norm_numI

/-- error: exponent 3 + 4 not handled by norm_numI -/
#guard_msgs in
example : I ^ (3 + 4) = 1 := by norm_numI

/--
error: failed to synthesize
  Neg ℕ
Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
error: exponent -1 not handled by norm_numI
-/
#guard_msgs in
example : I ^ (-1) = - I := by norm_numI

/-- error: Real-part disagreement: LHS normalizes to 0, RHS normalizes to 1 -/
#guard_msgs in
example : I^3 + I = 1 := by norm_numI

/-- error: type of equality is not ℂ -/
#guard_msgs in
example : (1 : ℝ) + (1 : ℝ) = 2 := by norm_numI

example : (3 : ℂ)^2 + (4 : ℂ)^2 = 25 := by
  have : (3 : ℂ)^2 = 9 := by norm_numI
  norm_numI
