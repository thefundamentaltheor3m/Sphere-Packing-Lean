module
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction


/-!
# Upper half-plane

This file proves results such as `ModularGroup.modular_S_sq`.
-/

open UpperHalfPlane

/-- Coercion of the `S`-action on `ℍ`: `(S • z : ℂ) = -1 / z`. -/
public theorem ModularGroup.coe_S_smul (z : UpperHalfPlane) :
    (↑(S • z) : ℂ) = (-1 : ℂ) / (z : ℂ) := by
  simpa [div_eq_mul_inv] using congrArg UpperHalfPlane.coe (UpperHalfPlane.modular_S_smul (z := z))

/-- The `S` matrix squares to `-1` in `SL(2, ℤ)`. -/
@[simp] public theorem ModularGroup.modular_S_sq : S * S = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S]

/-- Explicit matrix for `S * T` in `SL(2, ℤ)`. -/
@[simp] public theorem ModularGroup.S_mul_T :
    S * T = ⟨!![0, -1; 1, 1], by norm_num [Matrix.det_fin_two_of]⟩ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S, T]

/-- Coercion of the `(S * T)`-action on `ℍ`: `((S * T) • z : ℂ) = -1 / (z + 1)`. -/
public theorem ModularGroup.coe_ST_smul (z : UpperHalfPlane) :
    (↑((S * T) • z) : ℂ) = (-1 : ℂ) / ((z : ℂ) + 1) := by
  simpa [ModularGroup.S_mul_T] using coe_specialLinearGroup_apply (g := S * T) (z := z)
