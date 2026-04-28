module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Data.Fintype.Parity

@[expose] public section

-- Probably put it at LinearAlgebra/Matrix/SpecialLinearGroup.lean

theorem ModularGroup.modular_S_sq : S * S = -1 := by
  ext i j
  simp [S]
  fin_cases i <;> fin_cases j <;> simp
