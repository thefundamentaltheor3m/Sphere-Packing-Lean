import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Fintype.Parity

-- Probably put it at LinearAlgebra/Matrix/SpecialLinearGroup.lean

theorem ModularGroup.modular_S_sq : S * S = -1 := by
  ext i j
  simp [S]
  fin_cases i <;> fin_cases j <;> simp
