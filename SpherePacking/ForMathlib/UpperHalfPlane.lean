import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Fintype.Parity

-- Probably put it at LinearAlgebra/Matrix/SpecialLinearGroup.lean

theorem ModularGroup.modular_S_sq : S * S = -1 := by
  ext i j
  simp only [S, Int.reduceNeg, Matrix.SpecialLinearGroup.coe_mul, Matrix.cons_mul,
    Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.vecMul_cons, Matrix.head_cons, zero_smul,
    Matrix.tail_cons, neg_smul, one_smul, Matrix.neg_cons, neg_zero, Matrix.neg_empty,
    Matrix.empty_vecMul, add_zero, zero_add, Matrix.empty_mul, Equiv.symm_apply_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
    Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply]
  fin_cases i <;> fin_cases j <;> rfl
