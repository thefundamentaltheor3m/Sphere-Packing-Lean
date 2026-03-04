module

public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

namespace InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {u v : E}

theorem natCast_smul_left {a : ℕ} : ⟪a • u, v⟫_𝕜 = a • ⟪u, v⟫_𝕜 := by
  induction a with
  | zero => simp
  | succ n ih =>
    simp only [add_smul, one_smul, add_left] at ih ⊢
    rw [ih]

theorem intCast_smul_left {a : ℤ} : ⟪a • u, v⟫_𝕜 = a • ⟪u, v⟫_𝕜 := by
  cases a with
  | ofNat a => simp only [natCast_smul_left, Int.ofNat_eq_natCast, natCast_zsmul]
  | negSucc a => simp only [negSucc_zsmul, inner_neg_left, natCast_smul_left]

theorem natCast_smul_right {a : ℕ} : ⟪u, a • v⟫_𝕜 = a • ⟪u, v⟫_𝕜 := by
  induction a with
  | zero => simp
  | succ n ih =>
    simp only [add_smul, one_smul, inner_add_right] at ih ⊢
    rw [ih]

theorem intCast_smul_right {a : ℤ} : ⟪u, a • v⟫_𝕜 = a • ⟪u, v⟫_𝕜 := by
  cases a with
  | ofNat a => simp only [natCast_smul_right, Int.ofNat_eq_natCast, natCast_zsmul]
  | negSucc a => simp only [negSucc_zsmul, inner_neg_right, natCast_smul_right]

end InnerProductSpace
