import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups


open scoped CongruenceSubgroup MatrixGroups ModularForm UpperHalfPlane

theorem smul_infty_eq_cusp_gamma_one {c : OnePoint ℝ}
    (hc : IsCusp c (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(1))) :
     ∃ A : Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(1),
       A • OnePoint.infty = c := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z
      (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(1))] at hc
  rw [isCusp_SL2Z_iff'] at hc
  obtain ⟨A, hA⟩ := hc
  rw [Subtype.exists]
  use A
  have h1 : Matrix.SpecialLinearGroup.toGL
     ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) A)
       ∈ Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(1) := by
    simp only [Subgroup.mem_map]
    exact ⟨A, CongruenceSubgroup.mem_Gamma_one A, rfl⟩
  use h1
  symm at hA
  have : Matrix.SpecialLinearGroup.toGL
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) A) =
      (Matrix.SpecialLinearGroup.mapGL ℝ) A := rfl
  simp [this, hA]

theorem bounded_at_cusps_of_bounded_at_infty {f : ℍ → ℂ} {c : OnePoint ℝ} {N : ℕ} {k : ℤ}
    [NeZero N] (hc : IsCusp c Γ(N)) (hb : ∀ A ∈ 𝒮ℒ, UpperHalfPlane.IsBoundedAtImInfty (f ∣[k] A)) :
    c.IsBoundedAt f k := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  exact (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun A hA ↦ hb A ⟨A, rfl⟩
