import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

open scoped CongruenceSubgroup MatrixGroups ModularForm UpperHalfPlane

theorem zero_at_cusps_of_zero_at_infty {f : ℍ → ℂ} {c : OnePoint ℝ} {N : ℕ} {k : ℤ}
    [NeZero N] (hc : IsCusp c Γ(N)) (hb : ∀ A ∈ 𝒮ℒ, UpperHalfPlane.IsZeroAtImInfty (f ∣[k] A)) :
    c.IsZeroAt f k := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  refine (OnePoint.isZeroAt_iff_forall_SL2Z hc).mpr fun A hA ↦ hb A ⟨A, rfl⟩

theorem bounded_at_cusps_of_bounded_at_infty {f : ℍ → ℂ} {c : OnePoint ℝ} {N : ℕ} {k : ℤ}
    [NeZero N] (hc : IsCusp c Γ(N)) (hb : ∀ A ∈ 𝒮ℒ, UpperHalfPlane.IsBoundedAtImInfty (f ∣[k] A)) :
    c.IsBoundedAt f k := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  exact (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun A hA ↦ hb A ⟨A, rfl⟩
