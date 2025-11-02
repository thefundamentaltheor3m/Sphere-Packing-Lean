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

-- TODO: if this theorem is actually true with no additional hypotheses, then
-- we don't need the above theorem.
theorem bounded_at_cusps_of_bounded_at_infty
    {f : ℍ → ℂ}
    {c : OnePoint ℝ}
    {N : ℕ} {k : ℤ}
    (hc : IsCusp c (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(N)))
    (hb : ∀ A : Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(N),
               UpperHalfPlane.IsBoundedAtImInfty (f ∣[k] (A : GL (Fin 2) ℝ))) :
    c.IsBoundedAt f k := by
  rcases hc with ⟨A, hA, hAp, hAc⟩
  rcases Subgroup.mem_map.mp hA with ⟨g, hg_in_ΓN, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℚ, c = OnePoint.some (q : ℝ) := by
    sorry

  have hg_par : (g : GL (Fin 2) ℝ).IsParabolic := hAp
  obtain ⟨σ, hσ⟩ : ∃ σ : SL(2, ℤ), (Matrix.SpecialLinearGroup.mapGL ℝ σ) • OnePoint.infty = c := by
    obtain ⟨n, d, hd, hr⟩ := q
    sorry

  have hGn : Γ(N).Normal := CongruenceSubgroup.Gamma_normal N
  have hconj : σ⁻¹ * g * σ ∈ Γ(N) := Subgroup.Normal.conj_mem' hGn g hg_in_ΓN σ
  have hstablizer : (Matrix.SpecialLinearGroup.mapGL ℝ (σ⁻¹ * g * σ)) • (OnePoint.infty (X := ℝ)) =
                    OnePoint.infty := by
    sorry

  rw [OnePoint.isBoundedAt_iff hσ]
  sorry
