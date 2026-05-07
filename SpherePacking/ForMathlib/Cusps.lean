module
public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp

/-!
# Cusps

Lemmas relating zero/boundedness at `i∞` (after slashing by `𝒮ℒ`) to zero/boundedness at all cusps.
-/

open scoped MatrixGroups ModularForm UpperHalfPlane

/-- If `f` vanishes at `i∞` after slashing by all elements of `𝒮ℒ`, then `f` vanishes at every
cusp. -/
public theorem zero_at_cusps_of_zero_at_infty {f : ℍ → ℂ} {c : OnePoint ℝ} {k : ℤ}
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] (hc : IsCusp c 𝒢)
    (hb : ∀ A ∈ 𝒮ℒ, UpperHalfPlane.IsZeroAtImInfty (f ∣[k] A)) : c.IsZeroAt f k :=
  (OnePoint.isZeroAt_iff_forall_SL2Z
    ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).1 hc)).2 fun A _ ↦ hb A ⟨A, rfl⟩

/-- If `f` is bounded at `i∞` after slashing by all elements of `𝒮ℒ`, then `f` is bounded at every
cusp. -/
public theorem bounded_at_cusps_of_bounded_at_infty {f : ℍ → ℂ} {c : OnePoint ℝ} {k : ℤ}
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] (hc : IsCusp c 𝒢)
    (hb : ∀ A ∈ 𝒮ℒ, UpperHalfPlane.IsBoundedAtImInfty (f ∣[k] A)) : c.IsBoundedAt f k :=
  (OnePoint.isBoundedAt_iff_forall_SL2Z
    ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).1 hc)).2 fun A _ ↦ hb A ⟨A, rfl⟩

/-- If `f ∣[k] A = f` for all `A ∈ SL(2,ℤ)`, then boundedness of `f` at `i∞` implies boundedness of
`f ∣[k] A` at `i∞` for all `A ∈ 𝒮ℒ`. -/
public theorem isBoundedAtImInfty_slash_of_slash_eq {f : ℍ → ℂ} {k : ℤ}
    (hslash : ∀ A' : SL(2, ℤ), f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ A') = f)
    (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) :
    ∀ A ∈ 𝒮ℒ, UpperHalfPlane.IsBoundedAtImInfty (f ∣[k] (A : GL (Fin 2) ℝ)) := by
  rintro A ⟨A', rfl⟩; simpa [hslash A'] using hbdd
