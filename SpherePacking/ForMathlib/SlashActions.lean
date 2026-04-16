module

public import SpherePacking.ForMathlib.MDifferentiableFunProp
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.ModularForms.SlashActions

@[expose] public section

-- Maybe this belongs in NumberTheory/ModularForms/SlashActions.lean, next to ModularForm.mul_slash

local notation "GL(" n ", " R ")" "⁺" => @Matrix.GLPos (Fin n) R (instDecidableEqFin n)
  (Fin.fintype n) Real.linearOrderedCommRing

open ModularForm MatrixGroups UpperHalfPlane
open scoped Manifold

/- Looks like the way to fix the errors is to replace each GL(n, ℝ)⁺ with
  `@Matrix.GLPos (Fin 2) ℝ (instDecidableEqFin 2) (Fin.fintype 2) Real.linearOrderedCommRing :
  Subgroup (GL (Fin 2) ℝ)`... but it's just so ugly!
-/

/-- Slash action under -I₂ as a GL(n, ℝ)⁺ matrix. See `ModularForm.slash_neg_one'` for the SL(2, ℤ)
version. -/
theorem ModularForm.slash_neg_one {k : ℤ} (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-1 : (GL (Fin 2) ℝ)) =
    f ∣[k] (1 : (GL (Fin 2) ℝ)) := by
  simp [slash_def, denom, hk.neg_one_zpow, Matrix.det_neg, σ]

/-- Slash action under -I₂ as a SL(2, ℤ) matrix. See `ModularForm.slash_neg_one` for the GL(n, ℝ)⁺
version. -/
theorem ModularForm.slash_neg_one' {k : ℤ} (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-1 : SL(2, ℤ)) = f ∣[k] (1 : SL(2, ℤ)) := by
  simp [SL_slash_def, denom, hk.neg_one_zpow]

/-- See `ModularForm.slash_neg'` for the version where `g` is a SL(2, ℤ) matrix. -/
theorem ModularForm.slash_neg {k : ℤ} (g : GL (Fin 2) ℝ) (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-g) = f ∣[k] g := by
  rw [← neg_one_mul, SlashAction.slash_mul, slash_neg_one f hk, SlashAction.slash_one]

/-- See `ModularForm.slash_neg` for the version where `g` is a GL(n, ℝ)⁺ matrix. -/
theorem ModularForm.slash_neg' {k : ℤ} (g : SL(2, ℤ)) (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-g) = f ∣[k] g := by
  rw [SL_slash, ← slash_neg _ _ hk]
  congr
  aesop

/--
Bridge `MDifferentiableAt` on the upper half-plane with ordinary complex differentiability.
-/
lemma MDifferentiableAt_DifferentiableAt {F : ℍ → ℂ} {z : ℍ}
    (h : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F z) :
    DifferentiableAt ℂ (F ∘ ofComplex) ↑z := by
  have h₁ : DifferentiableWithinAt ℂ (F ∘ ofComplex) Set.univ ↑z := by
    simpa [writtenInExtChartAt, extChartAt, Set.range_id] using
      MDifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt h
  exact differentiableWithinAt_univ.1 h₁

/--
Ordinary complex differentiability near a point of `ℍ` gives `MDifferentiableAt` after coercion.
-/
lemma DifferentiableAt_MDifferentiableAt {G : ℂ → ℂ} {z : ℍ}
    (h : DifferentiableAt ℂ G ↑z) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (G ∘ (↑) : ℍ → ℂ) z := by
  rw [mdifferentiableAt_iff]
  apply DifferentiableAt.congr_of_eventuallyEq h
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp [Function.comp_apply, ofComplex_apply_of_im_pos hw]

section SlashActionDifferentiableHelpers

open ModularGroup

variable (γ : SL(2, ℤ))

/-- Differentiability of `denom`. -/
lemma differentiableAt_denom (z : ℂ) :
    DifferentiableAt ℂ (fun w => denom γ w) z := by
  simp only [denom]
  fun_prop

/-- Differentiability of `num`. -/
lemma differentiableAt_num (z : ℂ) :
    DifferentiableAt ℂ (fun w => num γ w) z := by
  simp only [num]
  fun_prop

end SlashActionDifferentiableHelpers

/--
Slash action by an element of `SL(2, ℤ)` preserves `MDifferentiable`.
-/
@[fun_prop]
theorem MDifferentiable.slash_SL2 {F : ℍ → ℂ} (hF : MDiff F) (k : ℤ) (γ : SL(2, ℤ)) :
    MDiff (F ∣[k] γ) := by
  intro τ
  let G : ℂ → ℂ := fun z ↦ (F ∘ ofComplex) (num γ z / denom γ z) * (denom γ z) ^ (-k)
  have hdet_pos : (0 : ℝ) < ((γ : GL (Fin 2) ℝ).det).val := by simp
  have hmobius_in_H : (num γ τ / denom γ τ).im > 0 := by
    rw [← UpperHalfPlane.coe_smul_of_det_pos hdet_pos τ]
    exact (γ • τ).im_pos
  have hF_diff : DifferentiableAt ℂ (F ∘ ofComplex) (num γ τ / denom γ τ) := by
    rw [← UpperHalfPlane.coe_smul_of_det_pos hdet_pos τ]
    exact MDifferentiableAt_DifferentiableAt (hF (γ • τ))
  have hmobius_diff : DifferentiableAt ℂ (fun z => num γ z / denom γ z) (τ : ℂ) := by
    exact (differentiableAt_num γ (τ : ℂ)).div
      (differentiableAt_denom γ (τ : ℂ)) (UpperHalfPlane.denom_ne_zero γ τ)
  have hpow_diff : DifferentiableAt ℂ (fun z => (denom γ z) ^ (-k)) (τ : ℂ) := by
    exact DifferentiableAt.zpow (differentiableAt_denom γ (τ : ℂ))
      (Or.inl (UpperHalfPlane.denom_ne_zero γ τ))
  have hG_diff : DifferentiableAt ℂ G (τ : ℂ) := by
    dsimp [G]
    exact (DifferentiableAt.comp (x := (τ : ℂ)) hF_diff hmobius_diff).mul hpow_diff
  have hG_eq : G ∘ UpperHalfPlane.coe = F ∣[k] γ := by
    ext z
    rw [Function.comp_apply, ModularForm.SL_slash_apply (f := F) (k := k) γ z]
    have hmobius_in_H' : (num γ z / denom γ z).im > 0 := by
      rw [← UpperHalfPlane.coe_smul_of_det_pos hdet_pos z]
      exact (γ • z).im_pos
    have hsmul_eq : ofComplex (num γ z / denom γ z) = γ • z := by
      apply UpperHalfPlane.ext
      simpa [ofComplex_apply_of_im_pos hmobius_in_H'] using
        (UpperHalfPlane.coe_smul_of_det_pos hdet_pos z).symm
    simp [G, hsmul_eq]
  simpa [hG_eq] using hG_diff.mdifferentiableAt.comp τ τ.mdifferentiable_coe
