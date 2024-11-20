import Mathlib.NumberTheory.ModularForms.SlashActions

-- Maybe this belongs in NumberTheory/ModularForms/SlashActions.lean, next to ModularForm.mul_slash

local notation "GL(" n ", " R ")" "⁺" => @Matrix.GLPos (Fin n) R (instDecidableEqFin n)
  (Fin.fintype n) Real.linearOrderedCommRing

open ModularForm MatrixGroups UpperHalfPlane

/- Looks like the way to fix the errors is to replace each GL(2, ℝ)⁺ with
  `@Matrix.GLPos (Fin 2) ℝ (instDecidableEqFin 2) (Fin.fintype 2) Real.linearOrderedCommRing :
  Subgroup (GL (Fin 2) ℝ)`... but it's just so ugly!
-/

/-- Slash action under -I₂ as a GL(2, ℝ)⁺ matrix. See `ModularForm.slash_neg_one'` for the SL(2, ℤ)
version. -/
theorem ModularForm.slash_neg_one {k : ℤ} (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-1 : GL(2, ℝ)⁺) = f ∣[k] (1 : GL(2, ℝ)⁺) := by
  ext x
  simp [slash_def, slash, denom, hk.neg_one_zpow, Matrix.det_neg]

/-- Slash action under -I₂ as a SL(2, ℤ) matrix. See `ModularForm.slash_neg_one` for the GL(2, ℝ)⁺
version. -/
theorem ModularForm.slash_neg_one' {k : ℤ} (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-1 : SL(2, ℤ)) = f ∣[k] (1 : SL(2, ℤ)) := by
  ext x
  have : ((-1 : SL(2, ℤ)) : GL(2, ℝ)⁺) • x = x := by ext; simp [num, denom]
  simp [slash_def, slash, denom, hk.neg_one_zpow, this]

/-- See `ModularForm.slash_neg'` for the version where `g` is a SL(2, ℤ) matrix. -/
theorem ModularForm.slash_neg {k : ℤ} (g : GL(2, ℝ)⁺) (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-g) = f ∣[k] g := by
  rw [← neg_one_mul, SlashAction.slash_mul, slash_neg_one f hk, SlashAction.slash_one]

/-- See `ModularForm.slash_neg` for the version where `g` is a GL(2, ℝ)⁺ matrix. -/
theorem ModularForm.slash_neg' {k : ℤ} (g : SL(2, ℤ)) (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-g) = f ∣[k] g := by
  rw [SL_slash, ← slash_neg _ _ hk]
  congr
  ext
  simp [ModularGroup.coe']
