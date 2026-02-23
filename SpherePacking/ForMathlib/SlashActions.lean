module
public import Mathlib.NumberTheory.ModularForms.SlashActions


/-!
# Slash actions

This file proves results such as `ModularForm.slash_neg_one`, `ModularForm.slash_neg`.
-/

open ModularForm UpperHalfPlane
open scoped MatrixGroups

/-- Slash action by `-1` agrees with slash action by `1` for even weight.

This is the version for the `GL (Fin 2) ℝ` slash action.
-/
@[simp] public theorem ModularForm.slash_neg_one {k : ℤ} (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-1 : GL (Fin 2) ℝ) =
    f ∣[k] (1 : GL (Fin 2) ℝ) := by
  simp [slash_def, denom, hk.neg_one_zpow, Matrix.det_neg, σ]

/-- Slash action by `-1` agrees with slash action by `1` for even weight.

The prime indicates this is the `SL(2, ℤ)` version.
-/
@[simp] public theorem ModularForm.slash_neg_one' {k : ℤ} (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-1 : SL(2, ℤ)) = f ∣[k] (1 : SL(2, ℤ)) := by
  simp [SL_slash_def, denom, hk.neg_one_zpow]

/-- Negating a matrix does not change the slash action for even weight (`GL (Fin 2) ℝ` version). -/
@[simp] public theorem ModularForm.slash_neg {k : ℤ} (g : GL (Fin 2) ℝ) (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-g) = f ∣[k] g := by
  rw [← neg_one_mul, SlashAction.slash_mul, slash_neg_one f hk, SlashAction.slash_one]

/-- Negating a matrix does not change the slash action for even weight (`SL(2, ℤ)` version).

The prime indicates this is the `SL(2, ℤ)` version.
-/
@[simp] public theorem ModularForm.slash_neg' {k : ℤ} (g : SL(2, ℤ)) (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-g) = f ∣[k] g := by
  simpa [SL_slash] using (ModularForm.slash_neg (k := k) (g := (g : GL (Fin 2) ℝ)) f hk)
