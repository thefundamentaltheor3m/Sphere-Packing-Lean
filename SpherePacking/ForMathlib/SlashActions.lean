module

public import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# Slash Actions

Auxiliary lemmas about slash actions of the modular group.

Mathlib's `ModularForm.slash_neg_one` and `ModularForm.slash_neg` are the `GL (Fin 2) ℝ` versions
of the lemmas below, valid in every weight (with a factor `(-1) ^ k`).
-/

@[expose] public section

open ModularForm MatrixGroups UpperHalfPlane

/-- Slash action under `-1 : SL(2, ℤ)` in even weight. -/
theorem ModularForm.slash_neg_one' {k : ℤ} (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-1 : SL(2, ℤ)) = f ∣[k] (1 : SL(2, ℤ)) := by
  simp [SL_slash_def, denom, hk.neg_one_zpow]

/-- Slash action under `-g` for `g : SL(2, ℤ)` in even weight. -/
theorem ModularForm.slash_neg' {k : ℤ} (g : SL(2, ℤ)) (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-g) = f ∣[k] g := by
  rw [SL_slash, SL_slash, show ((-g : SL(2, ℤ)) : GL (Fin 2) ℝ) = -(g : GL (Fin 2) ℝ) by
    ext; simp, slash_neg, hk.neg_one_zpow, one_mul]
