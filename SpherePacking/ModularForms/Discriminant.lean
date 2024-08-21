import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

open EisensteinSeries ModularForm UpperHalfPlane CongruenceSubgroup

/-!
# Discriminant form.

Define the discriminant form `Δ` as a modular form of weight 12; `Δ = (E₄^3 - E₆^2)/1728`, where `E₄` and `E₆` are normalized Eisenstein series, whose constant terms are 1.

Prove that `Δ` is a cusp form of weight 12, and its q-expansion satisfies the product formula
`Δ = q ∏_{n ≥ 1} (1 - q^n)^24`.
-/

local notation "E[" k "]" => @eisensteinSeries_MF k 1 (by decide) 0
noncomputable def E₄ : ModularForm (Gamma 1) 4 := (1/2) • E[4]
noncomputable def E₆ : ModularForm (Gamma 1) 6 := (1/2) • E[6]
noncomputable def Δ : ModularForm (Gamma 1) 12 :=
  (1/1728) • ((by exact (E₄.mul E₄).mul E₄) - (by exact E₆.mul E₆))

#check ModularForm.add     -- yay!
-- #check ModularForm.sub     -- doesn't exist
#check ModularForm.instSub -- just kidding!
-- #check ModularForm.neg     -- doesn't exist...
#check ModularForm.instNeg -- just kidding!

variable (γ : SL(2, ℤ))

theorem isZeroAtImInfty_Δ : IsZeroAtImInfty Δ.toFun := by sorry
theorem isZeroAtImInfty_Δ_slash : IsZeroAtImInfty (Δ.toFun ∣[(12 : ℤ)] γ) := by
  -- rw [Δ.slash_action_eq']? something like that
  sorry

noncomputable def Δ_CF: CuspForm (Gamma 1) 12 := {
  Δ with
  zero_at_infty' := isZeroAtImInfty_Δ_slash
}
