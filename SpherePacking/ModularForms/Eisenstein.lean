/-
The purpose of this file is to define the Eisenstein series we are interested in using more
convenient notation. We will also state results with `sorry`s that should be proved and eventually
moved elsewhere in the project.
-/

import Mathlib
-- import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs

open EisensteinSeries ModularForm Complex Real
open scoped UpperHalfPlane

noncomputable section Definitions

def standardcongruencecondition : Fin 2 → ZMod ((1 : ℕ+) : ℕ) := 0

-- private lemma aux4 : (3 : ℤ) ≤ 4 := by norm_num
-- private lemma aux6 : (3 : ℤ) ≤ 6 := by norm_num

/- The Eisenstein Series E₂, E₄ and E₆ -/
def E₂ : ℍ → ℂ := sorry -- eisensteinSeries_SIF standardcongruencecondition 2
def E₄ : ModularForm (CongruenceSubgroup.Gamma ↑1) 4 :=
  eisensteinSeries_MF (by norm_num) standardcongruencecondition
def E₆ : ModularForm (CongruenceSubgroup.Gamma ↑1) 6 :=
  eisensteinSeries_MF (by norm_num) standardcongruencecondition

lemma E₂_eq (z : UpperHalfPlane) : E₂ z =
    1 - 24 * ∑' (n : ℕ+), ↑n * cexp (2 * π * I * n * z) / (1 - cexp (2 * π * I * n * z)) := sorry

/- The discriminant form -/
def Δ (z : UpperHalfPlane) := ((E₄ z) ^ 3 - (E₆ z) ^ 2) / 1728

#check Δ

/- φ₀, φ₋₂ and φ₋₄, except we can't use - signs in subscripts for definitions... -/
def φ₀ (z : ℍ) := (((E₂ z) * (E₄ z) - (E₆ z)) ^ 2) / (Δ z)
def φ₂' (z : ℍ) := (E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) / (Δ z)
def φ₄' (z : ℍ) := ((E₄ z) ^ 2) / (Δ z)
/- We extend these definitions to ℂ for convenience. -/
def φ₀'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₀ ⟨z, hz⟩ else 0
def φ₂'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₂' ⟨z, hz⟩ else 0
def φ₄'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₄' ⟨z, hz⟩ else 0

end Definitions

noncomputable section Holomorphicity

-- Try and get the desired holomorphicity results for φ₀, φ₂ and φ₄ in terms of the Eᵢ

end Holomorphicity

noncomputable section Integrability

-- Here, we show that

end Integrability

open Complex Real

section Product_Formula

lemma MultipliableDiscriminantProductExpansion : Multipliable (fun (z : ℍ) =>
  cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24) := sorry

theorem DiscriminantProductFormula (z : ℍ) : Δ z = cexp (2 * π * I * z) * ∏' (n : ℕ+),
  (1 - cexp (2 * π * I * n * z)) ^ 24 := sorry

end Product_Formula

open ArithmeticFunction

section Ramanujan_Formula

-- In this section, we state some simplifications that are used in Cor 7.5-7.7 of the blueprint

theorem E₂_mul_E₄_sub_E₆ (z : ℍ) :
    (E₂ z) * (E₄ z) - (E₆ z) = 720 * ∑' (n : ℕ+), n * (σ 3 n) * cexp (2 * π * I * n * z) := by
  sorry

end Ramanujan_Formula

#min_imports
