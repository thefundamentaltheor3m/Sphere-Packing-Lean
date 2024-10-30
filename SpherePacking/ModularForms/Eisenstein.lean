/-
The purpose of this file is to define the Eisenstein series we are interested in using more convenient notation.
-/

import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
-- import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs

open EisensteinSeries ModularForm

def standardcongruencecondition : Fin 2 → ZMod ((1 : ℕ+) : ℕ) := 0

private lemma aux4 : (3 : ℤ) ≤ 4 := Int.le.intro_sub (4 - Nat.succ 2) rfl
private lemma aux6 : (3 : ℤ) ≤ 6 := Int.le.intro_sub (6 - Nat.succ 2) rfl

noncomputable def E₂ := eisensteinSeries_SIF standardcongruencecondition 2
noncomputable def E₄ := eisensteinSeries_MF (aux4) standardcongruencecondition
noncomputable def E₆ := eisensteinSeries_MF (aux6) standardcongruencecondition

-- Need to try and get holomorphicity conditions too
