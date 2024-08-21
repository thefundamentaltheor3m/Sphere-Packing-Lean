import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

open EisensteinSeries ModularForm UpperHalfPlane CongruenceSubgroup

local notation "G[" k "]" => @eisensteinSeries_MF k 1 (by decide) 0
noncomputable def E₄ : ModularForm (Gamma 1) 4 := (1/2) • G[4]
noncomputable def E₆ : ModularForm (Gamma 1) 6 := (1/2) • G[6]
noncomputable def Δ : ModularForm (Gamma 1) 12 :=
  (1/1728) • ((by exact (E₄.mul E₄).mul E₄) - (by exact E₆.mul E₆))

#check ModularForm.add     -- yay!
#check ModularForm.sub     -- doesn't exist
#check ModularForm.instSub -- just kidding!
#check ModularForm.neg     -- doesn't exist...
#check ModularForm.instNeg -- just kidding!

