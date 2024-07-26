import Mathlib.Data.Fin.VecNotation

variable {m : ℕ} {α : Type*}

namespace Matrix

-- TODO: Decide whether we want this in Mathlib (Data/Fin/VecNotation)

@[simp]
theorem cons_val_five (x : α) (u : Fin m.succ.succ.succ.succ.succ → α) :
    vecCons x u 5 = vecHead (vecTail (vecTail (vecTail (vecTail u)))) :=
  rfl

@[simp]
theorem cons_val_six (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 6 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail u))))) :=
  rfl

@[simp]
theorem cons_val_seven (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 7 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u)))))) :=
  rfl
