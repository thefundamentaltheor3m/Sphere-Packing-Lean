module
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic

/-!
# Swapping coordinates on `Fin 2`

This file defines the coordinate swap map `swap` on `Fin 2 → α` and packages it as an equivalence
`swap_equiv`.

## Main declarations
* `swap`
* `swap_equiv`
-/

open TopologicalSpace Set Metric Filter Function Complex

public def negEquiv : ℤ ≃ ℤ where
  toFun n := -n
  invFun n := -n
  left_inv := by apply neg_neg
  right_inv := by apply neg_neg

public def succEquiv : ℤ ≃ ℤ where
  toFun n := n.succ
  invFun n := n.pred
  left_inv := by apply Int.pred_succ
  right_inv := by apply Int.succ_pred

/-- Swap the two coordinates of a function `Fin 2 → α`. -/
@[expose] public def swap {α : Type*} : (Fin 2 → α) → (Fin 2 → α) := fun x => ![x 1, x 0]

/-- Unfold `swap` in terms of `![b 1, b 0]`. -/
@[simp]
public lemma swap_apply {α : Type*} (b : Fin 2 → α) : swap b = ![b 1, b 0] := rfl

/-- The map `swap` is an involution. -/
public lemma swap_involutive {α : Type*} (b : Fin 2 → α) : swap (swap b) = b := by
  ext i
  fin_cases i <;> rfl

/-- The equivalence `Fin 2 → α ≃ Fin 2 → α` given by swapping coordinates. -/
@[expose] public def swap_equiv {α : Type*} : (Fin 2 → α) ≃ (Fin 2 → α) :=
  ⟨swap, swap, swap_involutive, swap_involutive⟩
