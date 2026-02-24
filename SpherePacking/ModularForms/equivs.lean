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

def mapdiv (n : ℕ+) : Nat.divisorsAntidiagonal n → ℕ+ × ℕ+ :=
  by
  intro x
  have h11 := Nat.fst_mem_divisors_of_mem_antidiagonal x.2
  have h111 := Nat.pos_of_mem_divisors h11
  have h22 := Nat.snd_mem_divisors_of_mem_antidiagonal x.2
  have h222 := Nat.pos_of_mem_divisors h22
  set n1 : ℕ+ := ⟨x.1.1, h111⟩
  set n2 : ℕ+ := ⟨x.1.2, h222⟩
  use n1
  use n2
  exact h222

def sigmaAntidiagonalEquivProd : (Σ n : ℕ+, Nat.divisorsAntidiagonal n) ≃ ℕ+ × ℕ+
    where
  toFun x := mapdiv x.1 x.2
  invFun x :=
    ⟨⟨x.1.1 * x.2.1, by apply mul_pos x.1.2 x.2.2⟩, ⟨x.1, x.2⟩, by
      rw [Nat.mem_divisorsAntidiagonal]
      simp
      refine ⟨rfl, ?_, ?_⟩
      · linarith [x.1.2]
      · linarith [x.2.2]⟩
  left_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    rw [Nat.mem_divisorsAntidiagonal] at h
    simp_rw [mapdiv]
    simp only [PNat.mk_coe]
    ext
    · simp at *
      simp_rw [h]
      norm_cast
    · simp only
    simp only
  right_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    · simp_rw [mapdiv]
      exfalso
      simp at *
    simp_rw [mapdiv]
    norm_cast
