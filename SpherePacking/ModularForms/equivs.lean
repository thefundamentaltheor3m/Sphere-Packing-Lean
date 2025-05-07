import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Tactic



open  TopologicalSpace Set
  Metric Filter Function Complex



def negEquiv : ℤ ≃ ℤ where
  toFun n := -n
  invFun n := -n
  left_inv := by apply neg_neg
  right_inv := by apply neg_neg


def succEquiv : ℤ ≃ ℤ where
  toFun n := n.succ
  invFun n := n.pred
  left_inv := by apply Int.pred_succ
  right_inv := by apply Int.succ_pred





def swap {α : Type*} : (Fin 2 → α) → (Fin 2 → α) := fun x => ![x 1, x 0]

@[simp]
lemma swap_apply {α : Type*} (b : Fin 2 → α) : swap b = ![b 1, b 0] := rfl

lemma swap_involutive {α : Type*} (b : Fin 2 → α) : swap (swap b) = b := by
  ext i
  fin_cases i <;> rfl

def swap_equiv {α : Type*} : Equiv (Fin 2 → α) (Fin 2 → α) := Equiv.mk swap swap
  (by rw [Function.LeftInverse]; apply swap_involutive)
  (by rw [Function.RightInverse]; apply swap_involutive)


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
      rw [Nat.mem_divisorsAntidiagonal]; simp; constructor; rfl; constructor;
        linarith [x.1.2]; linarith [x.2.2] ⟩
  left_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    rw [Nat.mem_divisorsAntidiagonal] at h
    simp_rw [mapdiv]
    simp only [h, PNat.mk_coe, eq_self_iff_true, Subtype.coe_eta]
    ext
    simp at *
    simp_rw [h]
    norm_cast
    simp only
    simp only
  right_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    simp_rw [mapdiv]
    exfalso

    simp at *
    simp_rw [mapdiv]
    simp [eq_self_iff_true, Subtype.coe_eta]
    norm_cast
