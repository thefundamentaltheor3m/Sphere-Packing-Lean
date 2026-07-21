module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finitely Supported Functions

Auxiliary lemmas about `Finsupp` and linear combinations.
-/

@[expose] public section

theorem Finsupp.linearCombination_eq_sum {α β ι : Type*} [Fintype ι] [AddCommMonoid α] [Semiring β]
  [Module β α]
    (v : ι → α) (y : ι →₀ β) : Finsupp.linearCombination β v y = ∑ j, y j • v j :=
  Finsupp.sum_fintype _ _ (by simp)
