import Mathlib.LinearAlgebra.Finsupp

theorem Finsupp.total_eq_sum {α β ι : Type*} [Fintype ι] [AddCommMonoid α] [Semiring β] [Module β α]
    (v : ι → α) (y : ι →₀ β) : Finsupp.total ι α β v y = ∑ j, y j • v j :=
  Finsupp.sum_fintype _ _ (by simp)

