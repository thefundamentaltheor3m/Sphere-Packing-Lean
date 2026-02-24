module
public import Mathlib.Algebra.Module.ZLattice.Basic


/-!
# Z-lattices

This file proves results such as `ZSpan.ceil_sub_mem_fundamentalDomain`, `ZSpan.floor_eq_zero`.
-/

open ZSpan

variable {E ι K : Type*} [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [NormedAddCommGroup E] [NormedSpace K E] (b : Module.Basis ι K E) [FloorRing K] [Fintype ι]

/-- `ceil b v - v` belongs to the fundamental domain associated to `b`. -/
theorem ZSpan.ceil_sub_mem_fundamentalDomain (v : E) : ceil b v - v ∈ fundamentalDomain b := by
  rw [mem_fundamentalDomain]
  intro i
  simp_rw [map_sub, Finsupp.coe_sub, Pi.sub_apply, repr_ceil_apply, Set.mem_Ico, sub_nonneg]
  constructor
  · exact Int.le_ceil _
  · by_cases hv : Int.fract (b.repr v i) = 0
    · rcases (Int.fract_eq_zero_iff (a := b.repr v i)).1 hv with ⟨z, hz⟩
      simp [hz.symm]
    · rw [Int.ceil_sub_self_eq hv, sub_lt_self_iff]
      exact lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hv)

/-- A point is in the fundamental domain iff its `floor` vector is zero. -/
public theorem ZSpan.floor_eq_zero (v : E) : v ∈ fundamentalDomain b ↔ floor b v = 0 := by
  simp_rw [mem_fundamentalDomain, ← Int.floor_eq_zero_iff]
  constructor <;> intro h
  · simp [floor, h]
  · intro i
    exact_mod_cast (by simpa [h] using (repr_floor_apply b v i).symm)

section BasisIndexEquiv

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

namespace ZLattice

/--
Reindex the chosen `ℤ`-basis of a full-rank lattice in `ℝ^d` by `Fin d`.

This is useful for building `Basis (Fin d) ℤ Λ` via `.reindex` without carrying around an
abstract basis-index type.
-/
public noncomputable def basis_index_equiv (Λ : Submodule ℤ E)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    (Module.Free.ChooseBasisIndex ℤ Λ) ≃ (Fin d) := by
  refine Fintype.equivFinOfCardEq ?_
  rw [← Module.finrank_eq_card_chooseBasisIndex (R := ℤ) (M := Λ),
    ZLattice.rank (K := ℝ) (L := Λ),
    finrank_euclideanSpace, Fintype.card_fin]

end ZLattice

end BasisIndexEquiv
