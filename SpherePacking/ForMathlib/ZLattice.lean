module
public import Mathlib.Algebra.Module.ZLattice.Basic


/-!
# Z-lattices

This file proves results such as `ZSpan.ceil_sub_mem_fundamentalDomain`, `ZSpan.floor_eq_zero`.
-/

open ZSpan

variable {E ι K : Type*} [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [NormedAddCommGroup E] [NormedSpace K E] (b : Module.Basis ι K E) [FloorRing K] [Fintype ι]

theorem ZSpan.ceil_sub_mem_fundamentalDomain (v) : ceil b v - v ∈ fundamentalDomain b := by
  rw [mem_fundamentalDomain]
  intro i
  simp_rw [map_sub, Finsupp.coe_sub, Pi.sub_apply, repr_ceil_apply, Set.mem_Ico, sub_nonneg]
  constructor
  · exact Int.le_ceil _
  · by_cases hv : Int.fract (b.repr v i) ≠ 0
    · rw [Int.ceil_sub_self_eq hv, sub_lt_self_iff]
      exact lt_of_le_of_ne (Int.fract_nonneg _) hv.symm
    · rw [ne_eq, Decidable.not_not, Int.fract, sub_eq_zero] at hv
      have : ⌈(b.repr v) i⌉ = (b.repr v) i := by
        have := congrArg (fun x ↦ (⌈x⌉ : K)) hv
        simp_rw [Int.ceil_intCast, ← hv] at this
        exact this
      rw [this, sub_self]
      exact zero_lt_one

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
