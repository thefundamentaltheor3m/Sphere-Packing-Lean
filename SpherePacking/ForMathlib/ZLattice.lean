import Mathlib.Algebra.Module.ZLattice.Basic

open ZSpan Module

variable {E ι K : Type*} [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [NormedAddCommGroup E] [NormedSpace K E]
  (b : Basis ι K E) [FloorRing K] [Fintype ι] (m : E)

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

theorem ZSpan.floor_eq_zero (v : E) : v ∈ fundamentalDomain b ↔ floor b v = 0 := by
  simp_rw [mem_fundamentalDomain, ← Int.floor_eq_zero_iff]
  constructor <;> intro h
  · simp_rw [floor, h, zero_smul, Finset.sum_const, smul_zero]
  · intro i
    have := repr_floor_apply b v i
    rw [h, ZeroMemClass.coe_zero, map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
    exact_mod_cast this.symm
