import SpherePacking.ForMathlib.PoissonSummation.Zn_Pi

/-! # ℤ-Linear Equivalences of Lattices with `ℤ^n`.

In this file, we prove that there is a ℤ-linear equivalence of any lattice in Euclidean Space with
the standard lattice ℤ^n (as defined in `SpherePacking.ForMathlib.PoissonSummation.Zn_Pi`).
-/

open Submodule

namespace ZLattice

section Equivalence

variable {n : ℕ} (Λ : Submodule ℤ (ℝ^n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

/-- Any lattice in Euclidean space is `ℤ`-linearly equivalent to `↑ℤ^n`. -/
noncomputable def equiv_Zn : Λ ≃ₗ[ℤ] (ℤ^n) := LinearEquiv.ofFinrankEq Λ (ℤ^n) <| by
  rw [ZLattice.rank ℝ Λ, Zn_finrank n]
  exact finrank_euclideanSpace_fin

/-- For any `ZLattice` `Λ` in `ℝ^n`, the `LinearEquiv` from `ℤ^n` to `Λ`. -/
noncomputable def Zn_equiv : (ℤ^n) ≃ₗ[ℤ] Λ := (equiv_Zn Λ).symm

/- The point of the above is that we now have an element of GLₙ(ℤ) using which we can identify any
lattice with ℤ^n, the canonical free ℤ-submodule of the Euclidean space ℝ^n. This includes their
dual lattices, which we have shown to be lattices in
`SpherePacking.ForMathlib.PoissonSummation.DualLattice`. This is a crucial
step in the reduction of the general Poisson Summation Formula to the case where we only deal with
the canonical lattice ℤ^n. -/

end Equivalence

section Covolume

variable {n : ℕ} (Λ : Submodule ℤ (ℝ^n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

-- It'd be nice to show that the covolume of Λ is the determinant of its `Zn_equiv`.

end Covolume
end ZLattice
