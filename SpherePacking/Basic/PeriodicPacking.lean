import SpherePacking.Basic.SpherePacking
import SpherePacking.Basic.E8

/- In this file, we establish results about density of periodic packings. This roughly corresponds
to Section 2.2, "Bounds on Finite Density of Periodic Packing". -/

open SpherePacking EuclideanSpace MeasureTheory

variable {d : ℕ} (S : PeriodicSpherePacking d)

#check E8.E8_Set
#check E8.E8_Lattice
#check E8.E8_Basis
#check Basis.ofZlatticeBasis
#check Zspan.fundamentalDomain
#check Zspan.fundamentalDomain_isBounded
example : Submodule.span ℤ (Set.range E8.E8_Basis) = Submodule.span ℤ (Set.range E8.E8_Matrix) := by
  congr
  simp only [E8.E8_Basis, Basis.coe_mk]

lemma aux : Finite (S.centers ∩ S.

-- We want to define X / Λ
instance : Finite (Quotient S.addAction.orbitRel) := by
  sorry
