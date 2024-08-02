import SpherePacking.Basic.SpherePacking
import SpherePacking.Basic.E8

/- In this file, we establish results about density of periodic packings. This roughly corresponds
to Section 2.2, "Bounds on Finite Density of Periodic Packing". -/

open SpherePacking EuclideanSpace MeasureTheory

variable {d : ℕ} (S : PeriodicSpherePacking d)

#check S.lattice_basis
#check parallelepiped
#check Zspan.fundamentalDomain

#check Zspan.fundamentalDomain_ae_parallelepiped
#check Zspan.volume_fundamentalDomain
#check measure_congr

example {ι : Type*} [Fintype ι] [DecidableEq ι] (b b' : Basis ι ℝ (ι → ℝ)) :
    volume (Zspan.fundamentalDomain b) = volume (Zspan.fundamentalDomain b') := by
  sorry

lemma aux : Finite (S.centers ∩ S.lattice_basis.fundamentalDomain) := by
  sorry

-- We want to define X / Λ
instance : Finite (Quotient S.addAction.orbitRel) := by
  sorry
