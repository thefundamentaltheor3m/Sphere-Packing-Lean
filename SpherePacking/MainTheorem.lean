module

public import SpherePacking.Basic.E8

/-!
# The Sphere Packing Problem in Dimension 8

Statement of the main theorem: `E₈` realises the optimal sphere packing density in dimension `8`.
-/

@[expose] public section

open SpherePacking E8

theorem SpherePacking.MainTheorem : SpherePackingConstant 8 = E8Packing.density :=
  sorry
