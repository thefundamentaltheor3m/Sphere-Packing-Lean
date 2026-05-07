module
public import SpherePacking.E8.Packing
import SpherePacking.UpperBound

/-!
# Main theorem in dimension 8

We prove that the optimal sphere packing density in `R^8` is achieved by the `E8` lattice packing:
`SpherePackingConstant 8 = E8Packing.density`.

This file packages the final equality by combining the upper bound from
`SpherePacking.UpperBound` with the lower bound coming from the definition of
`SpherePackingConstant`.
-/

namespace SpherePacking

open SpherePacking E8

/-- Main theorem (dimension 8): the optimal packing density equals `E8Packing.density`. -/
public theorem MainTheorem : SpherePackingConstant 8 = E8Packing.density :=
  le_antisymm SpherePackingConstant_le_E8Packing_density <| by
    simpa [SpherePackingConstant] using
      le_iSup (fun S : SpherePacking 8 => S.density) E8Packing.toSpherePacking

end SpherePacking
