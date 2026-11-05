module

public import SpherePacking.Basic.E8

/-!
# The Sphere Packing Problem in Dimension 8

Statement of the main theorem: `E₈` realises the optimal sphere packing density in dimension `8`.

The main theorem `SpherePacking.MainTheorem` is the conjunction of two inequalities:

* `E8Packing_density_le_constant`: `E8Packing` is a sphere packing, so its density is at most the
  sphere packing constant;
* `SpherePacking.density_le_E8Packing_density`: every packing in dimension `8` has density at most
  that of `E₈`. By `periodic_constant_eq_constant`, this reduces to the periodic case
  `PeriodicSpherePacking.density_le_E8Packing_density`, which is where the Cohn–Elkies bound
  `LinearProgrammingBound` and the magic function `g` enter.
-/

@[expose] public section

open SpherePacking E8

/-- The `E₈` packing is a sphere packing in dimension `8`, hence its density is bounded by the
sphere packing constant (the supremum over all packings). Blueprint: first half of the proof of
`MainTheorem`. -/
theorem E8Packing_density_le_constant : E8Packing.density ≤ SpherePackingConstant 8 := by
  sorry

/-- Every *periodic* sphere packing in dimension `8` has density at most that of `E₈`. This is the
Cohn–Elkies bound `LinearProgrammingBound'` applied to the magic function `x ↦ g (x / √2)`.
Blueprint `theorem:CE_Main`. -/
theorem PeriodicSpherePacking.density_le_E8Packing_density (P : PeriodicSpherePacking 8) :
    P.density ≤ E8Packing.density := by
  sorry

/-- Every sphere packing in dimension `8` has density at most that of `E₈`. This follows from the
periodic case `PeriodicSpherePacking.density_le_E8Packing_density` via
`periodic_constant_eq_constant`. Blueprint `corollary:upper-bound-E8`. -/
theorem SpherePacking.density_le_E8Packing_density (P : SpherePacking 8) :
    P.density ≤ E8Packing.density := by
  sorry

/-- **The sphere packing problem in dimension 8**: the sphere packing constant in dimension `8` is
the density of the `E₈` packing. This is `le_antisymm` of
`SpherePacking.density_le_E8Packing_density` (taking the supremum over all packings) and
`E8Packing_density_le_constant`. Blueprint `MainTheorem`. -/
theorem SpherePacking.MainTheorem : SpherePackingConstant 8 = E8Packing.density := by
  sorry
