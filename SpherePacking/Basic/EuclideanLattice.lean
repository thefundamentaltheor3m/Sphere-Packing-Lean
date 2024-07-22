import Mathlib

open Euclidean BigOperators

namespace EuclideanLattice  -- Perhaps this can be moved to a different file...

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

class isLattice (Λ : AddSubgroup V) [DiscreteTopology Λ] extends IsZlattice ℝ Λ

section Action

/-!
# The Lattice Action

We need to define an action of a lattice on a set of lattice-periodic points in Euclidean space.
This will allow us to formalise the theorem for the density of a periodic packing.
-/

end Action

end EuclideanLattice
