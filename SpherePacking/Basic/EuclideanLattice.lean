import Mathlib

open Euclidean BigOperators

namespace EuclideanLattice  -- Perhaps this can be moved to a different file...

section Definitions

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

class isLattice (Λ : AddSubgroup V) [DiscreteTopology Λ] extends IsZlattice ℝ Λ

end Definitions

end EuclideanLattice
