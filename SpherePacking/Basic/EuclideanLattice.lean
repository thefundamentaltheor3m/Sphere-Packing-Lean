/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
import Mathlib

open Euclidean BigOperators

namespace EuclideanLattice  -- Perhaps this can be moved to a different file...

section Definitions

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

class isLattice (Λ : AddSubgroup V) [DiscreteTopology Λ] extends IsZlattice ℝ Λ

end Definitions

end EuclideanLattice
