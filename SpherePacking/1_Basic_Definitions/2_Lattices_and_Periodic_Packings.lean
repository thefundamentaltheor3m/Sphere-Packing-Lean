import Mathlib

open Euclidean BigOperators

namespace Lattice

section Definitions

variable {n : ℕ} (V : EuclideanSpace (Fin n) ℝ)

-- def in_lattice (B : Basis (Fin n) ℝ V) (v : V) : Prop :=
--   ∃ (a : Fin n → ℤ), v = ∑ i : (Fin n), ↑(a i) • (B i)

end Definitions

end Lattice
