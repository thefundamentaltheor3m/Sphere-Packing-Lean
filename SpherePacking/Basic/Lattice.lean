import Mathlib

open Euclidean BigOperators

namespace Lattice

section Definitions

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

def in_lattice (B : Basis (Fin d) ℝ V) (v : V) : Prop :=
  ∃ (a : Fin d → ℤ), v = ∑ i : (Fin d), ↑(a i) • (B i)

def is_lattice (Λ : Set V) : Prop := ∃ (B : Basis (Fin d) ℝ V), ∀ v : V, v ∈ Λ ↔ in_lattice B v

end Definitions

end Lattice
