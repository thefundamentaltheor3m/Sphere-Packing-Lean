import Mathlib

open Euclidean BigOperators

namespace EuclideanLattice

section Definitions

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

def in_lattice (B : Basis (Fin d) ℝ V) (v : V) : Prop :=
  ∃ (a : Fin d → ℤ), v = ∑ i : (Fin d), ↑(a i) • (B i)

def is_lattice (Λ : Set V) : Prop := ∃ (B : Basis (Fin d) ℝ V), ∀ v : V, v ∈ Λ ↔ in_lattice B v

end Definitions

section E8

local notation "V" => EuclideanSpace ℝ (Fin 8)

def E8 : Set V := sorry

end E8

end EuclideanLattice
