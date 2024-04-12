import Mathlib

variables {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

open Euclidean BigOperators

def in_lattice (B : Basis (Fin (FiniteDimensional.finrank ℝ V)) ℝ V) (v : V) : Prop := sorry
  -- ∃ (a : Fin n → ℤ), v = ∑ i : (Fin n), ↑(a i) * (B i)

@[ext]
structure lattice where
  basis : Basis (Fin n) ℝ V
  vectors : Set V
  hlattice : ∀ v, v ∈ vectors ↔ in_lattice basis v
