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

instance : SMul ℝ V := ⟨fun (r : ℝ) (v : V) => (fun i => r * v i)⟩

instance : HMul ℝ V V := ⟨fun (r : ℝ) (v : V) => (fun i => r * v i)⟩

def ℤ_as_ℝ : Set ℝ := {r : ℝ | ∃ (n : ℤ), ↑n = r}
local notation "↑ℤ" => ℤ_as_ℝ

def E8 : Set V := {v : V | ((∀ i : Fin 8, v i ∈ ↑ℤ) ∨ (∀ i : Fin 8, (2 * v i) ∈ ↑ℤ ∧ (v i ∉ ↑ℤ))) ∧ ∑ i : Fin 8, v i = 0}

def E8_normalised : Set V := {v : V | ∃ w ∈ E8, v = ((1 : ℝ) / (Real.sqrt 2)) * w}

end E8

end EuclideanLattice
