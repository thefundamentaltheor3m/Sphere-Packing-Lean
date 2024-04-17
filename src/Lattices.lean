import Mathlib

variables (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
local notation "n" => FiniteDimensional.finrank ℝ V
instance : HMul ℤ V V := { hMul := fun a v => a • v }

open Euclidean BigOperators

namespace Lattice

-- We begin with some boilerplate stuff. We define a lattice as the ℤ-span of some basis of V.

def in_lattice (B : Basis (Fin n) ℝ V) (v : V) : Prop :=
  ∃ (a : Fin n → ℤ), v = ∑ i : (Fin n), ↑(a i) * (B i)

@[ext]
structure lattice where
  basis : Basis (Fin n) ℝ V
  vectors : Set V
  hlattice : ∀ v, v ∈ vectors ↔ in_lattice V basis v

#check lattice
#check lattice.ext_iff
#check lattice.mk

def lattice_of_basis (B : Basis (Fin n) ℝ V) : lattice V :=
  { basis := B,
    vectors := {v | in_lattice V B v},
    hlattice := fun v => Iff.rfl }

def is_lattice (Λ : Set V) : Prop :=
  ∃ (B : Basis (Fin n) ℝ V), Λ = {v | in_lattice V B v}

def mem (v : V) (Λ : lattice V) : Prop :=
  v ∈ Λ.vectors

instance : Membership V (lattice V) := ⟨mem V⟩

lemma unfold_mem_def (v : V) (Λ : lattice V) : v ∈ Λ ↔ v ∈ Λ.vectors := Iff.rfl

def mem_iff (v : V) (Λ : lattice V) : v ∈ Λ ↔ in_lattice V Λ.basis v :=
  Λ.hlattice v

def to_subset (Λ : lattice V) : Set V :=
  Λ.vectors

instance : Coe (lattice V) (Set V) := ⟨to_subset V⟩

lemma mem_lattice_of_basis (B : Basis (Fin n) ℝ V) (v : V) :
  v ∈ (lattice_of_basis V B) ↔ in_lattice V B v :=
  Iff.rfl

lemma self_is_lattice_of_self_basis (Λ : lattice V) : Λ = lattice_of_basis V Λ.basis := by
    rw [lattice.ext_iff Λ (lattice_of_basis V Λ.basis)]
    constructor
    { rw [lattice.basis, lattice_of_basis] }
    { simp [lattice.vectors, lattice_of_basis]
      ext v
      constructor
      { intro h
        rw [← unfold_mem_def, mem_iff] at h
        exact h }
      { intro h
        rw [← unfold_mem_def, mem_iff]
        exact h } }

lemma contains_zero (Λ : lattice V) : (0 : V) ∈ Λ := by
  rw [mem_iff, in_lattice]
  use λ i => 0
  sorry

-- instance : AddCommMonoid V := {
--   add := fun v w => v + w,
--   add_assoc := fun v w x => add_assoc v w x,
--   zero := 0,
--   zero_add := fun v => zero_add v,
--   add_zero := fun v => add_zero v,
--   add_comm := fun v w => add_comm v w}

end Lattice
