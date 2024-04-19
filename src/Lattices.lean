import Mathlib

variables (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
local notation "n" => FiniteDimensional.finrank ℝ V
instance : HMul ℤ V V := { hMul := fun a v => a • v }
instance : SMulWithZero ℤ V := {
  smul := fun a v => a • v,
  smul_zero := fun x => smul_zero ↑x,
  zero_smul := fun v => zero_zsmul v}

open Euclidean BigOperators

namespace Lattice

-- We begin with some boilerplate stuff. We define a lattice as the ℤ-span of some basis of V.

def in_lattice (B : Basis (Fin n) ℝ V) (v : V) : Prop :=
  ∃ (a : Fin n → ℤ), v = ∑ i : (Fin n), ↑(a i) • (B i)

#check in_lattice

@[ext]
structure lattice where
  basis : Basis (Fin n) ℝ V
  vectors : Set V
  hlattice : ∀ v, v ∈ vectors ↔ in_lattice V basis v

#check lattice
#check lattice.ext_iff
#check lattice.mk
#check ↑(lattice.basis)

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
  use fun i => 0
  have : ∑ i : Fin n, (0 : V) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rfl
  rw [← this]
  refine' Finset.sum_congr rfl _
  intro i hi
  rw [zero_smul]

lemma vec_in_lattice {Λ : lattice V} (v : Λ.vectors) : in_lattice V Λ.basis ↑v :=
  (mem_iff V v Λ).1 ((unfold_mem_def V (↑v) Λ).mpr (Subtype.coe_prop v))

lemma closed_under_addition_mem (Λ : lattice V) : ∀ v w, v ∈ Λ → w ∈ Λ → v + w ∈ Λ := by
  intro v w hv hw
  rw [mem_iff] at *
  rcases hv with ⟨a, ha⟩
  rcases hw with ⟨b, hb⟩
  use fun i => a i + b i
  rw [ha, hb]
  simp only [add_smul]
  rw [← Finset.sum_add_distrib]

instance (Λ : lattice V) : HAdd Λ.vectors Λ.vectors V := {
  hAdd := fun v w => v + w
}

lemma closed_under_addition (Λ : lattice V) : ∀ v w : Λ.vectors, ↑v + ↑w ∈ Λ := by
  intro v w
  rcases vec_in_lattice V v with ⟨a, ha⟩
  rcases vec_in_lattice V w with ⟨b, hb⟩
  simp only [mem_iff, in_lattice._eq_1] at *
  use fun i => a i + b i
  simp_rw [add_smul, Finset.sum_add_distrib, ← ha, ← hb]
  rfl


example (Λ : lattice V) : ∀ v : Λ.vectors, ↑v ∈ Λ := fun v => by
  refine (unfold_mem_def V (↑v) Λ).mpr ?_
  simp only [Subtype.coe_prop]

instance (Λ : lattice V) : AddCommGroup Λ.vectors := {
  add := fun v w => ⟨↑v + ↑w, closed_under_addition V Λ v w⟩
  add_assoc := fun v w x => by
    ext
    exact add_assoc _ _ _
  zero := ⟨0, contains_zero V Λ⟩,
  zero_add := fun v => by
    ext
    exact zero_add _
  add_zero := fun v => by
    ext
    exact add_zero _
  neg := fun v => ⟨-v, by
    apply (mem_iff V _ _).2
    rw [in_lattice._eq_1]
    rcases vec_in_lattice V v with ⟨a, ha⟩
    use fun i => -a i
    simp only [neg_smul, Finset.sum_neg_distrib, ← ha] ⟩
  add_left_neg := fun v => by
    ext
    exact add_left_neg _
  add_comm := fun v w => by
    ext
    exact add_comm _ _ }

end Lattice
