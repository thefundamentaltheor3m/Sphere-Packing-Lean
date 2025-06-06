import Mathlib

open Euclidean BigOperators

namespace Lattice

section Definitions

variable (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
local notation "n" => FiniteDimensional.finrank ℝ V
instance : HMul ℤ V V := { hMul := fun a v => a • v }
instance : SMulWithZero ℤ V := {
  smul := fun a v => a • v,
  smul_zero := fun x => smul_zero ↑x,
  zero_smul := fun v => zero_zsmul v}

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

end Definitions

section AddCommGroup

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
local notation "n" => FiniteDimensional.finrank ℝ V
instance : HMul ℤ V V := { hMul := fun a v => a • v }
instance : SMulWithZero ℤ V := {
  smul := fun a v => a • v,
  smul_zero := fun x => smul_zero ↑x,
  zero_smul := fun v => zero_zsmul v}

def lattice_of_basis (B : Basis (Fin n) ℝ V) : lattice V :=
  { basis := B,
    vectors := {v | in_lattice V B v},
    hlattice := fun v => Iff.rfl }

def is_lattice (Λ : Set V) : Prop :=
  ∃ (B : Basis (Fin n) ℝ V), Λ = {v | in_lattice V B v}

def mem (v : V) (Λ : lattice V) : Prop :=
  v ∈ Λ.vectors

instance : Membership V (lattice V) := ⟨mem⟩

lemma unfold_mem_def (v : V) (Λ : lattice V) : v ∈ Λ ↔ v ∈ Λ.vectors := Iff.rfl

def mem_iff (v : V) (Λ : lattice V) : v ∈ Λ ↔ in_lattice V Λ.basis v :=
  Λ.hlattice v

def to_subset (Λ : lattice V) : Set V :=
  Λ.vectors

instance : Coe (lattice V) (Set V) := ⟨to_subset⟩

lemma mem_lattice_of_basis (B : Basis (Fin n) ℝ V) (v : V) :
  v ∈ (lattice_of_basis B) ↔ in_lattice V B v :=
  Iff.rfl

lemma self_is_lattice_of_self_basis (Λ : lattice V) : Λ = lattice_of_basis Λ.basis := by
  rw [lattice.ext_iff Λ (lattice_of_basis Λ.basis)]
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
  rw [mem_iff]
  use fun i => 0
  simp only [zero_smul]
  rw [Finset.sum_const_zero]

lemma vec_in_lattice {Λ : lattice V} (v : Λ.vectors) : in_lattice V Λ.basis ↑v :=
  (mem_iff _ _).1 ((unfold_mem_def (↑v) Λ).mpr (Subtype.coe_prop v))

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
  rcases vec_in_lattice v with ⟨a, ha⟩
  rcases vec_in_lattice w with ⟨b, hb⟩
  simp only [mem_iff] at *
  use fun i => a i + b i
  simp_rw [add_smul, Finset.sum_add_distrib, ← ha, ← hb]
  rfl

example (Λ : lattice V) : ∀ v : Λ.vectors, ↑v ∈ Λ := fun v => by
  refine (unfold_mem_def (↑v) Λ).mpr ?_
  simp only [Subtype.coe_prop]

instance (Λ : lattice V) : Zero Λ.vectors where
  zero := ⟨0, contains_zero Λ⟩

instance (Λ : lattice V) : Add Λ.vectors where
  add := fun v w => ⟨↑v + ↑w, closed_under_addition Λ v w⟩

instance (Λ : lattice V) : Neg Λ.vectors where
  neg := fun v => ⟨-v, by
    apply (mem_iff _ _).2
    rcases vec_in_lattice v with ⟨a, ha⟩
    use fun i => -a i
    simp only [neg_smul, Finset.sum_neg_distrib, ← ha] ⟩

instance (Λ : lattice V) : AddCommGroup Λ.vectors where
  add_assoc := fun v w x => by
    ext
    exact add_assoc _ _ _
  zero_add := fun v => by
    ext
    exact zero_add _
  add_zero := fun v => by
    ext
    exact add_zero _
  add_left_neg := fun v => by
    ext
    exact add_left_neg _
  add_comm := fun v w => by
    ext
    exact add_comm _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance (Λ : lattice V) : Module ℤ Λ.vectors := AddCommGroup.intModule ↑Λ.vectors

/- Isomorphism with ℤⁿ -/
-- def toZn (Λ : lattice V) : Λ.vectors → (Fin n → ℤ) := fun v i => sorry

example : FiniteDimensional.finrank ℝ (Module.Dual ℝ V) = n := Subspace.dual_finrank_eq

example (B : Basis (Fin n) ℝ (Module.Dual ℝ V)) :
  Basis (Fin (FiniteDimensional.finrank ℝ (Module.Dual ℝ V))) ℝ (Module.Dual ℝ V) := by
  rw [Subspace.dual_finrank_eq]
  exact B

end AddCommGroup

section Dual

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

noncomputable def basis_of_dual (Λ : lattice V) :
  Basis (Fin (FiniteDimensional.finrank ℝ (Module.Dual ℝ V))) ℝ (Module.Dual ℝ V) := by
  rw [Subspace.dual_finrank_eq]
  exact Basis.dualBasis Λ.basis

noncomputable def dual (Λ : lattice V) : lattice (Module.Dual ℝ V) :=
  { basis := basis_of_dual Λ
    vectors := {v | in_lattice (Module.Dual ℝ V) (basis_of_dual Λ) v}
    hlattice := fun v => Iff.rfl }

-- lemma dual_of_dual (Λ : lattice V) : dual (dual Λ) = Λ := by sorry

end Dual

section Volume

-- variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
--   [TopologicalSpace V] [T2Space V] [TopologicalAddGroup V] [ContinuousSMul ℝ V]
-- local notation "n" => FiniteDimensional.finrank ℝ V

-- noncomputable def Eucl : EuclideanSpace ℝ (Fin n) := toEuclidean V
-- example : V ≃L[ℝ] (Fin n → ℝ) := by library_search

variable {n : ℕ}
local notation "V" => Fin n → ℝ

example : FiniteDimensional.finrank ℝ V = n := by rw [FiniteDimensional.finrank_fintype_fun_eq_card,
  Fintype.card_fin]

variable (Λ : lattice V)

noncomputable def volume (Λ : lattice V) : ℝ := abs (Matrix.det (
  Basis.toMatrix (Pi.basisFun ℝ (Fin n)) fun i j => (Λ.basis ⟨i, by
    rw [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact i.2⟩) j ))

end Volume

section E8

local notation "V" => Fin 8 → ℝ

def is_integer (x : ℝ) : Prop := ∃ (n : ℤ), x = ↑n

def vec_to_V (v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ : ℝ) : V := fun i => match i with
  | ⟨0, _⟩ => v₀
  | ⟨1, _⟩ => v₁
  | ⟨2, _⟩ => v₂
  | ⟨3, _⟩ => v₃
  | ⟨4, _⟩ => v₄
  | ⟨5, _⟩ => v₅
  | ⟨6, _⟩ => v₆
  | ⟨7, _⟩ => v₇

def E8_Basis_Vecs : Fin 8 → V := fun i => match i with
  | ⟨0, _⟩ => vec_to_V 2 (-1) 0 0 0 0 0 0.5
  | ⟨1, _⟩ => vec_to_V 0 1 (-1) 0 0 0 0 0.5
  | ⟨2, _⟩ => vec_to_V 0 0 1 (-1) 0 0 0 0.5
  | ⟨3, _⟩ => vec_to_V 0 0 0 1 (-1) 0 0 0.5
  | ⟨4, _⟩ => vec_to_V 0 0 0 0 1 (-1) 0 0.5
  | ⟨5, _⟩ => vec_to_V 0 0 0 0 0 1 (-1) 0.5
  | ⟨6, _⟩ => vec_to_V 0 0 0 0 0 0 1 0.5
  | ⟨7, _⟩ => vec_to_V 0 0 0 0 0 0 0 0.5

-- def E8_Basis : Basis (Fin 8) ℝ V := Basis.mk ⟨E8_Basis_Vecs⟩

def E8 : lattice V where
  basis := sorry
  vectors := {v : V | ((∀ i : Fin 8, is_integer (v i)) ∨
    (∀ i : Fin 8, is_integer (2 * v i) ∧ ¬ is_integer (v i))) ∧ ∑ i : Fin 8, v i = 0}
  hlattice := sorry

end E8

end Lattice


-- instance (G : Type u_1) {α : Type u_2}  [Zero G]  [VAdd G α]  [MeasurableSpace α] (s : Set α)  (μ : autoParam (MeasureTheory.Measure α) _)
--   (M : MeasureTheory.IsAddFundamentalDomain) : AddCommGroup M := by
--   sorry
