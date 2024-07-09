import Mathlib

open Euclidean BigOperators

namespace EuclideanLattice

section Definitions

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

def inLattice (B : Basis (Fin d) ℝ V) (v : V) : Prop :=
  ∃ (a : Fin d → ℤ), v = ∑ i : (Fin d), ↑(a i) • (B i)

def isLattice (Λ : Set V) : Prop := ∃ (B : Basis (Fin d) ℝ V), ∀ v : V, v ∈ Λ ↔ inLattice B v

def isPeriodic (Λ : Set V) -- (hΛ : isLattice Λ)
  (X : Set V) : Prop := ∀ v x : V, v ∈ Λ → x ∈ X → v + x ∈ Λ

end Definitions

section ActionbyTranslation

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)
variable {X Λ : Set V} (hΛ : isLattice Λ) (hX : isPeriodic Λ X)

-- First, we show that a lattice is an additive, commutative group.

instance : Membership V Λ := ⟨fun v => hΛ.2 v⟩

lemma closed_under_addition : ∀ v w : V, v ∈ Λ → w ∈ Λ → v + w ∈ Λ := by
  sorry

-- instance : AddCommGroup Λ where
--   add := fun v w => ⟨v + w, sorry
--   ⟩
--   add_assoc := fun v w x => add_assoc v w x
--   zero := ⟨0, sorry⟩
--   zero_add := fun v => zero_add v
--   nsmul := sorry
--   zsmul := sorry
--   neg := fun v => ⟨-v, sorry⟩
--   add_zero := fun v => add_zero v
--   add_left_neg := fun v => add_left_neg v
--   add_comm := fun v w => add_comm v w

instance ActionOnPeriodic : AddAction Λ X := ⟨
  fun v x => v + x,
  fun v w x => rfl,
  fun v => (add_zero v).symm⟩

instance : AddAction Λ V := ActionOnPeriodic hΛ sorry

end ActionbyTranslation

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
