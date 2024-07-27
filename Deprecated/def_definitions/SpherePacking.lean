import Mathlib
import SpherePacking.Deprecated.def_definitions.EuclideanLattice

open Euclidean BigOperators EuclideanLattice

variable (d : ℕ)
local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "B" => Euclidean.ball

namespace SpherePacking

section Definitions_def

def Discrete (X : Set V) : Prop := (Countable X) ∧ (∀ x ∈ X, ∃ ε > 0, ∀ y ∈ X, y ≠ x → Euclidean.dist x y > ε)  -- Nothing equivalent in mathlib?

def Centres (X : Set V) : Prop := (Discrete d X) ∧ (∀ x ∈ X, ∀ y ∈ X, x ≠ y → Euclidean.dist x y ≥ 2)

def Packing_of_Centres (X : Set V) : Set V := ⋃ x ∈ X, {y | Euclidean.dist x y < 1}

def Packing (X P : Set V) : Prop := (Centres d X) ∧ (P = Packing_of_Centres d X)  -- We don't include boundaries

def isPacking (P : Set V) : Prop := ∃ X, Packing d X P

def LatticePacking (Λ P : Set V) : Prop := (Packing d Λ P) ∧ (isLattice Λ)

def isLatticePacking (P : Set V) : Prop := ∃ Λ, LatticePacking d Λ P

def PeriodicPacking (Λ P : Set V) : Prop := (LatticePacking d Λ P) ∧ (isPeriodic Λ P)

def isPeriodicPacking (P : Set V) : Prop := ∃ Λ, PeriodicPacking d Λ P

end Definitions_def

end SpherePacking
