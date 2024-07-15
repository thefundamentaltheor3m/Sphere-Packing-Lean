import Mathlib
import SpherePacking.Basic.EuclideanLattice

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

section Definitions_class

class SpherePackingCentres (X : Set V) [DiscreteTopology X] where
  nonoverlapping : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → Euclidean.dist x y ≥ 2

class LatticePackingCentres (X : AddSubgroup V) [DiscreteTopology X] [isLattice' X] extends SpherePackingCentres d X

class PeriodicPackingCentres (X : Set V) [DiscreteTopology X] [SpherePackingCentres d X] {Λ : AddSubgroup V} [DiscreteTopology Λ] [isLattice' Λ] where
  periodic : ∀ x ∈ X, ∀ y ∈ Λ, x + y ∈ X

def SpherePacking' (X : Set V) [DiscreteTopology X] [SpherePackingCentres d X] : Set V := ⋃ x ∈ X, (B x 1)

end Definitions_class

noncomputable section Density

open MeasureTheory

instance : MeasureSpace V := by infer_instance

instance : MeasureSpace V :=
{ volume := volume }

-- variables {X P : Set V} (hP : isPacking d X P)

-- variable {X : Set V} [SpherePackingCentres d X]

-- local notation "P" => SpherePacking' d X

def FiniteDensity (X : Set V) [DiscreteTopology X] [SpherePackingCentres d X] (r : ℝ) : ENNReal := volume ((SpherePacking' d X) ∩ B (0:V) r) / (volume (B (0:V) r))  -- Can remove hP and hr because nonneg error is handled by Euclidean.ball and strictly speaking this definition doesn't have to apply to a packing...

def Density (X : Set V) [DiscreteTopology X] [SpherePackingCentres d X] : ENNReal := Filter.limsup (FiniteDensity d X) (Filter.atTop)

def Constant : ENNReal := sSup {x : ENNReal | ∃ X : Set V, ∃ inst1 :DiscreteTopology X, ∃ inst2 : SpherePackingCentres d X, Density d X = x} -- I don't really like how this looks. Is there a better way of formalising it?

end Density

section E8_Packing

-- def E8 := Packing_of_Centres 8 (EuclideanLattice.E8_Normalised_Set)

instance : SpherePackingCentres 8 EuclideanLattice.E8_Normalised_Set where
  nonoverlapping := by
    intros x hx y hy hxy
    sorry


-- theorem Main : Constant 8 = Density 8 E8_Normalised_Set := sorry

end E8_Packing

end SpherePacking
