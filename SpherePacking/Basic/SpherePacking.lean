import Mathlib
import SpherePacking.Basic.EuclideanLattice

open Euclidean BigOperators EuclideanLattice

variable (d : ℕ)
local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "B" => Euclidean.ball

namespace SpherePacking

section Definitions

class SpherePackingCentres (X : Set V) [DiscreteTopology X] where
  nonoverlapping : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → Euclidean.dist x y ≥ 2

class LatticePackingCentres (X : AddSubgroup V) [DiscreteTopology X] [isLattice X] extends SpherePackingCentres d X

class PeriodicPackingCentres (X : Set V) [DiscreteTopology X] [SpherePackingCentres d X] {Λ : AddSubgroup V} [DiscreteTopology Λ] [isLattice Λ] where
  periodic : ∀ x ∈ X, ∀ y ∈ Λ, x + y ∈ X

def Packing_of_Centres (X : Set V) [DiscreteTopology X] [SpherePackingCentres d X] : Set V := ⋃ x ∈ X, (B x 1)

end Definitions

local notation "P" => Packing_of_Centres d

noncomputable section Density

open MeasureTheory

instance : MeasureSpace V := by infer_instance

instance : MeasureSpace V :=
{ volume := volume }

def FiniteDensity (X : Set V) [DiscreteTopology X] [SpherePackingCentres d X] (r : ℝ) : ENNReal := volume ((P X) ∩ B (0:V) r) / (volume (B (0:V) r))

def Density (X : Set V) [DiscreteTopology X] [SpherePackingCentres d X] : ENNReal := Filter.limsup (FiniteDensity d X) (Filter.atTop)

def Constant : ENNReal := sSup {x : ENNReal | ∃ X : Set V, ∃ inst1 : DiscreteTopology X, ∃ inst2 : SpherePackingCentres d X, Density d X = x} -- I don't really like how this looks. Is there a better way of formalising it?

end Density

end SpherePacking
