import Mathlib
import SpherePacking.Basic.EuclideanLattice

open Euclidean BigOperators EuclideanLattice

/-!
# The choices made in this file mirror those made in `Algebra.Module.Zlattice.Basic`. Specifically,
- All conditions pertaining to types of sphere packings are defined on the sets of centres
- A sphere packing can be built from any set of centres using `Packing_of_Centres`.
-/

variable (d : ℕ)
local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "B" => Euclidean.ball

namespace SpherePacking

section Definitions

-- TODO: Rename to IsSpherePackingCentres, then define SpherePackingCentres as the univ
-- and define Constant below as a sSup over this set
class SpherePackingCentres (X : Set V) (r : ℝ) [DiscreteTopology X] where
  nonoverlapping : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → r ≤ ‖x - y‖

class LatticePackingCentres (X : AddSubgroup V) (r : ℝ)
    [DiscreteTopology X] [IsZlattice ℝ X] extends
  SpherePackingCentres d X r

class PeriodicPackingCentres (X : Set V) (r : ℝ) [DiscreteTopology X] [SpherePackingCentres d X r]
    (Λ : AddSubgroup V) [DiscreteTopology Λ] [IsZlattice ℝ Λ] where
  periodic : ∀ x ∈ X, ∀ y ∈ Λ, x + y ∈ X

def Packing_of_Centres (X : Set V) (r : ℝ) [DiscreteTopology X] [SpherePackingCentres d X r] :
    Set V :=
  ⋃ x ∈ X, (B x (r / 2))

end Definitions

local notation "P" => Packing_of_Centres d

noncomputable section Density

open scoped ENNReal
open MeasureTheory

def FiniteDensity (X : Set V) (r : ℝ) [DiscreteTopology X] [SpherePackingCentres d X r] (R : ℝ) :
    ℝ≥0∞ :=
  volume ((P X r) ∩ B (0:V) R) / (volume (B (0:V) R))

def Density (X : Set V) (r : ℝ) [DiscreteTopology X] [SpherePackingCentres d X r] : ℝ≥0∞ :=
  Filter.limsup (FiniteDensity d X r) Filter.atTop

def PeriodicConstant : ENNReal :=
  sSup {x : ℝ≥0∞ |
    ∃ (X : Set V) (r : ℝ) (Λ : AddSubgroup V)
      (_inst1 : DiscreteTopology X) (_inst2 : SpherePackingCentres d X r)
      (_inst3 : DiscreteTopology Λ) (_inst4 : IsZlattice ℝ Λ)
      (_inst5 : PeriodicPackingCentres d X r Λ), Density d X r = x}

def Constant : ENNReal :=
  sSup {x : ℝ≥0∞ |
    ∃ (X : Set V) (r : ℝ) (_inst1 : DiscreteTopology X) (_inst2 : SpherePackingCentres d X r),
      Density d X r = x}
  -- I don't really like how this looks. Is there a better way of formalising it?

end Density

end SpherePacking
