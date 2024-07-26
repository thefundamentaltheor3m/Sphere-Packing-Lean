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

class SpherePackingCentres (X : Set V) (r : ℝ := 1) [DiscreteTopology X] where
  nonoverlapping : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → r ≤ ‖x - y‖

class LatticePackingCentres (X : AddSubgroup V) [DiscreteTopology X] [isLattice X] extends
  SpherePackingCentres d X

class PeriodicPackingCentres (X : Set V) [DiscreteTopology X] [SpherePackingCentres d X]
  {Λ : AddSubgroup V} [DiscreteTopology Λ] [isLattice Λ] where
  periodic : ∀ x ∈ X, ∀ y ∈ Λ, x + y ∈ X

def Packing_of_Centres (X : Set V) (r : ℝ)
    [DiscreteTopology X] [SpherePackingCentres d X r] : Set V :=
  ⋃ x ∈ X, (B x (r / 2))

end Definitions

local notation "P" => Packing_of_Centres d

noncomputable section Density

open scoped ENNReal
open MeasureTheory

-- NOTE (grhkm): I *might* have messed up some constants with the introduction of (r : ℝ)
-- Probably a TODO to doublecheck
def FiniteDensity (X : Set V) (r : ℝ) [DiscreteTopology X] [SpherePackingCentres d X r] (R : ℝ) :
    ℝ≥0∞ :=
  volume ((P X r) ∩ B (0:V) R) / (volume (B (0:V) R))

def Density (X : Set V) (r : ℝ) [DiscreteTopology X] [SpherePackingCentres d X r] : ℝ≥0∞ :=
  Filter.limsup (FiniteDensity d X r) Filter.atTop

def Constant : ENNReal :=
  sSup {x : ℝ≥0∞ |
    ∃ (X : Set V) (r : ℝ) (_inst1 : DiscreteTopology X) (_inst2 : SpherePackingCentres d X r),
      Density d X r = x}
  -- I don't really like how this looks. Is there a better way of formalising it?

end Density

end SpherePacking
