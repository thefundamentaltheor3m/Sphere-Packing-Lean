import Mathlib
import SpherePacking.Basic.EuclideanLattice

open Euclidean BigOperators EuclideanLattice

variable (d : ℕ)
local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "B" => Euclidean.ball

def Discrete (X : Set V) : Prop := (Countable X) ∧ (∀ x ∈ X, ∃ ε > 0, ∀ y ∈ X, y ≠ x → Euclidean.dist x y > ε)  -- Nothing equivalent in mathlib?

namespace SpherePacking

section Definitions

def Centres (X : Set V) : Prop := (Discrete d X) ∧ (∀ x ∈ X, ∀ y ∈ X, x ≠ y → Euclidean.dist x y ≥ 2)

def Packing_of_Centres (X : Set V) : Set V := ⋃ x ∈ X, {y | Euclidean.dist x y < 1}

def Packing (X P : Set V) : Prop := (Centres d X) ∧ (P = Packing_of_Centres d X)  -- We don't include boundaries

def isPacking (P : Set V) : Prop := ∃ X, Packing d X P

def LatticePacking (Λ P : Set V) : Prop := (Packing d Λ P) ∧ (isLattice Λ)

def isLatticePacking (P : Set V) : Prop := ∃ Λ, LatticePacking d Λ P

def PeriodicPacking (Λ P : Set V) : Prop := (LatticePacking d Λ P) ∧ (isPeriodic Λ P)

def isPeriodicPacking (P : Set V) : Prop := ∃ Λ, PeriodicPacking d Λ P

end Definitions

noncomputable section Density

open MeasureTheory

instance : MeasureSpace V := by infer_instance

instance : MeasureSpace V :=
{ volume := volume }

-- variables {X P : Set V} (hP : isPacking d X P)

def FiniteDensity (P : Set V) (r : ℝ) : ENNReal := volume (P ∩ B (0:V) r) / (volume (B (0:V) r))  -- Can remove hP and hr because nonneg error is handled by Euclidean.ball and strictly speaking this definition doesn't have to apply to a packing...

def Density (P : Set V) : ENNReal := Filter.limsup (FiniteDensity d P) (Filter.atTop)

def Constant : ENNReal := sSup {x : ENNReal | ∃ P, isPacking d P ∧ Density d P = x}

-- To convert a limit into a function, could it be some kind of exists.mk of some some number such that (tendsto that number) is satisfied?

end Density

section E8_Packing

def E8 := Packing_of_Centres 8 (EuclideanLattice.E8_normalised)

theorem Main : Constant 8 = Density 8 E8 := sorry

end E8_Packing

end SpherePacking
