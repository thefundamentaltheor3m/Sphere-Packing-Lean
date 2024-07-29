import SpherePacking.Basic.SpherePacking

open MulAction
#check orbitRel.Quotient
variable {G : Type*} [Group G] {α : Type*} {X : Type*} [MulAction G X]
#check Quotient (orbitRel G X)

example : Set (Quotient (orbitRel G X)) := Set.univ

/- In this file, we establish results about density of periodic packings. This roughly corresponds
to Section 2.2, "Bounds on Finite Density of Periodic Packing". -/

open SpherePacking EuclideanSpace MeasureTheory

variable (d : ℕ)
local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "V" d => EuclideanSpace ℝ (Fin d)

variable
  (X : Set (V d)) (r : ℝ) [DiscreteTopology X] [SpherePackingCentres d X r]
  (Λ : AddSubgroup (V d)) [DiscreteTopology Λ] [IsZlattice ℝ Λ] [PeriodicPackingCentres d X r Λ]
  {F : Set (V d)} (hF : IsAddFundamentalDomain Λ F volume)

-- We want to define X / Λ

