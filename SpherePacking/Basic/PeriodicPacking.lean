import SpherePacking.Basic.SpherePacking

/- In this file, we establish results about density of periodic packings. This roughly corresponds
to Section 2.2, "Bounds on Finite Density of Periodic Packing". -/

variable
  (X : Set (V d)) (r : ℝ) [DiscreteTopology X] [SpherePackingCentres d X r]
  (Λ : AddSubgroup (V d)) [DiscreteTopology Λ] [IsZlattice ℝ Λ] [PeriodicPackingCentres d X r Λ]
  {F : Set (V d)} (hF : IsAddFundamentalDomain Λ F volume)
