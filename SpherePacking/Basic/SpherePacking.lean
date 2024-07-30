import Mathlib

/-!
# Density of Sphere Packings

Let `X ⊆ ℝ^d` be a set of points such that distinct points are at least distance `r` apart. Putting
a ball of radius `r / 2` around each point, we have a configuration of *sphere packing*. We call `X`
the sphere packing centers.

We also define the *density* of the configuration.
-/

open scoped ENNReal
open Metric BigOperators Pointwise Filter MeasureTheory

section Definitions

structure SpherePacking (d : ℕ) where
  centers : Set (EuclideanSpace ℝ (Fin d))
  radius : ℝ
  radius_pos : 0 < radius
  centers_dist : Pairwise (radius ≤ dist · · : centers → centers → Prop)

structure PeriodicSpherePacking (d : ℕ) extends SpherePacking d where
  Λ : AddSubgroup (EuclideanSpace ℝ (Fin d))
  Λ_discrete : DiscreteTopology Λ := by infer_instance
  Λ_lattice : IsZlattice ℝ Λ := by infer_instance
  -- Note that an AddAction here is not enough, because
  Λ_action : ∀ ⦃x y⦄, x ∈ Λ → y ∈ centers → x + y ∈ centers

variable {d : ℕ}

noncomputable instance PeriodicSpherePacking.instAddAction (S : PeriodicSpherePacking d) :
    AddAction S.Λ S.centers where
  vadd x y := ⟨↑x + ↑y, S.Λ_action x.prop y.prop⟩
  zero_vadd := by
    intro ⟨v, hv⟩
    apply Subtype.ext
    exact zero_add v
  add_vadd := by
    intro ⟨u, hu⟩ ⟨v, hv⟩ ⟨p, hp⟩
    apply Subtype.ext
    exact add_assoc u v p

abbrev SpherePacking.balls (S : SpherePacking d) : Set (EuclideanSpace ℝ (Fin d)) :=
  ⋃ x ∈ S.centers, ball x (S.radius / 2)

noncomputable def SpherePacking.finiteDensity (S : SpherePacking d) (R : ℝ) : ℝ≥0∞ :=
  volume (S.balls ∩ ball 0 R) / (volume (ball (0 : EuclideanSpace ℝ (Fin d)) R))

noncomputable def SpherePacking.density (S : SpherePacking d) : ℝ≥0∞ :=
  limsup S.finiteDensity atTop

end Definitions

noncomputable section Density

variable {d : ℕ} (S : SpherePacking d)

/-- The `PeriodicSpherePackingConstant` in dimension d is the supremum of the density of all
periodic packings. See also `<TODO>` for specifying the separation radius of the packings. -/
def PeriodicSpherePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ S : PeriodicSpherePacking d, S.density

/-- The `SpherePackingConstant` in dimension d is the supremum of the density of all packings. See
also `<TODO>` for specifying the separation radius of the packings. -/
def SpherePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ S : SpherePacking d, S.density

end Density

section DensityLemmas

open SpherePacking

variable {d : ℕ} (S : SpherePacking d)

lemma finiteDensity_le_one (R : ℝ) : S.finiteDensity R ≤ 1 := by
  rw [finiteDensity]
  apply ENNReal.div_le_of_le_mul
  rw [one_mul]
  exact volume.mono Set.inter_subset_right

lemma density_le_one : S.density ≤ 1 := by
  rw [density]
  apply limsup_le_iSup.trans
  apply iSup_le
  intro
  exact finiteDensity_le_one _ _

-- TODO

/-- Finite density of a scaled packing. -/
lemma density_smul (r : ℝ) (hX : Pairwise (r ≤ dist · · : X → X → Prop))
    (R : ℝ) (c : ℝ) (hc : 0 < c) :
      FiniteDensity (c • X) (c * r) (c * R) = FiniteDensity X r R := by
  simp_rw [FiniteDensity]

/-- Density of a scaled packing. -/
lemma density_smul (r : ℝ) (hX : Pairwise (r ≤ dist · · : X → X → Prop)) (c : ℝ) (hc : 0 < c) :
    Density (c • X) (c * r) = Density X r := by
  sorry

theorem aux (d : ℕ) :
    PeriodicSpherePackingConstant d
      = ⨆ (X : Set (EuclideanSpace ℝ (Fin d))) (Λ : AddSubgroup (EuclideanSpace ℝ (Fin d)))
        (inst1 : DiscreteTopology Λ) (inst2 : IsZlattice ℝ Λ) (inst3 : AddAction Λ X),
          Density X 1 := by
  rw [PeriodicSpherePackingConstant, iSup_comm]
  apply le_antisymm
  · -- ⨆ (r) (X) (..), Density X r ≤ ⨆ (X) (..), Density X 1
    sorry
  · -- ⨆ (X) (..), Density X 1 ≤ ⨆ (r) (X) (..), Density X r
    convert le_ciSup ?_ (1 : ℝ)
    · rfl
    · use 1
      simp_rw [mem_upperBounds, Set.mem_range]
      rintro C ⟨r, rfl⟩
      repeat (apply iSup_le; intro)
      exact density_le_one _ _

end DensityLemmas
