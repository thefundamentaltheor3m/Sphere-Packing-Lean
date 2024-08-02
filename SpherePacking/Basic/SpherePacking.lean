/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Gareth Ma
-/
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
  separation : ℝ
  separation_pos : 0 < separation := by positivity
  centers_dist : Pairwise (separation ≤ dist · · : centers → centers → Prop)

structure PeriodicSpherePacking (d : ℕ) extends SpherePacking d where
  Λ : AddSubgroup (EuclideanSpace ℝ (Fin d))
  -- Note that an AddAction here is not enough, because
  Λ_action : ∀ ⦃x y⦄, x ∈ Λ → y ∈ centers → x + y ∈ centers
  Λ_discrete : DiscreteTopology Λ := by infer_instance
  Λ_lattice : IsZlattice ℝ Λ := by infer_instance

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

@[simp]
abbrev SpherePacking.balls (S : SpherePacking d) : Set (EuclideanSpace ℝ (Fin d)) :=
  ⋃ x ∈ S.centers, ball x (S.separation / 2)

@[simp]
noncomputable def SpherePacking.finiteDensity (S : SpherePacking d) (R : ℝ) : ℝ≥0∞ :=
  volume (S.balls ∩ ball 0 R) / (volume (ball (0 : EuclideanSpace ℝ (Fin d)) R))

@[simp]
noncomputable def SpherePacking.density (S : SpherePacking d) : ℝ≥0∞ :=
  limsup S.finiteDensity atTop

end Definitions

section Instances
variable {d : ℕ}
open Real

-- Unfortunately I can't define a SMul ℝ (SpherePacking d) because we require 0 < c
-- Perhaps we can define a monoid action instead - Sid
def SpherePacking.scale (S : SpherePacking d) {c : ℝ} (hc : 0 < c) : SpherePacking d where
  centers := c • S.centers
  separation := c * S.separation
  separation_pos := Real.mul_pos hc S.separation_pos
  centers_dist := fun ⟨x, hx⟩ ⟨y, hy⟩ _ ↦ by
    change c * S.separation ≤ ‖x - y‖
    obtain ⟨x', ⟨hx', rfl⟩⟩ := Set.mem_smul_set.mp hx
    obtain ⟨y', ⟨hy', rfl⟩⟩ := Set.mem_smul_set.mp hy
    rw [← smul_sub, norm_smul, norm_eq_abs, abs_eq_self.mpr hc.le]
    rw [ne_eq, Subtype.mk.injEq] at *
    have : x' ≠ y' := by rintro rfl; tauto
    have : (⟨x', hx'⟩ : S.centers) ≠ ⟨y', hy'⟩ := by simp [this]
    have := S.centers_dist this
    exact (mul_le_mul_left hc).mpr this

noncomputable def PeriodicSpherePacking.scale (S : PeriodicSpherePacking d) {c : ℝ} (hc : 0 < c) :
    PeriodicSpherePacking d := {
  SpherePacking.scale S.toSpherePacking hc with
  Λ := c • S.Λ
  Λ_action := fun x y hx hy ↦ by
    simp_all only [SpherePacking.scale, Set.mem_smul_set, AddSubgroup.mem_smul_pointwise_iff_exists]
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    use x + y, S.Λ_action hx hy, smul_add ..
  Λ_discrete := by
    have := S.Λ_discrete
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff] at this ⊢
    obtain ⟨ε, hε, hε'⟩ := this
    use c * ε, Real.mul_pos hc hε
    simp_rw [dist_zero_right, AddSubgroup.coe_norm, AddSubgroup.coe_pointwise_smul,
      Subtype.forall, AddSubmonoid.mk_eq_zero, AddSubgroup.mem_smul_pointwise_iff_exists] at hε' ⊢
    rintro x ⟨x, hx, rfl⟩ hx'
    rw [norm_smul, norm_eq_abs, abs_eq_self.mpr hc.le, mul_lt_mul_left hc] at hx'
    rw [hε' x hx hx', smul_zero]
  Λ_lattice := by
    haveI := S.Λ_discrete
    haveI := S.Λ_lattice
    use ?_
    rw [← S.Λ_lattice.span_top]
    ext v
    simp_rw [Submodule.mem_span]
    constructor <;> intro h p hp
    · specialize h (c • p) ?_
      · rw [AddSubgroup.coe_pointwise_smul, Submodule.coe_pointwise_smul]
        exact Set.smul_set_mono hp
      · have : c • v ∈ c • p := Submodule.smul_mem _ _ h
        have := Submodule.smul_mem_pointwise_smul _ c⁻¹ _ this
        simpa [smul_smul, inv_mul_cancel hc.ne.symm, one_smul]
    · specialize h (c⁻¹ • p) ?_
      · rw [AddSubgroup.coe_pointwise_smul, Submodule.coe_pointwise_smul] at *
        have := Set.smul_set_mono (a := c⁻¹) hp
        rwa [smul_smul, inv_mul_cancel hc.ne.symm, one_smul] at this
      · have : c⁻¹ • v ∈ c⁻¹ • p := Submodule.smul_mem _ _ h
        have := Submodule.smul_mem_pointwise_smul _ c _ this
        simpa [smul_smul, mul_inv_cancel hc.ne.symm, one_smul]
}

end Instances

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
open scoped NNReal
namespace SpherePacking

variable {d : ℕ} (S : SpherePacking d) {c : ℝ≥0}

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

theorem EuclideanSpace.volume_ball_mul {ι : Type*} [Nonempty ι] [Fintype ι]
    {x : EuclideanSpace ℝ ι} {c : ℝ} (hc : 0 ≤ c) (R : ℝ) :
      volume (ball x (c * R)) = ENNReal.ofReal c ^ Fintype.card ι * volume (ball x R) := by
  simp_rw [EuclideanSpace.volume_ball]
  simp only [← mul_assoc]
  rw [ENNReal.ofReal_mul hc, mul_pow]

/-- Finite density of a scaled packing. -/
lemma scale_finiteDensity (hd : 0 < d) (S : SpherePacking d) {c : ℝ} (hc : 0 < c) (R : ℝ) :
    (S.scale hc).finiteDensity (c * R) = S.finiteDensity R := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  dsimp [finiteDensity, balls, scale]
  rw [EuclideanSpace.volume_ball_mul hc.le]
  sorry

/-- Density of a scaled packing. -/
lemma scale_density (hd : 0 < d) (S : SpherePacking d) {c : ℝ} (hc : 0 < c) :
    (S.scale hc).density = S.density := by
  -- Proving this would be a good practice for limsup API
  dsimp [density, finiteDensity]
  sorry

theorem constant_eq_constant_normalized (hd : 0 < d) :
    SpherePackingConstant d = ⨆ (S : SpherePacking d) (_ : S.separation = 1), S.density := by
  rw [iSup_subtype', SpherePackingConstant]
  apply le_antisymm
  · apply iSup_le
    intro S
    have h := inv_mul_cancel S.separation_pos.ne.symm
    have := le_iSup (fun S : { S : SpherePacking d // S.separation = 1 } ↦ S.val.density)
        ⟨S.scale (inv_pos.mpr S.separation_pos), h⟩
    simpa only [scale_density hd]
  · apply iSup_le
    intro ⟨S, _⟩
    exact le_iSup density S

end SpherePacking
end DensityLemmas
