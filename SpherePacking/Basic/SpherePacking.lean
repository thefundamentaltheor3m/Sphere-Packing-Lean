/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Gareth Ma
-/
import Mathlib
import SpherePacking.ForMathlib.VolumeOfBalls
import SpherePacking.ForMathlib.Real

open BigOperators MeasureTheory Metric

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

-- I considered defining a SetOf instance to treat SpherePacking as its centers automatically,
-- but decided against it and opt for explicitly stating the conversion
structure SpherePacking (d : ℕ) where
  centers : Set (EuclideanSpace ℝ (Fin d))
  separation : ℝ
  separation_pos : 0 < separation := by positivity
  centers_dist : Pairwise (separation ≤ dist · · : centers → centers → Prop)

structure PeriodicSpherePacking (d : ℕ) extends SpherePacking d where
  Λ : AddSubgroup (EuclideanSpace ℝ (Fin d))
  -- Note that an AddAction here is not enough, because it might not agree with the action induced
  -- by EuclideanSpace
  Λ_action : ∀ ⦃x y⦄, x ∈ Λ → y ∈ centers → x + y ∈ centers
  Λ_discrete : DiscreteTopology Λ := by infer_instance
  Λ_lattice : IsZlattice ℝ Λ := by infer_instance

variable {d : ℕ}

theorem SpherePacking.centers_dist' (S : SpherePacking d) (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ S.centers) (hy : y ∈ S.centers) (hxy : x ≠ y) :
    S.separation ≤ dist x y := by
  have : (⟨x, hx⟩ : S.centers) ≠ ⟨y, hy⟩ := Subtype.coe_ne_coe.mp hxy
  -- The following fails. Reason unknown.
  -- exact S.centers_dist this
  have := S.centers_dist this
  simp only at this
  exact this

instance SpherePacking.instCentersDiscrete (S : SpherePacking d) :
    DiscreteTopology S.centers := by
  simp_rw [← singletons_open_iff_discrete, Metric.isOpen_iff]
  intro ⟨u, hu⟩ ⟨v, hv⟩ huv
  simp_rw [Set.subset_singleton_iff, mem_ball, Subtype.forall, Subtype.mk.injEq]
  rw [Set.mem_singleton_iff, Subtype.mk.injEq] at huv
  subst huv
  use S.separation, S.separation_pos
  intro a ha h_dist
  contrapose! h_dist
  exact S.centers_dist <| Subtype.coe_ne_coe.mp h_dist

noncomputable instance PeriodicSpherePacking.addAction (S : PeriodicSpherePacking d) :
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
  ⋃ x : S.centers, ball (x : EuclideanSpace ℝ (Fin d)) (S.separation / 2)

noncomputable def SpherePacking.finiteDensity (S : SpherePacking d) (R : ℝ) : ℝ≥0∞ :=
  volume (S.balls ∩ ball 0 R) / (volume (ball (0 : EuclideanSpace ℝ (Fin d)) R))

noncomputable def SpherePacking.density (S : SpherePacking d) : ℝ≥0∞ :=
  limsup S.finiteDensity atTop

end Definitions

section Scaling
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

lemma PeriodicSpherePacking.scale_toSpherePacking
    {S : PeriodicSpherePacking d} {c : ℝ} (hc : 0 < c) :
    (S.scale hc).toSpherePacking = S.toSpherePacking.scale hc :=
  rfl

lemma SpherePacking.scale_balls {S : SpherePacking d} {c : ℝ} (hc : 0 < c) :
    (S.scale hc).balls = c • S.balls := by
  ext x
  simp only [scale, Set.mem_iUnion, Set.iUnion_coe_set]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have := Set.smul_mem_smul_set (a := c⁻¹) hy
    rw [smul_smul, inv_mul_cancel hc.ne.symm, one_smul] at this
    simp only [mem_ball, Set.mem_smul_set, Set.mem_iUnion] at hxy ⊢
    use c⁻¹ • x, ?_, ?_
    · use c⁻¹ • y, this
      have : 0 ≤ c⁻¹ := by positivity
      have h : 0 < c⁻¹ := by positivity
      rw [dist_eq_norm] at hxy ⊢
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_eq_self.mpr this]
      apply lt_of_lt_of_le (b := c⁻¹ * (c * S.separation / 2))
      · exact (mul_lt_mul_left h).mpr hxy
      · rw [mul_div_assoc, ← mul_assoc, inv_mul_cancel hc.ne.symm, one_mul]
    · rw [smul_smul, mul_inv_cancel hc.ne.symm, one_smul]
  · intro h
    simp only [mem_ball, Set.mem_smul_set, Set.mem_iUnion] at h ⊢
    obtain ⟨x, ⟨⟨y, hy₁, hy₂⟩, rfl⟩⟩ := h
    use c • y, ⟨y, hy₁, rfl⟩
    rw [dist_eq_norm] at hy₂ ⊢
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_eq_self.mpr hc.le, mul_div_assoc]
    gcongr

lemma PeriodicSpherePacking.scale_balls {S : PeriodicSpherePacking d} {c : ℝ} (hc : 0 < c) :
    (S.scale hc).balls = c • S.balls :=
  SpherePacking.scale_balls hc

end Scaling

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
namespace SpherePacking

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

-- TODO: Fix the namespace issues lol
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
  have : ball (0 : EuclideanSpace ℝ (Fin d)) (c * R) = c • ball 0 R := by
    convert (_root_.smul_ball hc.ne.symm (0 : EuclideanSpace ℝ (Fin d)) R).symm
    · exact Eq.symm (DistribMulAction.smul_zero c)
    · rw [Real.norm_eq_abs, abs_eq_self.mpr hc.le]
  rw [finiteDensity, scale_balls, this]
  have : c • S.balls ∩ c • ball 0 R = c • (S.balls ∩ ball 0 R) := by
    ext x;
    simp only [Set.iUnion_coe_set, Set.mem_inter_iff, Set.mem_smul_set]
    constructor <;> intro h
    · done
    · done
  sorry

example {s t : Set ℝ} {c : ℝ} (hc : c ≠ 0) : c • (s ∩ t) = (c • s) ∩ (c • t) :=
  Set.smul_set_inter₀ hc

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

section PeriodicDensity

/- In this subsection, we prove that PeriodicDensity is equivalent to Density. This would allow us
to compute density of a periodic sphere packing easier. -/

-- TODO: state the theorem lol (first need to define PeriodicDensity in PeriodicPacking.lean
-- Probably also using dot notation under PeriodicSpherePacking namespace

end PeriodicDensity

section BasicResults
open scoped ENNReal
open EuclideanSpace

variable {d : ℕ} (S : SpherePacking d)

/- In this section we establish basic results about FiniteDensity and Density of different types of
packings. -/

lemma biUnion_inter_balls_subset_biUnion_balls_inter
    (X : Set (EuclideanSpace ℝ (Fin d))) (r R : ℝ) :
    ⋃ x ∈ X ∩ ball 0 R, ball x r ⊆ (⋃ x ∈ X, ball x r) ∩ ball 0 (R + r) := by
  intro x hx
  simp at hx ⊢
  obtain ⟨y, ⟨hy₁, hy₂⟩⟩ := hx
  use ⟨y, ⟨hy₁.left, hy₂⟩⟩
  apply lt_of_le_of_lt <| norm_le_norm_add_norm_sub' x y
  gcongr <;> tauto

lemma biUnion_balls_inter_subset_biUnion_inter_balls
    (X : Set (EuclideanSpace ℝ (Fin d))) (r R : ℝ) :
    (⋃ x ∈ X, ball x r) ∩ ball 0 (R - r) ⊆ ⋃ x ∈ X ∩ ball 0 R, ball x r := by
  intro x hx
  simp at hx ⊢
  obtain ⟨⟨y, ⟨hy₁, hy₂⟩⟩, hx⟩ := hx
  use y, ⟨hy₁, ?_⟩, hy₂
  calc
    ‖y‖ ≤ ‖x‖ + ‖y - x‖ := norm_le_norm_add_norm_sub' y x
    _ = ‖x‖ + dist x y := by rw [dist_comm]; rfl
    _ < R - r + r := by gcongr
    _ = R := by ring

theorem SpherePacking.volume_iUnion_balls_eq_tsum
    (R : ℝ) {r' : ℝ} (hr' : r' ≤ S.separation / 2) :
    volume (⋃ x : ↑(S.centers ∩ ball 0 R), ball (x : EuclideanSpace ℝ (Fin d)) r')
      = ∑' x : ↑(S.centers ∩ ball 0 R), volume (ball (x : EuclideanSpace ℝ (Fin d)) r') := by
  have : Countable S.centers := countable_of_Lindelof_of_discrete
  have : Countable ↑(S.centers ∩ ball 0 R) := Set.Countable.mono (Set.inter_subset_left) this
  apply measure_iUnion ?_ (fun _ ↦ measurableSet_ball)
  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  apply ball_disjoint_ball
  simp_rw [ne_eq, Subtype.mk.injEq] at h ⊢
  linarith [S.centers_dist' x y hx.left hy.left h]

-- https://github.com/leanprover-community/mathlib4/pull/15214/files
-- Putting it as axioms so that #print axioms will show that this should be removed
-- TODO: remove when merged
axiom ENNReal.tsum_const_eq' {α : Type*} (s : Set α) (c : ENNReal) :
    ∑' (_ : s), c = s.encard * c

/-- This gives an upper bound on the number of points in the sphere packing X with norm less than R.
-/
theorem SpherePacking.inter_ball_encard_le (hd : 0 < d) (R : ℝ) :
    (S.centers ∩ ball 0 R).encard ≤
      volume (S.balls ∩ ball 0 (R + S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) := by
  have h := volume.mono <|
    biUnion_inter_balls_subset_biUnion_balls_inter S.centers (S.separation / 2) R
  change volume _ ≤ volume _ at h
  simp_rw [Set.biUnion_eq_iUnion, S.volume_iUnion_balls_eq_tsum R (le_refl _),
    Measure.addHaar_ball_center, ENNReal.tsum_const_eq'] at h
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rwa [← ENNReal.le_div_iff_mul_le] at h <;> left
  · exact (volume_ball_pos _ (by linarith [S.separation_pos])).ne.symm
  · exact (volume_ball_lt_top _).ne

/-- This gives an upper bound on the number of points in the sphere packing X with norm less than R.
-/
theorem SpherePacking.inter_ball_encard_ge (hd : 0 < d) (R : ℝ) :
    (S.centers ∩ ball 0 R).encard ≥
      volume (S.balls ∩ ball 0 (R - S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) := by
  have h := volume.mono <|
    biUnion_balls_inter_subset_biUnion_inter_balls S.centers (S.separation / 2) R
  change volume _ ≤ volume _ at h
  simp_rw [Set.biUnion_eq_iUnion, S.volume_iUnion_balls_eq_tsum _ (le_refl _),
    Measure.addHaar_ball_center, ENNReal.tsum_const_eq'] at h
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rwa [← ENNReal.div_le_iff_le_mul] at h <;> left
  · exact (volume_ball_pos _ (by linarith [S.separation_pos])).ne.symm
  · exact (volume_ball_lt_top _).ne

theorem aux6 (R : ℝ) : Finite ↑(S.centers ∩ ball 0 R) := by
  apply Set.encard_lt_top_iff.mp
  by_cases hd : 0 < d
  · haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
    apply ENat.toENNReal_lt.mp
    apply lt_of_le_of_lt (S.inter_ball_encard_le hd R)
    apply ENNReal.div_lt_top ?_ (volume_ball_pos _ (by linarith [S.separation_pos])).ne.symm
    rw [← lt_top_iff_ne_top]
    calc
      _ ≤ volume (ball 0 (R + S.separation / 2)) := volume.mono Set.inter_subset_right
      _ < ⊤ := EuclideanSpace.volume_ball_lt_top _
  · rw [not_lt, nonpos_iff_eq_zero] at hd
    have : (ball (0 : EuclideanSpace ℝ (Fin 0)) R).encard ≤ 1 := by
      rw [← Set.Finite.cast_ncard_eq (Set.toFinite _), Nat.cast_le_one]
      exact Set.ncard_le_one_of_subsingleton _
    subst hd
    apply lt_of_le_of_lt (Set.encard_mono inf_le_right)
    apply lt_of_le_of_lt this (by decide)

theorem SpherePacking.finiteDensity_ge (hd : 0 < d) (R : ℝ) :
    S.finiteDensity R
      ≥ (S.centers ∩ ball 0 (R - S.separation / 2)).encard
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [finiteDensity, balls]
  apply ENNReal.div_le_div_right
  rw [← ENNReal.le_div_iff_mul_le] <;> try left
  · have := S.inter_ball_encard_le hd (R - S.separation / 2)
    rwa [sub_add_cancel] at this
  · exact (volume_ball_pos _ (by linarith [S.separation_pos])).ne.symm
  · exact (volume_ball_lt_top _).ne

theorem SpherePacking.finiteDensity_le (hd : 0 < d) (R : ℝ) :
    S.finiteDensity R
      ≤ (S.centers ∩ ball 0 (R + S.separation / 2)).encard
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [finiteDensity, balls]
  apply ENNReal.div_le_div_right
  rw [← ENNReal.div_le_iff_le_mul] <;> try left
  · have := S.inter_ball_encard_ge hd (R + S.separation / 2)
    rwa [add_sub_cancel_right] at this
  · exact (volume_ball_pos _ (by linarith [S.separation_pos])).ne.symm
  · exact (volume_ball_lt_top _).ne

example : volume (ball (0 : EuclideanSpace ℝ (Fin 8)) (√2 / 2))
    = ENNReal.ofReal (Real.pi ^ 4 / 384) := by
  have h₁ : √2 ^ 8 = 16 := by
    trans (√2 ^ 2) ^ 4
    · rw [← pow_mul]
    · norm_num
  have h₂ : √Real.pi ^ 8 = Real.pi ^ 4 := by
    trans (√Real.pi ^ 2) ^ 4
    · rw [← pow_mul]
    · rw [Real.sq_sqrt Real.pi_nonneg]
  have h₃ : Nat.factorial 4 = 24 := by
    decide
  rw [volume_ball, ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul] <;> try positivity
  norm_num
  rw [h₁, h₂, h₃]
  congr 1
  ring_nf

open scoped Topology NNReal
open Asymptotics Filter ENNReal

private lemma aux {ε : ℝ≥0∞} (hε : 0 < ε) (hd : 0 < d) :
    ∃ k : ℝ, k ≥ 0 ∧ ∀ k' ≥ k, ENNReal.ofReal ((k' / (k' + 1)) ^ d) ∈ Set.Icc (1 - ε) (1 + ε) := by
  -- wtf
  by_cases hε' : ε = ⊤
  · use 0
    subst hε'
    simp
  · have : ∃ t : ℝ, 0 < t ∧ ε = ENNReal.ofReal t := by
      obtain ⟨⟨t, ht_nonneg⟩, rfl⟩ := Option.ne_none_iff_exists'.mp hε'
      rw [ENNReal.some_eq_coe, ENNReal.coe_pos] at hε
      use t, hε, (ENNReal.ofReal_eq_coe_nnreal ht_nonneg).symm
    obtain ⟨t, ht_pos, rfl⟩ := this
    by_cases ht : t ≤ 1
    · have hd' : (d : ℝ) ≠ 0 := by rw [ne_eq, Nat.cast_eq_zero]; exact Nat.not_eq_zero_of_lt hd
      let K : ℝ := 1 / (1 - (1 - t) ^ (1 / (d : ℝ))) - 1
      have hK : 0 ≤ K := by
        simp_rw [K]
        apply sub_nonneg.mpr
        apply one_le_one_div
        · rw [sub_pos]
          apply Real.rpow_lt_one
          · linarith
          · linarith
          · exact one_div_pos.mpr <| Nat.cast_pos'.mpr hd
        · rw [sub_le_self_iff]
          apply Real.rpow_nonneg
          linarith
      use K, hK
      intro k' hk'
      have : 1 - 1 / (k' + 1) ≥ 1 - 1 / (K + 1) := by
        gcongr
      have hK' : (k' / (k' + 1)) ^ d ≥ 1 - t := calc
        -- (K / (K + 1)) ^ d = (1 - 1 / (K + 1)) ^ d := by
        (k' / (k' + 1)) ^ d = (1 - 1 / (k' + 1)) ^ d := by
          congr
          rw [eq_sub_iff_add_eq, div_add_div_same, div_self]
          linarith
        _ ≥ (1 - 1 / (K + 1)) ^ d := by
          gcongr
          rw [sub_nonneg, one_div_le, div_one]
          · linarith
          · linarith
          · linarith
        _ = ((1 - t) ^ (1 / (d : ℝ))) ^ d := by simp [K]
        _ = 1 - t := by
          rw [← Real.rpow_mul_natCast (by linarith), one_div_mul_cancel hd', Real.rpow_one]
      rw [Set.mem_Icc, tsub_le_iff_right, ← ENNReal.ofReal_add]
      · constructor
        · apply ENNReal.one_le_ofReal.mpr
          linarith
        · trans 1
          · apply ENNReal.ofReal_le_one.mpr
            apply pow_le_one
            · apply div_nonneg
              · linarith
              · linarith
            · apply (div_le_one _).mpr
              · linarith
              · linarith
          · exact le_self_add
      · linarith
      · linarith
    · use 0, le_refl 0
      intro k' hk'
      have : 0 ≤ k' ^ d / (k' + 1) ^ d := by
        apply div_nonneg
        · apply pow_nonneg
          linarith
        · apply pow_nonneg
          linarith
      have : k' ^ d / (k' + 1) ^ d ≤ 1 := by
        apply (div_le_one _).mpr
        · apply pow_le_pow_left
          · linarith
          · linarith
        · apply pow_pos
          linarith
      rw [not_le] at ht
      rw [div_pow, Set.mem_Icc, tsub_le_iff_right]
      constructor
      · rw [← ENNReal.ofReal_add, ENNReal.one_le_ofReal]
        · linarith
        · linarith
        · linarith
      · trans 1
        · exact ENNReal.ofReal_le_one.mpr this
        · apply le_self_add

theorem volume_ball_ratio_tendsto_nhds_one {C : ℝ} (hd : 0 < d) (hC : 0 < C) :
    Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))) atTop (𝓝 1) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have (R : ℝ) (hR : 0 ≤ R) : volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
        = ENNReal.ofReal (R ^ d / (R + C) ^ d) := by
    rw [volume_ball, volume_ball, Fintype.card_fin, ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul,
      ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_div_of_pos, mul_div_mul_right]
    <;> positivity
  rw [ENNReal.tendsto_atTop (by decide)]
  intro ε hε
  obtain ⟨k, ⟨hk₁, hk₂⟩⟩ := aux hε hd
  use k * C
  intro n hn
  specialize hk₂ (n / C) ((le_div_iff hC).mpr hn)
  -- boring
  rw [this]
  · convert hk₂
    rw [← div_pow]
    congr 1
    rw [div_eq_div_iff]
    · rw [mul_add, mul_add, ← mul_div_assoc, mul_one, div_mul_cancel₀, mul_div_right_comm]
      exact hC.ne.symm
    · apply ne_of_gt
      calc
        n + C ≥ k * C + C := by gcongr
        _ > 0 := by positivity
    · apply ne_of_gt
      calc
        n / C + 1 ≥ k * C / C + 1 := by gcongr
        _ = k + 1 := by rw [mul_div_cancel_right₀ _ hC.ne.symm]
        _ > 0 := by linarith
  · exact (by positivity : 0 ≤ k * C).trans hn

end BasicResults
