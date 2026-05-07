/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Gareth Ma
-/
module
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Density of Sphere Packings: definitions and basic notions for periodic packings.
-/

open MeasureTheory Metric Filter Module

open scoped BigOperators ENNReal Pointwise

section Definitions

/-- A sphere packing in `R^d`, specified by a set of centers and a positive separation distance. -/
public structure SpherePacking (d : ℕ) where
  centers : Set (EuclideanSpace ℝ (Fin d))
  separation : ℝ
  separation_pos : 0 < separation := by positivity
  centers_dist : Pairwise (separation ≤ dist · · : centers → centers → Prop)

/-- A sphere packing that is invariant under translation by a `ℤ`-lattice. -/
public structure PeriodicSpherePacking (d : ℕ) extends SpherePacking d where
  lattice : Submodule ℤ (EuclideanSpace ℝ (Fin d))
  lattice_action : ∀ ⦃x y⦄, x ∈ lattice → y ∈ centers → x + y ∈ centers
  lattice_discrete : DiscreteTopology lattice := by infer_instance
  lattice_isZLattice : IsZLattice ℝ lattice := by infer_instance

variable {d : ℕ}

attribute [instance] PeriodicSpherePacking.lattice_discrete
  PeriodicSpherePacking.lattice_isZLattice

public theorem SpherePacking.centers_dist' (S : SpherePacking d) (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ S.centers) (hy : y ∈ S.centers) (hxy : x ≠ y) : S.separation ≤ dist x y :=
  S.centers_dist (i := ⟨x, hx⟩) (j := ⟨y, hy⟩) (Subtype.coe_ne_coe.mp hxy)

public instance SpherePacking.instCentersDiscrete (S : SpherePacking d) :
    DiscreteTopology S.centers := .of_forall_le_dist S.separation_pos S.centers_dist

public noncomputable instance PeriodicSpherePacking.addAction (S : PeriodicSpherePacking d) :
    AddAction S.lattice S.centers where
  vadd x y := ⟨↑x + ↑y, S.lattice_action x.prop y.prop⟩
  zero_vadd y := Subtype.ext (zero_add y.val)
  add_vadd _ _ _ := Subtype.ext (add_assoc ..)

@[simp]
public theorem PeriodicSpherePacking.addAction_vadd (S : PeriodicSpherePacking d)
    {x : S.lattice} {y : S.centers} :
    x +ᵥ y = ⟨x.val + y.val, S.lattice_action x.prop y.prop⟩ := rfl

/-- Balls of radius `S.separation / 2` around the centers of a packing. -/
@[expose, reducible] public def SpherePacking.balls (S : SpherePacking d) :
    Set (EuclideanSpace ℝ (Fin d)) := ⋃ x : S.centers, ball (x.val) (S.separation / 2)

/-- Volume of packing balls inside `ball 0 R`, normalized by `volume (ball 0 R)`. -/
@[expose] public noncomputable def SpherePacking.finiteDensity (S : SpherePacking d) (R : ℝ) :
    ℝ≥0∞ := volume (S.balls ∩ ball 0 R) / (volume (ball (0 : EuclideanSpace ℝ (Fin d)) R))

/-- The (upper) density: `limsup` of `finiteDensity` as `R → ∞`. -/
@[expose] public noncomputable def SpherePacking.density (S : SpherePacking d) : ℝ≥0∞ :=
  limsup S.finiteDensity atTop

public theorem PeriodicSpherePacking.basis_Z_span
    (S : PeriodicSpherePacking d) {ι : Type*} (b : Basis ι ℤ S.lattice) :
    Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) = S.lattice :=
  Basis.ofZLatticeBasis_span ℝ S.lattice b

public theorem PeriodicSpherePacking.mem_basis_Z_span
    (S : PeriodicSpherePacking d) {ι : Type*} (b : Basis ι ℤ S.lattice) (v) :
    v ∈ Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) ↔ v ∈ S.lattice :=
  SetLike.ext_iff.mp (S.basis_Z_span b) v

end Definitions

section Scaling
variable {d : ℕ}
open Real

/-- Scale a packing by a positive factor `c` (dilating centers and separation). -/
@[expose] public def SpherePacking.scale (S : SpherePacking d) {c : ℝ} (hc : 0 < c) :
    SpherePacking d where
  centers := c • S.centers
  separation := c * S.separation
  separation_pos := mul_pos hc S.separation_pos
  centers_dist := fun ⟨x, hx⟩ ⟨y, hy⟩ hxy ↦ by
    obtain ⟨x', hx', rfl⟩ := Set.mem_smul_set.mp hx
    obtain ⟨y', hy', rfl⟩ := Set.mem_smul_set.mp hy
    change c * S.separation ≤ ‖c • x' - c • y'‖
    rw [← smul_sub, norm_smul, norm_eq_abs, abs_eq_self.mpr hc.le]
    exact (mul_le_mul_iff_right₀ hc).mpr <| S.centers_dist (i := ⟨x', hx'⟩) (j := ⟨y', hy'⟩)
      fun heq ↦ hxy <| by simp [Subtype.ext_iff] at heq; simp [heq]

/-- Scale a periodic packing by a positive factor `c`, scaling both centers and the lattice. -/
@[expose] public noncomputable def PeriodicSpherePacking.scale (S : PeriodicSpherePacking d) {c : ℝ}
    (hc : 0 < c) : PeriodicSpherePacking d := {
  S.toSpherePacking.scale hc with
  lattice := c • S.lattice
  lattice_action := fun x y hx hy ↦ by
    simp_all only [SpherePacking.scale, Set.mem_smul_set]
    obtain ⟨x, hx, rfl⟩ := hx; obtain ⟨y, hy, rfl⟩ := hy
    exact ⟨x + y, S.lattice_action hx hy, smul_add ..⟩
  lattice_discrete := by
    have hd := S.lattice_discrete
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff] at hd ⊢
    obtain ⟨ε, hε, hε'⟩ := hd; refine ⟨c * ε, mul_pos hc hε, ?_⟩
    simp_rw [dist_zero_right, Subtype.forall] at hε' ⊢; rintro x ⟨x, hx, rfl⟩ hx'
    simp only [DistribSMul.toLinearMap_apply, Submodule.mk_eq_zero, smul_eq_zero,
      AddSubgroupClass.coe_norm, norm_smul, norm_eq_abs, abs_eq_self.mpr hc.le,
      mul_lt_mul_iff_right₀ hc] at hx' ⊢
    exact .inr (by simpa using hε' x hx hx')
  lattice_isZLattice := by
    use ?_; rw [← S.lattice_isZLattice.span_top]
    ext v; simp_rw [Submodule.mem_span]; refine ⟨fun h p hp ↦ ?_, fun h p hp ↦ ?_⟩
    · simpa [smul_smul, inv_mul_cancel₀ hc.ne.symm] using
        Submodule.smul_mem_pointwise_smul _ c⁻¹ _ (Submodule.smul_mem (c • p) c
          (h _ <| by rw [Submodule.coe_pointwise_smul]; exact Set.smul_set_mono hp))
    · simpa [smul_smul, mul_inv_cancel₀ hc.ne.symm] using
        Submodule.smul_mem_pointwise_smul _ c _ (Submodule.smul_mem (c⁻¹ • p) c⁻¹
          (h _ <| by
            rw [Submodule.coe_pointwise_smul] at *
            simpa [smul_smul, inv_mul_cancel₀ hc.ne.symm] using Set.smul_set_mono (a := c⁻¹) hp))
}

lemma SpherePacking.scale_balls {S : SpherePacking d} {c : ℝ} (hc : 0 < c) :
    (S.scale hc).balls = c • S.balls := by
  ext; simp [SpherePacking.balls, SpherePacking.scale, Set.smul_set_iUnion, Set.mem_smul_set,
    _root_.smul_ball hc.ne', Real.norm_eq_abs, abs_of_pos hc, mul_div_assoc]

lemma PeriodicSpherePacking.scale_balls {S : PeriodicSpherePacking d} {c : ℝ} (hc : 0 < c) :
    (S.scale hc).balls = c • S.balls := SpherePacking.scale_balls hc

end Scaling

noncomputable section Density
namespace SpherePacking

/-- Supremum of density over all periodic packings in dimension `d`. -/
@[expose] public def _root_.PeriodicSpherePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ S : PeriodicSpherePacking d, S.density

/-- Supremum of density over all packings in dimension `d`. -/
@[expose] public def _root_.SpherePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ S : SpherePacking d, S.density

@[simp]
public lemma scale_finiteDensity {d : ℕ} (S : SpherePacking d) {c : ℝ} (hc : 0 < c) (R : ℝ) :
    (S.scale hc).finiteDensity (c * R) = S.finiteDensity R := by
  rw [finiteDensity, scale_balls, show ball (0 : EuclideanSpace ℝ (Fin d)) (c * R) = c • ball 0 R by
      simpa [Real.norm_eq_abs, abs_of_pos hc, mul_assoc] using
        (smul_ball hc.ne.symm (0 : EuclideanSpace ℝ (Fin d)) R).symm,
    ← Set.smul_set_inter₀ hc.ne.symm,
    Measure.addHaar_smul_of_nonneg _ hc.le, Measure.addHaar_smul_of_nonneg _ hc.le,
    ENNReal.mul_div_mul_left _ _ (by simp; positivity) ENNReal.ofReal_ne_top, finiteDensity]

@[simp]
public lemma scale_finiteDensity' {d : ℕ} (S : SpherePacking d) {c : ℝ} (hc : 0 < c) (R : ℝ) :
    (S.scale hc).finiteDensity R = S.finiteDensity (R / c) := by
  simpa [mul_div_assoc', hc.ne.symm] using S.scale_finiteDensity hc (R := R / c)

public lemma scale_density {d : ℕ} (S : SpherePacking d) {c : ℝ} (hc : 0 < c) :
    (S.scale hc).density = S.density := by
  simpa [density, Function.comp, map_div_atTop_eq c hc] using
    (limsup_congr (.of_forall (S.scale_finiteDensity' hc))).trans
      (Filter.limsup_comp (u := S.finiteDensity) (v := (· / c)) (f := atTop))

public theorem constant_eq_constant_normalized {d : ℕ} :
    SpherePackingConstant d = ⨆ (S : SpherePacking d) (_ : S.separation = 1), S.density := by
  rw [iSup_subtype', SpherePackingConstant]
  refine le_antisymm (iSup_le fun S ↦ ?_) (iSup_le fun ⟨S, _⟩ ↦ le_iSup density S)
  simpa [scale_density] using
    le_iSup (fun S : { S : SpherePacking d // S.separation = 1 } ↦ S.val.density)
      ⟨S.scale (inv_pos.mpr S.separation_pos), inv_mul_cancel₀ S.separation_pos.ne.symm⟩

end SpherePacking
end Density

section BasicResults
open scoped ENNReal

variable {d : ℕ} (S : SpherePacking d)

lemma biUnion_inter_balls_subset_biUnion_balls_inter
    (X : Set (EuclideanSpace ℝ (Fin d))) (r R : ℝ) :
    ⋃ x ∈ X ∩ ball 0 R, ball x r ⊆ (⋃ x ∈ X, ball x r) ∩ ball 0 (R + r) := fun x hx => by
  simp only [Set.mem_inter_iff, Set.mem_iUnion, mem_ball, exists_prop, dist_zero_right] at hx ⊢
  obtain ⟨y, hy₁, hy₂⟩ := hx
  exact ⟨⟨y, hy₁.1, hy₂⟩, (norm_le_norm_add_norm_sub' x y).trans_lt (by gcongr <;> tauto)⟩

lemma biUnion_balls_inter_subset_biUnion_inter_balls
    (X : Set (EuclideanSpace ℝ (Fin d))) (r R : ℝ) :
    (⋃ x ∈ X, ball x r) ∩ ball 0 (R - r) ⊆ ⋃ x ∈ X ∩ ball 0 R, ball x r := fun x hx => by
  simp only [Set.mem_inter_iff, Set.mem_iUnion, mem_ball, exists_prop, dist_zero_right] at hx ⊢
  obtain ⟨⟨y, hy₁, hy₂⟩, hx⟩ := hx
  refine ⟨y, ⟨hy₁, ?_⟩, hy₂⟩
  rw [← sub_add_cancel R r]
  exact (norm_le_norm_add_norm_sub x y).trans_lt <|
    add_lt_add hx (by simpa [dist_eq_norm, norm_sub_rev] using hy₂)

theorem SpherePacking.volume_iUnion_balls_eq_tsum
    (R : ℝ) {r' : ℝ} (hr' : r' ≤ S.separation / 2) :
    volume (⋃ x : ↑(S.centers ∩ ball 0 R), ball (x : EuclideanSpace ℝ (Fin d)) r')
      = ∑' x : ↑(S.centers ∩ ball 0 R), volume (ball (x : EuclideanSpace ℝ (Fin d)) r') :=
  have _ : Countable ↑(S.centers ∩ ball 0 R) := Set.Countable.mono
    Set.inter_subset_left (countable_of_Lindelof_of_discrete (X := S.centers))
  measure_iUnion (fun ⟨x, hx⟩ ⟨y, hy⟩ h ↦ ball_disjoint_ball <| by
    linarith [S.centers_dist' x y hx.1 hy.1 (by simpa using h)]) fun _ ↦ measurableSet_ball

theorem SpherePacking.inter_ball_encard_le (R : ℝ) :
    (S.centers ∩ ball 0 R).encard ≤
      volume (S.balls ∩ ball 0 (R + S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) := by
  have h : volume _ ≤ volume _ := volume.mono <|
    biUnion_inter_balls_subset_biUnion_balls_inter S.centers (S.separation / 2) R
  simp_rw [Set.biUnion_eq_iUnion, S.volume_iUnion_balls_eq_tsum R le_rfl,
    Measure.addHaar_ball_center, ENNReal.tsum_set_const] at h
  rwa [← ENNReal.le_div_iff_mul_le
    (.inl (Metric.measure_ball_pos volume _ (by linarith [S.separation_pos])).ne.symm)
    (.inl MeasureTheory.measure_ball_lt_top.ne)] at h

theorem SpherePacking.inter_ball_encard_ge (R : ℝ) :
    (S.centers ∩ ball 0 R).encard ≥
      volume (S.balls ∩ ball 0 (R - S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) := by
  have h : volume _ ≤ volume _ := volume.mono <|
    biUnion_balls_inter_subset_biUnion_inter_balls S.centers (S.separation / 2) R
  simp_rw [Set.biUnion_eq_iUnion, S.volume_iUnion_balls_eq_tsum _ le_rfl,
    Measure.addHaar_ball_center, ENNReal.tsum_set_const] at h
  exact ENNReal.div_le_of_le_mul h

public theorem SpherePacking.finite_centers_inter_ball (R : ℝ) :
    Finite ↑(S.centers ∩ ball 0 R) :=
  Set.encard_lt_top_iff.mp <| ENat.toENNReal_lt.mp <|
    (S.inter_ball_encard_le R).trans_lt <| ENNReal.div_lt_top
      ((volume.mono Set.inter_subset_right).trans_lt measure_ball_lt_top).ne
      (Metric.measure_ball_pos volume _ (by linarith [S.separation_pos])).ne.symm

public theorem SpherePacking.finiteDensity_ge (_hd : 0 < d) (R : ℝ) :
    S.finiteDensity R ≥ (S.centers ∩ ball 0 (R - S.separation / 2)).encard
      * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
  rw [finiteDensity, balls]
  exact ENNReal.div_le_div_right ((ENNReal.le_div_iff_mul_le
    (.inl (Metric.measure_ball_pos volume _ (by linarith [S.separation_pos])).ne.symm)
    (.inl MeasureTheory.measure_ball_lt_top.ne)).1 <| by
      simpa [sub_add_cancel] using S.inter_ball_encard_le (R - S.separation / 2)) _

public theorem SpherePacking.finiteDensity_le (_hd : 0 < d) (R : ℝ) :
    S.finiteDensity R ≤ (S.centers ∩ ball 0 (R + S.separation / 2)).encard
      * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
  rw [finiteDensity, balls]
  exact ENNReal.div_le_div_right ((ENNReal.div_le_iff_le_mul
    (.inl (Metric.measure_ball_pos volume _ (by linarith [S.separation_pos])).ne.symm)
    (.inl MeasureTheory.measure_ball_lt_top.ne)).1 <| by
      simpa [add_sub_cancel_right] using S.inter_ball_encard_ge (R + S.separation / 2)) _

end BasicResults
