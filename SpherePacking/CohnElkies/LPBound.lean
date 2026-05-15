/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Relator
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Trigonometric

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.RCLike.Inner
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular

public import SpherePacking.Basic.PeriodicPacking.Aux
public import SpherePacking.CohnElkies.PoissonSummationGeneral
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Combinatorics.Pigeonhole

/-!
# Cohn-Elkies linear programming bound

Cohn-Elkies upper bound on `SpherePackingConstant d` via `LinearProgrammingBound`. Also contains
the periodizing constructions and boundary-control machinery (merged from `BoundaryControl`):
`periodizedCenters`, `periodize_to_periodicSpherePacking`, `coordCube`/`coordCubeInner`, the cube
lattice `cubeLattice`, and the main result `periodic_constant_eq_constant`.
-/

section PeriodicPackingBoundaryControl

open scoped ENNReal Pointwise Topology BigOperators
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module Filter

variable {d : ℕ}

/-- Any coordinate of a vector is bounded in absolute value by the Euclidean norm. -/
public lemma abs_coord_le_norm (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |x i| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by
    have hsq : (x.ofLp i) ^ 2 = ‖x.ofLp i‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    rw [hsq]
    exact Finset.single_le_sum (f := fun j : Fin d => ‖x.ofLp j‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i))

/-- If `ball x r ⊆ A` and `ball y r ⊆ B` with `A` and `B` disjoint, then `2 * r ≤ dist x y`. -/
public lemma dist_le_of_disjoint_ball_subsets {x y : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    {A B : Set (EuclideanSpace ℝ (Fin d))}
    (hx : ball x r ⊆ A) (hy : ball y r ⊆ B) (hAB : Disjoint A B) : 2 * r ≤ dist x y := by
  by_contra hlt
  refine Set.disjoint_left.1 hAB (hx (a := midpoint ℝ x y) ?_) (hy (a := midpoint ℝ x y) ?_) <;>
    simpa [Metric.mem_ball, dist_comm] using
      (by nlinarith [lt_of_not_ge hlt] : (1 / 2 : ℝ) * dist x y < r)

/-- The union of all lattice translates of a set `F` of representatives. -/
@[expose] public noncomputable def periodizedCenters (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    (F : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) := ⋃ g : Λ, g +ᵥ F

/-- Membership in `periodizedCenters` is equivalent to being a translate of a point in `F`. -/
public lemma mem_periodizedCenters_iff {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {F : Set (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)} :
    x ∈ periodizedCenters (d := d) Λ F ↔ ∃ g : Λ, ∃ f ∈ F, x = g +ᵥ f := by
  simp [periodizedCenters, Set.mem_vadd_set, eq_comm]

/-- `periodizedCenters` is closed under addition by lattice vectors. -/
public lemma periodizedCenters_lattice_action {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {F : Set (EuclideanSpace ℝ (Fin d))} {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ Λ) (hy : y ∈ periodizedCenters (d := d) Λ F) :
    x + y ∈ periodizedCenters (d := d) Λ F := by
  rcases mem_periodizedCenters_iff.1 hy with ⟨g, f, hf, rfl⟩
  exact mem_periodizedCenters_iff.2
    ⟨⟨x, hx⟩ + g, f, hf, by simp [Submodule.vadd_def, vadd_eq_add, add_assoc]⟩

/-- Translating a ball by a lattice vector stays inside the translate of the ambient set. -/
public lemma ball_vadd_subset_vadd {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {D : Set (EuclideanSpace ℝ (Fin d))} {r : ℝ} {g : Λ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : ball x r ⊆ D) : ball (g +ᵥ x) r ⊆ g +ᵥ D := fun y hy =>
  ⟨(- (g : EuclideanSpace ℝ (Fin d))) +ᵥ y, hx <| by
    simpa [Metric.mem_ball, dist_eq_norm, Submodule.vadd_def, vadd_eq_add, sub_eq_add_neg,
      add_assoc, add_comm, add_left_comm] using hy, by simp [vadd_eq_add]⟩

/-- Construct a periodic sphere packing by translating a set of representatives `F ⊆ S.centers`
along a lattice `Λ`. -/
@[expose] public noncomputable def periodize_to_periodicSpherePacking
    (S : SpherePacking d)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (D F : Set (EuclideanSpace ℝ (Fin d)))
    (hD_unique_covers : ∀ x, ∃! g : Λ, g +ᵥ x ∈ D) (hF_centers : F ⊆ S.centers)
    (hF_ball : ∀ x ∈ F, ball x (S.separation / 2) ⊆ D) : PeriodicSpherePacking d where
  centers := periodizedCenters (d := d) Λ F
  separation := S.separation
  separation_pos := S.separation_pos
  centers_dist := fun a b hab => by
    change S.separation ≤ dist (a : EuclideanSpace ℝ (Fin d)) (b : EuclideanSpace ℝ (Fin d))
    rcases mem_periodizedCenters_iff.1 a.property with ⟨ga, fa, hfa, ha⟩
    rcases mem_periodizedCenters_iff.1 b.property with ⟨gb, fb, hfb, hb⟩
    by_cases hgg : ga = gb
    · subst hgg
      simpa [ha, hb] using (dist_vadd_cancel_left (ga : EuclideanSpace ℝ (Fin d)) fa fb).symm ▸
        S.centers_dist' fa fb (hF_centers hfa) (hF_centers hfb)
          (fun h => hab <| Subtype.ext <| by simp [ha, hb, h])
    · simpa [ha, hb, two_mul, add_halves] using dist_le_of_disjoint_ball_subsets
        (ball_vadd_subset_vadd (hF_ball fa hfa)) (ball_vadd_subset_vadd (hF_ball fb hfb))
        (disjoint_vadd_of_unique_covers (D := D) hD_unique_covers hgg)
  lattice := Λ
  lattice_action := fun _ _ ↦ periodizedCenters_lattice_action
  lattice_discrete := inferInstance
  lattice_isZLattice := inferInstance

/-- The coordinate cube `[0,L)^d` as a set in `EuclideanSpace`. -/
@[expose] public def coordCube (d : ℕ) (L : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, x i ∈ Set.Ico (0 : ℝ) L}

/-- The "inner cube" `[r, L-r]^d` (closed intervals) used to keep radius-`r` balls inside
`coordCube L`. -/
@[expose] public def coordCubeInner (d : ℕ) (L r : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, x i ∈ Set.Icc r (L - r)}

/-- A scaled basis used to realize `coordCube L` as a fundamental domain. -/
@[expose] public noncomputable def cubeBasis (d : ℕ) (L : ℝ) (hL : 0 < L) :
    Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis).isUnitSMul
    (fun _ : Fin d ↦ IsUnit.mk0 L (ne_of_gt hL))

/-- The lattice generated by `cubeBasis L hL`. -/
@[expose] public noncomputable def cubeLattice (d : ℕ) (L : ℝ) (hL : 0 < L) :
    Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℤ (Set.range (cubeBasis d L hL))

instance instDiscreteTopology_cubeLattice (L : ℝ) (hL : 0 < L) :
    DiscreteTopology (cubeLattice d L hL) := by
  change DiscreteTopology (Submodule.span ℤ (Set.range (cubeBasis d L hL)))
  infer_instance

instance instIsZLattice_cubeLattice (L : ℝ) (hL : 0 < L) :
    IsZLattice ℝ (cubeLattice d L hL) := by dsimp [cubeLattice]; infer_instance

public lemma fundamentalDomain_cubeBasis_eq_coordCube (L : ℝ) (hL : 0 < L) :
    fundamentalDomain (cubeBasis d L hL) = coordCube d L := by
  ext x
  simp only [ZSpan.mem_fundamentalDomain, coordCube, cubeBasis, Module.Basis.repr_isUnitSMul,
    Units.smul_def, Units.val_inv_eq_inv_val, Set.mem_setOf_eq, Set.mem_Ico]
  refine ⟨fun hx i => ?_, fun hx i => ?_⟩ <;> specialize hx i
  · exact ⟨by simpa [mul_inv_cancel₀ hL.ne'] using
        (by simpa [mul_assoc] using mul_nonneg hL.le hx.1 : 0 ≤ (L * L⁻¹) * x.ofLp i),
      by simpa [mul_inv_cancel₀ hL.ne'] using
        (by simpa [mul_assoc] using mul_lt_mul_of_pos_left hx.2 hL :
          (L * L⁻¹) * x.ofLp i < (L : ℝ) * 1)⟩
  · exact ⟨mul_nonneg (inv_pos.mpr hL).le hx.1,
      by simpa [mul_assoc, inv_mul_cancel₀ hL.ne'] using mul_lt_mul_of_pos_left hx.2 (inv_pos.mpr hL)⟩

lemma ball_subset_coordCube_of_mem_inner {L r : ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ coordCubeInner d L r) : ball x r ⊆ coordCube d L := fun y hy i => by
  have hsub := abs_lt.mp <| lt_of_le_of_lt (by simpa using abs_coord_le_norm (d := d) (y - x) i :
    |y i - x i| ≤ ‖y - x‖)
    (by simpa [Metric.mem_ball, dist_eq_norm, dist_comm] using hy : ‖y - x‖ < r)
  refine ⟨?_, ?_⟩ <;> linarith [(hx i).1, (hx i).2, hsub.1, hsub.2]

public lemma periodizedCenters_inter_eq_of_subset {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {D F : Set (EuclideanSpace ℝ (Fin d))}
    (hF_sub : F ⊆ D) (hD_unique_covers : ∀ x, ∃! g : Λ, g +ᵥ x ∈ D) :
    periodizedCenters (d := d) Λ F ∩ D = F := by
  ext x
  have zvadd : ∀ y : EuclideanSpace ℝ (Fin d), (0 : ↥Λ) +ᵥ y = y := fun y => zero_vadd _ _
  refine ⟨?_, fun hxF => ⟨mem_periodizedCenters_iff.2 ⟨0, x, hxF, (zvadd x).symm⟩, hF_sub hxF⟩⟩
  rintro ⟨⟨_, ⟨g, rfl⟩, ⟨f, hfF, rfl⟩⟩, hxD⟩
  obtain ⟨_, _, hg0uniq⟩ := hD_unique_covers f
  have hg0g : g = 0 := by
    have h1 : (fun g ↦ g +ᵥ f ∈ D) g := hxD
    have h2 : (fun g ↦ g +ᵥ f ∈ D) (0 : ↥Λ) := by
      change (0 : ↥Λ) +ᵥ f ∈ D
      rw [zvadd]; exact hF_sub hfF
    exact (hg0uniq g h1).trans (hg0uniq 0 h2).symm
  rw [hg0g]
  change (0 : ↥Λ) +ᵥ f ∈ F
  rw [zvadd]
  exact hfF

namespace PeriodicConstant

private lemma volume_preimage_ofLp (s : Set (Fin d → ℝ)) (hs : MeasurableSet s) :
    volume ((fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹' s) = volume s := by
  simpa using (PiLp.volume_preserving_ofLp (ι := Fin d)).measure_preimage hs.nullMeasurableSet

public lemma coordCube_unique_covers (L : ℝ) (hL : 0 < L) :
    ∀ x, ∃! g : cubeLattice d L hL, g +ᵥ x ∈ coordCube d L := fun x => by
  simpa [cubeLattice, fundamentalDomain_cubeBasis_eq_coordCube L hL] using
    exist_unique_vadd_mem_fundamentalDomain (cubeBasis d L hL) x

public lemma isBounded_coordCube (L : ℝ) (hL : 0 < L) : IsBounded (coordCube d L) := by
  simpa [fundamentalDomain_cubeBasis_eq_coordCube L hL] using
    fundamentalDomain_isBounded (cubeBasis d L hL)

public lemma volume_coordCube (L : ℝ) : volume (coordCube d L) = (ENNReal.ofReal L) ^ d := by
  rw [show coordCube d L = (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
        (Set.pi Set.univ fun _ : Fin d ↦ Set.Ico (0 : ℝ) L) from
      Set.ext fun x => by simp [coordCube, Set.mem_pi],
    volume_preimage_ofLp _
      (.pi Set.countable_univ fun _ _ ↦ measurableSet_Ico), volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico, sub_zero]

public lemma coordCubeInner_eq_preimage_ofLp (L r : ℝ) :
    coordCubeInner d L r =
      (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
        (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc r (L - r)) := by
  ext x; simp [coordCubeInner, Pi.le_def, forall_and]

public lemma volume_coordCubeInner (L r : ℝ) :
    volume (coordCubeInner d L r) = (ENNReal.ofReal (L - 2 * r)) ^ d := by
  rw [coordCubeInner_eq_preimage_ofLp, volume_preimage_ofLp _
    (.pi Set.countable_univ fun _ _ ↦ measurableSet_Icc), volume_pi, Measure.pi_pi]
  simp [Real.volume_Icc, sub_eq_add_neg, add_left_comm, add_comm, two_mul]

end PeriodicConstant

namespace PeriodicConstantApprox

public lemma coordCube_unique_covers_vadd (L : ℝ) (hL : 0 < L) (v : cubeLattice d L hL) :
    ∀ x, ∃! g : cubeLattice d L hL, g +ᵥ x ∈ v +ᵥ coordCube d L := fun x => by
  have hvadd (a : cubeLattice d L hL) :
      a +ᵥ x ∈ v +ᵥ coordCube d L ↔ (a - v) +ᵥ x ∈ coordCube d L := by
    simp [Set.mem_vadd_set_iff_neg_vadd_mem, Submodule.vadd_def, vadd_eq_add, sub_eq_add_neg,
      add_assoc, add_comm]
  obtain ⟨g, hg, hguniq⟩ := PeriodicConstant.coordCube_unique_covers (d := d) L hL x
  exact ⟨g + v, (hvadd _).2 (by simpa), fun _ ha => sub_eq_iff_eq_add.1 (hguniq _ <| (hvadd _).1 ha)⟩

public lemma ball_subset_vadd_coordCube_of_mem_vadd_inner {L r : ℝ} (hL : 0 < L)
    {v : cubeLattice d L hL} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ v +ᵥ coordCubeInner d L r) :
    ball x r ⊆ v +ᵥ coordCube d L := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hball : ball y r ⊆ coordCube d L := ball_subset_coordCube_of_mem_inner hy
  intro z hz
  refine ⟨z - v, hball ?_, by simp [vadd_eq_add]⟩
  change dist z ((v : EuclideanSpace ℝ (Fin d)) + y) < r at hz
  rw [mem_ball, dist_eq_norm, show z - ↑v - y = z - (↑v + y) from by abel, ← dist_eq_norm]
  exact hz

public lemma finite_lattice_in_ball (L : ℝ) (hL : 0 < L) (R : ℝ) :
    Set.Finite {g : cubeLattice d L hL | (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 R} := by
  refine (Set.Finite.preimage_embedding (f := ⟨fun g : cubeLattice d L hL =>
    (g : EuclideanSpace ℝ (Fin d)), Subtype.val_injective⟩) (by
      simpa [cubeLattice] using ZSpan.setFinite_inter (b := cubeBasis d L hL)
        (s := ball (0 : EuclideanSpace ℝ (Fin d)) R) Metric.isBounded_ball)).subset fun g hg => ?_
  exact ⟨hg, g.property⟩

section CoordCubeCover

variable (L : ℝ) (hL : 0 < L)

noncomputable def coordCubeCover (x : EuclideanSpace ℝ (Fin d)) : cubeLattice d L hL :=
  Classical.choose (PeriodicConstant.coordCube_unique_covers L hL x)

lemma coordCubeCover_spec (x : EuclideanSpace ℝ (Fin d)) :
    coordCubeCover L hL x +ᵥ x ∈ coordCube d L :=
  (Classical.choose_spec (PeriodicConstant.coordCube_unique_covers L hL x)).1

lemma neg_coordCubeCover_mem_ball {C R : ℝ}
    (hC : coordCube d L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ ball 0 R) :
    ((-coordCubeCover L hL x : cubeLattice d L hL) :
        EuclideanSpace ℝ (Fin d)) ∈ ball 0 (R + C) := by
  set g := (coordCubeCover L hL x : EuclideanSpace ℝ (Fin d))
  rw [mem_ball_zero_iff, show ((-coordCubeCover L hL x : cubeLattice d L hL) :
    EuclideanSpace ℝ (Fin d)) = -g from rfl, norm_neg]
  linarith [show ‖x‖ < R by simpa [mem_ball_zero_iff] using hx,
    show ‖g + x‖ < C by simpa [mem_ball_zero_iff] using hC (by
      simpa [Submodule.vadd_def, vadd_eq_add] using coordCubeCover_spec L hL x),
    show ‖g‖ ≤ ‖g + x‖ + ‖x‖ by simpa [add_sub_cancel_right] using norm_sub_le (g + x) x]

end CoordCubeCover

lemma card_finite_lattice_in_ball_mul_volume_coordCube_le_volume_ball {L : ℝ} (hL : 0 < L)
    {R C : ℝ} (hC : coordCube d L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C) :
    let htSet :=
      PeriodicConstantApprox.finite_lattice_in_ball (d := d) L hL (R + C)
    let t : Finset (cubeLattice d L hL) := htSet.toFinset
    (t.card : ℝ≥0∞) * volume (coordCube d L) ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C))) := by
  intro htSet t
  haveI hvi : VAddInvariantMeasure (↥(cubeLattice d L hL)) (EuclideanSpace ℝ (Fin d))
      (MeasureTheory.volume) :=
    inferInstanceAs (VAddInvariantMeasure (cubeLattice d L hL).toAddSubgroup _ _)
  haveI hmcv : MeasurableConstVAdd (↥(cubeLattice d L hL)) (EuclideanSpace ℝ (Fin d)) :=
    ⟨fun _ => measurable_const_vadd _⟩
  have hvadd : ∀ g : ↥(cubeLattice d L hL),
      volume (g +ᵥ coordCube d L) = volume (coordCube d L) :=
    fun g => @measure_vadd _ _ _ _ _ MeasureTheory.volume hvi g (coordCube d L)
  have hms : MeasurableSet (coordCube d L) := by
    rw [show coordCube d L = fundamentalDomain (cubeBasis d L hL) from
      (fundamentalDomain_cubeBasis_eq_coordCube L hL).symm]
    exact fundamentalDomain_measurableSet _
  calc (↑t.card : ℝ≥0∞) * volume (coordCube d L)
      = ∑ g ∈ t, volume (g +ᵥ coordCube d L) := by
        simp_rw [hvadd, Finset.sum_const]
        rw [nsmul_eq_mul]
    _ = volume (⋃ g ∈ t, g +ᵥ coordCube d L) := (measure_biUnion_finset
        (fun _ _ _ _ hgh => disjoint_vadd_of_unique_covers (d := d)
          (PeriodicConstant.coordCube_unique_covers L hL) hgh)
        (fun g _ => @MeasurableSet.const_vadd _ _ _ _ _ hmcv _ hms g)).symm
    _ ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C))) := volume.mono <| by
        rintro y hy
        obtain ⟨g, hgT, x, hx, rfl⟩ := Set.mem_iUnion₂.1 hy
        have hg : (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 (R + C) :=
          htSet.mem_toFinset.1 (by simpa [t] using hgT)
        simp only [vadd_eq_add, mem_ball_zero_iff]
        linarith [norm_add_le (g : EuclideanSpace ℝ (Fin d)) x,
          mem_ball_zero_iff.mp (hC hx), mem_ball_zero_iff.mp hg]

section BoundaryControl

def constVec (d : ℕ) (c : ℝ) : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun _ : Fin d => c)

lemma coordCube_boundary_half_add_ball_subset_outer_diff_inner (L : ℝ) :
    ((coordCube d L \ coordCubeInner d L (1 / 2)) +
        ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
      ⊆ ((constVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner d (L + 1) 0) \
        coordCubeInner d L 1 := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  have hyi : ∀ i : Fin d, |y i| < (1 / 2 : ℝ) := fun i =>
    (abs_coord_le_norm y i).trans_lt (by simpa [mem_ball_zero_iff] using hy)
  refine ⟨Set.mem_vadd_set_iff_neg_vadd_mem.2 fun i => ?_, fun hz_inner => ?_⟩
  · simp only [coordCubeInner, coordCube, constVec, vadd_eq_add] at hx ⊢
    refine ⟨by simpa [add_assoc, add_left_comm, add_comm] using
      (by linarith [(hx.1 i).1, abs_lt.mp (hyi i)] : (0:ℝ) ≤ x i + y i + (1/2:ℝ)),
      by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (by linarith [(hx.1 i).2.le, abs_lt.mp (hyi i)] : x i + y i + (1/2:ℝ) ≤ L + 1)⟩
  · obtain ⟨i, hi⟩ : ∃ i : Fin d, ¬ x i ∈ Set.Icc (1 / 2 : ℝ) (L - 1 / 2) := by
      simpa [coordCubeInner, Set.mem_setOf_eq] using not_forall.mp hx.2
    rw [Set.mem_Icc, not_and_or] at hi
    have hz_i : (x i + y i) ∈ Set.Icc (1 : ℝ) (L - 1) := by
      simpa [coordCubeInner, Set.mem_setOf_eq] using hz_inner i
    obtain hi | hi := hi <;> linarith [hz_i.1, hz_i.2, abs_lt.mp (hyi i)]

variable (S : SpherePacking d)

lemma card_mul_volume_ball_le_volume_outer_diff_inner {L : ℝ} (hL : 0 < L)
    (hSsep : S.separation = 1)
    {g : cubeLattice d L hL} {s : Finset (EuclideanSpace ℝ (Fin d))}
    (hs_centers : ∀ x ∈ s, x ∈ S.centers)
    (hs_boundary : ∀ x ∈ s,
      x ∈ (g +ᵥ coordCube d L) \ (g +ᵥ coordCubeInner d L (1 / 2))) :
    (s.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ)) ≤
      volume (((constVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner d (L + 1) 0) \
        coordCubeInner d L 1) := by
  let r : ℝ := (1 / 2 : ℝ)
  have hdisj : (s : Set (EuclideanSpace ℝ (Fin d))).PairwiseDisjoint fun x => ball x r :=
    fun x hx y hy hxy => ball_disjoint_ball (by
      dsimp [r]; linarith [show (1 : ℝ) ≤ dist x y by
        simpa [hSsep] using S.centers_dist' x y (hs_centers x hx) (hs_centers y hy) hxy])
  have hsub : (⋃ x ∈ s, ball x r) ⊆
      g +ᵥ (((constVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner d (L + 1) 0) \
            coordCubeInner d L 1) := fun y hy => by
    obtain ⟨x, hxS, hyBall⟩ : ∃ x ∈ s, y ∈ ball x r := by simpa using hy
    have hxB := hs_boundary x hxS
    set x0 : EuclideanSpace ℝ (Fin d) := (-(g : EuclideanSpace ℝ (Fin d))) +ᵥ x
    set y0 : EuclideanSpace ℝ (Fin d) := (-(g : EuclideanSpace ℝ (Fin d))) +ᵥ y
    have hvadd_eq : ∀ (v w : EuclideanSpace ℝ (Fin d)) (S : Set (EuclideanSpace ℝ (Fin d))),
        v ∈ ((g : EuclideanSpace ℝ (Fin d)) +ᵥ S) ↔ -(g : EuclideanSpace ℝ (Fin d)) +ᵥ v ∈ S :=
      fun v w S => Set.mem_vadd_set_iff_neg_vadd_mem
    have hxB1' : x0 ∈ coordCube d L := by
      have : x ∈ (g : EuclideanSpace ℝ (Fin d)) +ᵥ coordCube d L := hxB.1
      rwa [Set.mem_vadd_set_iff_neg_vadd_mem] at this
    have hxB2' : x0 ∉ coordCubeInner d L (1/2) := fun h => hxB.2 (by
      rwa [Set.mem_vadd_set_iff_neg_vadd_mem])
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, y0] using
      coordCube_boundary_half_add_ball_subset_outer_diff_inner (d := d) L
        (by simpa [r] using (show y0 ∈ (coordCube d L \ coordCubeInner d L (1 / 2)) +
            ball (0 : EuclideanSpace ℝ (Fin d)) r from
          ⟨x0, ⟨hxB1', hxB2'⟩,
            y0 - x0,
            by simpa [Metric.mem_ball, dist_eq_norm, Metric.vadd_ball, x0, y0] using hyBall,
            by simp [sub_eq_add_neg, add_left_comm]⟩))
  calc (s.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ))
      = volume (⋃ x ∈ s, ball x r) := by
        rw [show (2⁻¹ : ℝ) = r by norm_num]
        simpa [Measure.addHaar_ball_center, mul_comm, mul_assoc] using
          (measure_biUnion_finset (μ := volume) hdisj (fun _ _ => measurableSet_ball)).symm
    _ ≤ volume (g +ᵥ (((constVec d (-(1 / 2 : ℝ))) +ᵥ coordCubeInner d (L + 1) 0) \
          coordCubeInner d L 1)) := volume.mono hsub
    _ = _ := by simp [measure_vadd]

end BoundaryControl

lemma volume_cubeShell_eq_pow (L : ℝ) :
    volume (((constVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner d (L + 1) 0) \
        coordCubeInner d L 1) =
      (ENNReal.ofReal (L + 1)) ^ d - (ENNReal.ofReal (L - 2)) ^ d := by
  simpa [measure_vadd, constVec, PeriodicConstant.volume_coordCubeInner] using
    measure_diff (μ := volume) (fun x hx => Set.mem_vadd_set_iff_neg_vadd_mem.2 fun i => by
      simp only [coordCubeInner, Set.mem_setOf_eq, constVec, vadd_eq_add, one_div,
        WithLp.ofLp_add, WithLp.ofLp_neg, Pi.add_apply, Pi.neg_apply, neg_neg] at hx ⊢
      exact ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩ :
    coordCubeInner d L 1 ⊆ (constVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner d (L + 1) 0)
      (show MeasurableSet (coordCubeInner d L 1) by
        simpa [PeriodicConstant.coordCubeInner_eq_preimage_ofLp] using
          (MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Icc).preimage
            (PiLp.volume_preserving_ofLp (ι := Fin d)).measurable).nullMeasurableSet
      (by simp [PeriodicConstant.volume_coordCubeInner])

lemma toNNReal_covolume_cubeLattice (L : ℝ) (hL : 0 < L) :
    Real.toNNReal (ZLattice.covolume (cubeLattice d L hL) volume) =
      (volume (coordCube d L)).toNNReal := by
  simp [show ZLattice.covolume (cubeLattice d L hL) volume = (volume (coordCube d L)).toReal by
    simpa [Measure.real, fundamentalDomain_cubeBasis_eq_coordCube L hL] using
      ZLattice.covolume_eq_measure_fundamentalDomain (L := cubeLattice d L hL) (μ := volume)
        (by simpa [cubeLattice] using ZSpan.isAddFundamentalDomain (cubeBasis d L hL) volume :
          IsAddFundamentalDomain (cubeLattice d L hL)
            (fundamentalDomain (cubeBasis d L hL)) volume)]

lemma periodize_cube_density_eq (hd : 0 < d) (S : SpherePacking d) (hSsep : S.separation = 1)
    {L : ℝ} (hL : 0 < L) {g : cubeLattice d L hL}
    (F : Finset (EuclideanSpace ℝ (Fin d)))
    (hF_centers : ∀ x ∈ F, x ∈ S.centers)
    (hF_inner : ∀ x ∈ F, x ∈ g +ᵥ coordCubeInner d L (2⁻¹ : ℝ)) :
    ∃ P : PeriodicSpherePacking d, P.separation = 1 ∧ P.density =
        (F.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ)) /
          Real.toNNReal (ZLattice.covolume (cubeLattice d L hL) volume) := by
  let D : Set (EuclideanSpace ℝ (Fin d)) := g +ᵥ coordCube d L
  let Fset : Set (EuclideanSpace ℝ (Fin d)) := (F : Set (EuclideanSpace ℝ (Fin d)))
  have hD_unique := PeriodicConstantApprox.coordCube_unique_covers_vadd L hL g
  let P : PeriodicSpherePacking d :=
    periodize_to_periodicSpherePacking (d := d) S (Λ := cubeLattice d L hL) D Fset
      (hD_unique_covers := hD_unique) (hF_centers := by assumption)
      (hF_ball := fun x hx => ball_subset_vadd_coordCube_of_mem_vadd_inner hL <| by
        simpa [hSsep] using hF_inner x (by simpa [Fset] using hx))
  have hPsep : P.separation = 1 := by simpa [P, hSsep]
  have hnumReps : P.numReps = F.card := by
    exact_mod_cast show (P.numReps : ENat) = (F.card : ENat) by
      simpa [show P.centers ∩ D = Fset by
        simpa [P, periodize_to_periodicSpherePacking, Fset] using
          periodizedCenters_inter_eq_of_subset (d := d) (Λ := cubeLattice d L hL) (D := D)
            (F := Fset) (fun x hx => by
              rcases hF_inner x (by simpa [Fset] using hx) with ⟨a, ha, rfl⟩
              exact ⟨a, fun i => ⟨(by norm_num : (0:ℝ) < _).le.trans (ha i).1,
                (ha i).2.trans_lt (sub_lt_self _ (by norm_num))⟩, rfl⟩)
            hD_unique, Fset, Set.encard_coe_eq_coe_finsetCard] using
        (P.encard_centers_inter_isFundamentalDomain (d := d) (D := D)
          (by simpa [D, Submodule.vadd_def, vadd_eq_add] using
            (PeriodicConstant.isBounded_coordCube L hL).vadd (g : EuclideanSpace ℝ (Fin d)) :
            IsBounded D) hD_unique hd).symm
  exact ⟨P, hPsep, by simpa [hnumReps, hPsep] using P.density_eq' (d := d) hd⟩

lemma tendsto_volume_cubeShell_div_volume_coordCube_zero :
    Tendsto
        (fun L : ℝ =>
          volume (((constVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner d (L + 1) 0) \
              coordCubeInner d L 1) /
            volume (coordCube d L))
        atTop (𝓝 (0 : ℝ≥0∞)) := by
  let f : ℝ → ℝ := fun L : ℝ => ((L + 1) ^ d - (L - 2) ^ d) / (L ^ d)
  have hf : Tendsto f atTop (𝓝 (0 : ℝ)) := by
    have h1 : Tendsto (fun L : ℝ => (1 + L⁻¹) ^ d) atTop (𝓝 (1 : ℝ)) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add tendsto_inv_atTop_zero).pow d
    have h2 : Tendsto (fun L : ℝ => (1 - 2 * L⁻¹) ^ d) atTop (𝓝 (1 : ℝ)) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub
        ((tendsto_const_nhds (x := (2 : ℝ))).mul tendsto_inv_atTop_zero)).pow d
    refine (by simpa using h1.sub h2 :
      Tendsto (fun L : ℝ => (1 + L⁻¹) ^ d - (1 - 2 * L⁻¹) ^ d) atTop (𝓝 (0 : ℝ))).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L _
    change (1 + L⁻¹) ^ d - (1 - 2 * L⁻¹) ^ d = ((L + 1) ^ d - (L - 2) ^ d) / (L ^ d)
    rw [sub_div]; congr 1 <;> rw [← div_pow] <;> congr 1 <;> field_simp
  refine (show Tendsto (fun L : ℝ => ENNReal.ofReal (f L)) atTop (𝓝 (0 : ℝ≥0∞)) by
    simpa using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hf).congr' ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with L hL2
  have hL2' : 0 ≤ L - 2 := by linarith
  rw [volume_cubeShell_eq_pow L, show volume (coordCube d L) = (ENNReal.ofReal L) ^ d by
      simpa using PeriodicConstant.volume_coordCube L,
    ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ L + 1), ← ENNReal.ofReal_pow hL2',
    ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ L), ← ENNReal.ofReal_sub _ (pow_nonneg hL2' d)]
  simpa [f] using ENNReal.ofReal_div_of_pos (x := (L + 1)^d - (L - 2)^d) (pow_pos (by linarith) d)

end PeriodicConstantApprox

namespace SpherePacking

theorem exists_periodicSpherePacking_sep_one_density_gt_of_lt_density (hd : 0 < d)
    (S : SpherePacking d) (hSsep : S.separation = 1) {b : ℝ≥0∞} (hb : b < S.density) :
    ∃ P : PeriodicSpherePacking d, P.separation = 1 ∧ b < P.density := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  obtain ⟨c, hbc, hcS⟩ := exists_between hb
  let cubeShellErr : ℝ → ℝ≥0∞ := fun L : ℝ =>
    volume (((PeriodicConstantApprox.constVec (d := d) (- (1 / 2 : ℝ))) +ᵥ
        coordCubeInner d (L + 1) 0) \ coordCubeInner d L 1) /
      volume (coordCube d L)
  obtain ⟨L, hLpos, hLerr⟩ := ((eventually_gt_atTop (0 : ℝ)).and
      (((by simpa [cubeShellErr] using
          PeriodicConstantApprox.tendsto_volume_cubeShell_div_volume_coordCube_zero :
        Tendsto cubeShellErr atTop (𝓝 (0 : ℝ≥0∞)))).eventually
          (Iio_mem_nhds (tsub_pos_of_lt hbc)))).exists
  obtain ⟨C, hC⟩ : ∃ C : ℝ, coordCube d L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C := by
    simpa using (PeriodicConstant.isBounded_coordCube L hLpos).subset_ball 0
  have hCpos : 0 < C := by
    simpa [Metric.mem_ball, dist_eq_norm] using
      hC (by simp [coordCube, hLpos] : (0 : EuclideanSpace ℝ (Fin d)) ∈ coordCube d L)
  let r : ℝ := (2⁻¹ : ℝ); let Cshift : ℝ := r + 2 * C
  let ratio : ℝ → ℝ≥0∞ := fun R : ℝ =>
    volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) /
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift))
  obtain ⟨R, hcR, hRpos, hRratio⟩ :=
      ((frequently_lt_of_lt_limsup (h := by simpa [SpherePacking.density] using hcS) :
        ∃ᶠ R in (atTop : Filter ℝ), c < S.finiteDensity R).and_eventually
      ((eventually_gt_atTop (0 : ℝ)).and
        ((show Tendsto (fun R : ℝ => c * ratio R) atTop (𝓝 c) by
          simpa [mul_one] using ENNReal.Tendsto.const_mul (a := c)
            (by simpa [ratio, Cshift, add_zero] using
              volume_ball_ratio_tendsto_nhds_one'' (C := (0 : ℝ)) (C' := Cshift) hd :
              Tendsto ratio atTop (𝓝 (1 : ℝ≥0∞)))).eventually
          (Ioi_mem_nhds (lt_tsub_iff_left.mp hLerr : b + cubeShellErr L < c))))).exists
  let volBall : ℝ≥0∞ := volume (ball (0 : EuclideanSpace ℝ (Fin d)) r)
  let volCube : ℝ≥0∞ := volume (coordCube d L)
  let shellVol : ℝ≥0∞ :=
    volume (((PeriodicConstantApprox.constVec (d := d) (- (1 / 2 : ℝ))) +ᵥ
        coordCubeInner d (L + 1) 0) \ coordCubeInner d L 1)
  have hvolCube_ne0 : volCube ≠ 0 := by
    simpa [volCube, PeriodicConstant.volume_coordCube L] using
      pow_ne_zero d (ENNReal.ofReal_pos.mpr hLpos).ne'
  have hvolCube_ne_top : volCube ≠ ∞ :=
    (PeriodicConstant.isBounded_coordCube L hLpos).measure_lt_top.ne
  have hc_ratio : c * ratio R <
      ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) * volBall /
        volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) := by
    simpa [ratio, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      ENNReal.div_lt_div_right
        ((Metric.measure_ball_pos volume _ (by positivity)).ne.symm :
          volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) ≠ 0)
        (MeasureTheory.measure_ball_lt_top (μ := volume)).ne
        (ENNReal.mul_lt_of_lt_div <| hcR.trans_le <| by simpa [hSsep, volBall, r, add_assoc,
          add_left_comm, add_comm] using S.finiteDensity_le hd R :
        c * volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) <
        ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) * volBall)
  let R₁ : ℝ := R + r
  have hX : (S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R₁).Finite :=
    SpherePacking.finite_centers_inter_ball S R₁
  let s : Finset (EuclideanSpace ℝ (Fin d)) := hX.toFinset
  let htSet := PeriodicConstantApprox.finite_lattice_in_ball (d := d) L hLpos (R₁ + C)
  let t : Finset (cubeLattice d L hLpos) := htSet.toFinset
  let f : EuclideanSpace ℝ (Fin d) → cubeLattice d L hLpos := fun x =>
    -PeriodicConstantApprox.coordCubeCover L hLpos x
  have hf_maps : (s : Set (EuclideanSpace ℝ (Fin d))).MapsTo f t := fun _ hx =>
    htSet.mem_toFinset.2 <|
      PeriodicConstantApprox.neg_coordCubeCover_mem_ball L hLpos hC (hX.mem_toFinset.1 hx).2
  obtain ⟨g0, _, hg0max⟩ := Finset.exists_max_image t (fun g => (s.filter fun x => f x = g).card)
    ⟨0, htSet.mem_toFinset.2 (by simp [Metric.mem_ball]; positivity)⟩
  let sg : Finset (EuclideanSpace ℝ (Fin d)) := s.filter fun x => f x = g0
  have hsg_centers : ∀ x ∈ sg, x ∈ S.centers := fun x hx =>
    (hX.mem_toFinset.1 (Finset.mem_filter.1 hx).1).1
  have hsg_memCube : ∀ x ∈ sg, x ∈ g0 +ᵥ coordCube d L := fun x hx => by
    have h : g0 = -PeriodicConstantApprox.coordCubeCover L hLpos x :=
      (Finset.mem_filter.1 hx).2.symm
    exact h ▸ by simpa [Set.mem_vadd_set_iff_neg_vadd_mem]
      using PeriodicConstantApprox.coordCubeCover_spec L hLpos x
  have hs_le : (s.card : ℝ≥0∞) ≤ (t.card : ℝ≥0∞) * (sg.card : ℝ≥0∞) := by
    exact_mod_cast by simpa [Finset.card_eq_sum_card_fiberwise hf_maps, Finset.sum_const] using
      Finset.sum_le_sum hg0max
  have ht_vol : ((t.card : ℝ≥0∞) * volCube)
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R₁ + 2 * C)) := by
    simpa [volCube, R₁, r, t, htSet] using
      PeriodicConstantApprox.card_finite_lattice_in_ball_mul_volume_coordCube_le_volume_ball
        hLpos hC
  have hs_enc : ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) =
      s.card := congrArg ((↑) : ENat → ℝ≥0∞) (show (S.centers ∩ ball 0 (R + r)).Finite by
    simpa [R₁, r, add_assoc, add_left_comm, add_comm] using hX).encard_eq_coe_toFinset_card
  have hs_mul : ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞)
      * volCube ≤ (sg.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) :=
    calc ((S.centers ∩ ball _ (R + r)).encard : ℝ≥0∞) * volCube
        = (s.card : ℝ≥0∞) * volCube := by rw [hs_enc]
      _ ≤ (t.card : ℝ≥0∞) * (sg.card : ℝ≥0∞) * volCube := mul_le_mul_left hs_le volCube
      _ = (sg.card : ℝ≥0∞) * ((t.card : ℝ≥0∞) * volCube) := by ac_rfl
      _ ≤ _ := mul_le_mul_right (by
          simpa [show R + Cshift = R₁ + 2 * C by simp [Cshift, R₁, r, add_left_comm, add_comm],
            volCube] using ht_vol) _
  have hsg_density :
      b + cubeShellErr L < (sg.card : ℝ≥0∞) * volBall / volCube := by
    set V := volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift))
    refine (hRratio.trans hc_ratio).trans_le ?_
    have := mul_le_mul_left (show ((S.centers ∩ ball 0 (R + r)).encard : ℝ≥0∞) / V ≤
        (sg.card : ℝ≥0∞) / volCube by
      have h := ENNReal.div_le_div_right (ENNReal.div_le_of_le_mul hs_mul) volCube
      rwa [show ∀ a c : ℝ≥0∞, ((a * volCube) / c) / volCube = a / c from fun a c => by
        simp only [div_eq_mul_inv,
          show a * volCube * c⁻¹ * volCube⁻¹ = a * c⁻¹ * (volCube * volCube⁻¹) by ring,
          ENNReal.mul_inv_cancel hvolCube_ne0 hvolCube_ne_top, mul_one]] at h) volBall
    simp only [div_eq_mul_inv] at this ⊢; convert this using 1 <;> ring
  let innerSet : Set (EuclideanSpace ℝ (Fin d)) := g0 +ᵥ coordCubeInner d L r
  letI : DecidablePred (fun x : EuclideanSpace ℝ (Fin d) => x ∈ innerSet) := Classical.decPred _
  let F : Finset (EuclideanSpace ℝ (Fin d)) := sg.filter fun x => x ∈ innerSet
  let sb : Finset (EuclideanSpace ℝ (Fin d)) := sg.filter fun x => x ∉ innerSet
  have hsb_vol : (sb.card : ℝ≥0∞) * volBall ≤ shellVol := by
    simpa [volBall, shellVol, r, PeriodicConstantApprox.constVec] using
      PeriodicConstantApprox.card_mul_volume_ball_le_volume_outer_diff_inner S hLpos hSsep
        (fun x hx => hsg_centers x (Finset.mem_filter.1 hx).1)
        (fun x hx => ⟨hsg_memCube x (Finset.mem_filter.1 hx).1, by
          simpa [innerSet, show r = (1 / 2 : ℝ) by norm_num] using (Finset.mem_filter.1 hx).2⟩)
  obtain ⟨P, hPsep, hPdens⟩ := PeriodicConstantApprox.periodize_cube_density_eq hd S hSsep hLpos F
    (fun x hx => hsg_centers x (Finset.mem_filter.1 hx).1)
    (fun x hx => by simpa [innerSet] using (Finset.mem_filter.1 hx).2)
  have hPdens' : P.density = (F.card : ℝ≥0∞) * volBall / volCube := by
    simpa [volBall, show (Real.toNNReal (ZLattice.covolume (cubeLattice d L hLpos) volume) : ℝ≥0∞) =
        volCube by rw [show Real.toNNReal (ZLattice.covolume (cubeLattice d L hLpos) volume) =
          volCube.toNNReal by simpa [volCube] using
            PeriodicConstantApprox.toNNReal_covolume_cubeLattice (d := d) L hLpos,
        ENNReal.coe_toNNReal hvolCube_ne_top]] using hPdens
  refine ⟨P, hPsep, (lt_tsub_iff_right.mpr hsg_density).trans_le (tsub_le_iff_right.2 ?_)⟩
  have hsplit : (sg.card : ℝ≥0∞) * volBall =
      (F.card : ℝ≥0∞) * volBall + (sb.card : ℝ≥0∞) * volBall := by
    rw [show (sg.card : ℝ≥0∞) = (F.card : ℝ≥0∞) + (sb.card : ℝ≥0∞) by exact_mod_cast
      (Finset.card_filter_add_card_filter_not (s := sg) (p := fun x => x ∈ innerSet)).symm, add_mul]
  simpa [hPdens', div_eq_mul_inv, mul_add, add_mul, mul_assoc,
    show cubeShellErr L = shellVol / volCube by simp [cubeShellErr, shellVol, volCube],
    shellVol] using ENNReal.div_le_div_right (hsplit ▸ add_le_add_right hsb_vol _ :
      (sg.card : ℝ≥0∞) * volBall ≤ (F.card : ℝ≥0∞) * volBall + shellVol) volCube

end SpherePacking

/-- The periodic sphere packing constant equals the sphere packing constant. -/
public theorem periodic_constant_eq_constant (hd : 0 < d) :
    PeriodicSpherePackingConstant d = SpherePackingConstant d := by
  rw [periodic_constant_eq_periodic_constant_normalized,
    SpherePacking.constant_eq_constant_normalized]
  refine le_antisymm (iSup₂_le fun P hPsep =>
    (le_iSup (fun _ : (P.toSpherePacking).separation = 1 ↦ (P.toSpherePacking).density) hPsep).trans
      <| le_iSup (fun S : SpherePacking d ↦ ⨆ (_ : S.separation = 1), S.density)
        P.toSpherePacking) (iSup₂_le fun S hSsep => le_of_forall_lt fun a ha => ?_)
  obtain ⟨b, hab, hbS⟩ := exists_between ha
  obtain ⟨P, hPsep, hbP⟩ :=
    SpherePacking.exists_periodicSpherePacking_sep_one_density_gt_of_lt_density hd S hSsep hbS
  exact hab.trans (hbP.trans_le (le_iSup_of_le P (le_iSup_of_le hPsep le_rfl)))

end PeriodicPackingBoundaryControl

open scoped FourierTransform ENNReal SchwartzMap BigOperators RealInnerProductSpace
open SpherePacking MeasureTheory Complex Real Bornology Module

section LPPrereqs

variable {d : ℕ} [Fact (0 < d)]
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

/-- Convenience: `Fin d` is nonempty when `0 < d`. -/
public instance instNonemptyFin : Nonempty (Fin d) := ⟨0, Fact.out⟩

noncomputable section

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
  (f : 𝓢(V, E))

/-- Fourier inversion for Schwartz functions. -/
@[simp]
public theorem fourierInversion : 𝓕⁻ (𝓕 ⇑f) = f := by rw [← fourier_coe, ← fourierInv_coe]; simp

end SchwartzMap
section Integration

open MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [MeasureSpace E] [BorelSpace E]
variable [(volume : Measure E).IsAddLeftInvariant] [(volume : Measure E).Regular]
  [NeZero (volume : Measure E)]

instance : (volume : Measure E).IsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_regular

/-- If `f` is continuous, integrable, and pointwise nonnegative, then `∫ f = 0` iff `f = 0`.
This uses that an additive-invariant regular measure is positive on nonempty open sets. -/
public theorem Continuous.integral_zero_iff_zero_of_nonneg {f : E → ℝ} (hf₁ : Continuous f)
    (hf₂ : Integrable f) (hnn : ∀ x, 0 ≤ f x) : ∫ (v : E), f v = 0 ↔ f = 0 := by
  refine ⟨fun hintf => funext fun x => ?_, fun hf => by simp [hf]⟩
  by_contra hx
  exact (MeasureTheory.Measure.measure_pos_of_mem_nhds volume
      ((isOpen_lt continuous_const hf₁).mem_nhds (lt_of_le_of_ne (hnn x) (Ne.symm hx)))).ne'
    (measure_mono_null (fun (y : E) (hy : 0 < f y) => hy.ne')
      ((integral_eq_zero_iff_of_nonneg hnn hf₂).1 hintf))

end Integration

end

end LPPrereqs

/-! ## Summability and reindexing helpers (merged from `LPBoundReindex`) -/

namespace SpherePacking.CohnElkies
variable {d : ℕ}

namespace LPBoundAux

variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]

/-- A Schwartz function has summable norms on any translate of a `ℤ`-lattice. -/
public lemma summable_norm_comp_add_zlattice (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (a : EuclideanSpace ℝ (Fin d)) :
    Summable (fun ℓ : Λ => ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖) := by
  let k : ℕ := Module.finrank ℤ Λ + 2
  obtain ⟨C, _hCpos, hC⟩ := f.decay k 0
  set b : EuclideanSpace ℝ (Fin d) := -a
  refine Summable.of_norm_bounded_eventually
    (f := fun ℓ : Λ => ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖)
    (g := fun ℓ : Λ => (C + 1) * ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖⁻¹ ^ k) ?_ ?_
  · simpa [mul_assoc] using
      (ZLattice.summable_norm_sub_inv_pow (L := Λ) (n := k) (by simp [k]) b).mul_left (C + 1)
  · letI : DiscreteTopology Λ.toAddSubgroup := inferInstanceAs (DiscreteTopology Λ)
    refine (show ({ℓ : Λ | ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ ≤ (1 : ℝ)} : Set Λ).Finite by
      simpa [Set.preimage, Metric.mem_closedBall, dist_eq_norm, and_true] using
        (Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
          Metric.isBounded_closedBall (by simpa [Submodule.coe_toAddSubgroup] using
            AddSubgroup.isClosed_of_discrete (H := Λ.toAddSubgroup) :
            IsClosed (X := EuclideanSpace ℝ (Fin d))
              (Λ : Set (EuclideanSpace ℝ (Fin d))))).preimage_embedding
          (f := (⟨Subtype.val, Subtype.coe_injective⟩ : Λ ↪ EuclideanSpace ℝ (Fin d)))).subset
            fun ℓ hfail => ?_
    by_contra hlarge
    have hpos : 0 < ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ ^ k :=
      pow_pos (lt_of_lt_of_le one_pos (lt_of_not_ge hlarge).le) _
    have hdec :
        ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ ^ k *
          ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖ ≤ C := by
      simpa [show ‖a + (ℓ : EuclideanSpace ℝ (Fin d))‖ =
          ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ from by simp [b, sub_eq_add_neg, add_comm],
        norm_iteratedFDeriv_zero] using hC (a + (ℓ : EuclideanSpace ℝ (Fin d)))
    refine hfail (by simpa [div_eq_mul_inv, inv_pow] using
      ((le_div_iff₀' hpos).2 hdec).trans (by
        simpa [div_eq_mul_inv, mul_assoc] using
          mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1)
            (by positivity : 0 ≤ (‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ ^ k)⁻¹)))

end LPBoundAux

namespace LPBoundSummability

open SpherePacking.CohnElkies.LPBoundAux

variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]
variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (a : EuclideanSpace ℝ (Fin d))

/-- A Schwartz function is summable on any translate of a discrete `ℤ`-lattice. -/
public theorem summable_lattice_translate :
    Summable (fun ℓ : Λ => f (a + (ℓ : EuclideanSpace ℝ (Fin d)))) :=
  Summable.of_norm (summable_norm_comp_add_zlattice (Λ := Λ) f a)

/-- The real part of a Schwartz function is summable on any translate of a discrete `ℤ`-lattice. -/
public theorem summable_lattice_translate_re :
    Summable (fun ℓ : Λ => (f (a + (ℓ : EuclideanSpace ℝ (Fin d)))).re) :=
  Complex.reCLM.summable (summable_lattice_translate (Λ := Λ) f a)

end LPBoundSummability

/-- A discrete `ℤ`-lattice has a discrete dual submodule (for the Euclidean inner product). -/
public instance (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] :
    DiscreteTopology
      (LinearMap.BilinForm.dualSubmodule (B := innerₗ (EuclideanSpace ℝ (Fin d))) Λ) := by
  let bZ : Basis (Module.Free.ChooseBasisIndex ℤ Λ) ℤ Λ := Module.Free.chooseBasis ℤ Λ
  have hB : LinearMap.BilinForm.Nondegenerate (innerₗ (EuclideanSpace ℝ (Fin d)) :
      LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin d))) := by
    constructor <;> intro x hx <;>
      exact inner_self_eq_zero.1 (by simpa [innerₗ_apply_apply] using hx x : ⟪x, x⟫ = (0 : ℝ))
  exact (show LinearMap.BilinForm.dualSubmodule (B := innerₗ (EuclideanSpace ℝ (Fin d))) Λ =
      Submodule.span ℤ (Set.range
        (LinearMap.BilinForm.dualBasis (B := innerₗ (EuclideanSpace ℝ (Fin d)))
          hB (bZ.ofZLatticeBasis ℝ Λ))) by
    simpa [bZ.ofZLatticeBasis_span (K := ℝ) (L := Λ)] using
      LinearMap.BilinForm.dualSubmodule_span_of_basis (B := innerₗ (EuclideanSpace ℝ (Fin d)))
        (R := ℤ) (S := ℝ) (M := EuclideanSpace ℝ (Fin d)) hB (bZ.ofZLatticeBasis ℝ Λ)) ▸
    inferInstance

noncomputable section

/-- Equivalence `((P.centers ∩ D) × P.lattice) ≃ P.centers` from a unique-covering assumption. -/
@[expose] public def centersInterProdEquiv (P : PeriodicSpherePacking d) [Nonempty P.centers]
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) :
    (↑(P.centers ∩ D) × P.lattice) ≃ P.centers := by
  have hcover :
      ∀ x : P.centers, ∃! g : P.lattice, g +ᵥ (x : EuclideanSpace ℝ (Fin d)) ∈ P.centers ∩ D :=
    fun x =>
      let ⟨g, hg, hguniq⟩ := hD_unique_covers (x : EuclideanSpace ℝ (Fin d))
      ⟨g, ⟨P.lattice_action g.property x.property, hg⟩, fun g' hg' => hguniq g' hg'.2⟩
  let cover : P.centers → P.lattice := fun x => Classical.choose (hcover x)
  let repr : P.centers → ↑(P.centers ∩ D) := fun x =>
    ⟨cover x +ᵥ (x : EuclideanSpace ℝ (Fin d)), (Classical.choose_spec (hcover x)).1⟩
  let toCenter : ↑(P.centers ∩ D) × P.lattice → P.centers := fun p =>
    ⟨p.2 +ᵥ (p.1 : EuclideanSpace ℝ (Fin d)), P.lattice_action p.2.property p.1.property.1⟩
  let toPair : P.centers → ↑(P.centers ∩ D) × P.lattice := fun x => (repr x, -cover x)
  refine { toFun := toCenter, invFun := toPair, left_inv := ?_, right_inv := ?_ }
  · intro p
    have hcov : cover (toCenter p) = -p.2 :=
      ((Classical.choose_spec (hcover (toCenter p))).2 (-p.2)
        (by simp [toCenter, p.1.property])).symm
    exact Prod.ext (Subtype.ext (by simp [toPair, repr, toCenter, hcov])) (by simp [toPair, hcov])
  · exact fun x => Subtype.ext (by simp [toPair, repr, toCenter, neg_vadd_vadd])

/-- Reindex the `x : P.centers` sum as a `x₀ : P.centers ∩ D` sum over lattice translates,
the periodic decomposition used in `LPBound.lean`. -/
public lemma tsum_centers_eq_tsum_centersInter_centersInter_lattice
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (P : PeriodicSpherePacking d) [Nonempty P.centers]
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_isBounded : Bornology.IsBounded D)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) :
    ∑' (x : P.centers) (y : ↑(P.centers ∩ D)), (f (x - (y : EuclideanSpace ℝ (Fin d)))).re =
      ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
        (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re := by
  haveI : Finite (↑(P.centers ∩ D)) := finite_centers_inter_of_isBounded P D hD_isBounded hd
  letI : Fintype (↑(P.centers ∩ D)) := Fintype.ofFinite _
  let e : (↑(P.centers ∩ D) × P.lattice) ≃ P.centers :=
    centersInterProdEquiv (P := P) (D := D) hD_unique_covers
  have he_sub (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice) :
      ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))) =
        (x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)) := by
    simp [e, centersInterProdEquiv, Submodule.vadd_def, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm]
  rw [show (∑' x : P.centers, ∑' y : ↑(P.centers ∩ D), (f (x - (y : EuclideanSpace ℝ (Fin d)))).re)
        = ∑' p : ↑(P.centers ∩ D) × P.lattice,
          ∑' y : ↑(P.centers ∩ D),
            (f ((e p : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re from by
      simpa [e] using (e.tsum_eq (f := fun x : P.centers =>
        ∑' y : ↑(P.centers ∩ D), (f (x - (y : EuclideanSpace ℝ (Fin d)))).re)).symm]
  have hSummable_p :
      Summable (fun p : ↑(P.centers ∩ D) × P.lattice => ∑' y : ↑(P.centers ∩ D),
        (f ((e p : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re) := by
    simp_rw [tsum_fintype]
    refine summable_sum fun y _ => Summable.of_norm_bounded
      (g := fun p : ↑(P.centers ∩ D) × P.lattice =>
        ‖f ((p.1 : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (p.2 : EuclideanSpace ℝ (Fin d)))‖) ?_ ?_
    · refine (summable_prod_of_nonneg fun _ => norm_nonneg _).2
        ⟨fun x => by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (SpherePacking.CohnElkies.LPBoundAux.summable_norm_comp_add_zlattice (Λ := P.lattice) f
            ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))), Summable.of_finite⟩
    · rintro ⟨x, ℓ⟩
      simpa [he_sub x y ℓ, Real.norm_eq_abs] using
        Complex.abs_re_le_norm (f
          ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))))
  rw [show (∑' p : ↑(P.centers ∩ D) × P.lattice,
          ∑' y : ↑(P.centers ∩ D),
            (f ((e p : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re)
        = ∑' (x : ↑(P.centers ∩ D)) (ℓ : P.lattice),
          ∑' y : ↑(P.centers ∩ D),
            (f ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re from by
      simpa using hSummable_p.tsum_prod]
  have hy_comm : ∀ x : ↑(P.centers ∩ D),
      (∑' ℓ : P.lattice, ∑' y : ↑(P.centers ∩ D),
            (f ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re) =
        ∑' y : ↑(P.centers ∩ D), ∑' ℓ : P.lattice,
          (f ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) -
            (y : EuclideanSpace ℝ (Fin d)))).re := fun x => by
    simpa [tsum_fintype] using
      (Summable.tsum_finsetSum (s := (Finset.univ : Finset ↑(P.centers ∩ D)))
        (f := fun (y : ↑(P.centers ∩ D)) (ℓ : P.lattice) =>
          (f ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re)
        (fun y _ =>
          (summable_congr fun b => congrArg Complex.re (congrArg (⇑f) (he_sub x y b))).mpr
            (SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_translate_re
              (Λ := P.lattice) (f := f)
              ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))))))
  simp_rw [hy_comm]
  exact tsum_congr fun x =>
    tsum_congr₂ fun b c => congrArg Complex.re (congrArg (⇑f) (he_sub x b c))

end

/-! ## Main LP bound -/

/-- Commute the finite `x,y` sums with the dual-lattice `m` sum in the Poisson summation
expression. We assume `𝓕 f` is real-valued so the result lives in real parts. -/
public lemma calc_steps_swap_sums {d : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), (((𝓕 f) x).re : ℂ) = (𝓕 f) x)
    (P : PeriodicSpherePacking d) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_isBounded : Bornology.IsBounded D) (hd : 0 < d) :
    (∑' x : ↑(P.centers ∩ D),
        ∑' y : ↑(P.centers ∩ D),
          (1 / ZLattice.covolume P.lattice volume) *
            ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
              (𝓕 f m) *
                exp (2 * π * I *
                  ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                    (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])).re
      =
      ((1 / ZLattice.covolume P.lattice volume) *
          ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
            (𝓕 f m).re *
              (∑' x : ↑(P.centers ∩ D),
                ∑' y : ↑(P.centers ∩ D),
                  exp (2 * π * I *
                    ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                      (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))).re := by
  have : Finite (↑(P.centers ∩ D)) := finite_centers_inter_of_isBounded P D hD_isBounded hd
  letI : Fintype (↑(P.centers ∩ D)) := Fintype.ofFinite (↑(P.centers ∩ D))
  refine congrArg Complex.re ?_
  let c : ℂ := (1 / ZLattice.covolume P.lattice volume : ℂ)
  let a : SchwartzMap.dualLattice (d := d) P.lattice → ℂ := fun m => ((𝓕 f m).re : ℂ)
  let e : ↑(P.centers ∩ D) → ↑(P.centers ∩ D) →
      SchwartzMap.dualLattice (d := d) P.lattice → ℂ := fun x y m =>
    exp (2 * π * I *
      ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
        (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])
  have hFourierReal : ∀ m : SchwartzMap.dualLattice (d := d) P.lattice, (𝓕 f m) = a m := fun m => by
    simpa [a] using (hRealFourier (m : EuclideanSpace ℝ (Fin d))).symm
  have hSummableFourierNorm :
      Summable (fun m : SchwartzMap.dualLattice (d := d) P.lattice =>
        ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖) := by
    simpa using
      (SpherePacking.CohnElkies.LPBoundAux.summable_norm_comp_add_zlattice
        (Λ := SchwartzMap.dualLattice (d := d) P.lattice) (f := 𝓕 f)
        (a := (0 : EuclideanSpace ℝ (Fin d))))
  have hSummable_c_mul_a_mul_e : ∀ x y : ↑(P.centers ∩ D),
      Summable fun m : SchwartzMap.dualLattice (d := d) P.lattice => c * a m * e x y m := fun x y =>
    Summable.of_norm_bounded
      (g := fun m : SchwartzMap.dualLattice (d := d) P.lattice =>
        ‖c‖ * ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖)
      (by simpa [mul_assoc] using hSummableFourierNorm.mul_left ‖c‖) fun m => by
        have hnexp : ‖e x y m‖ = (1 : ℝ) := by
          simpa [e, mul_assoc, mul_left_comm, mul_comm] using
            (Complex.norm_exp_I_mul_ofReal (x := 2 * π *
              ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))
        simp_all
  have hmain :
      (∑' x : ↑(P.centers ∩ D),
          ∑' y : ↑(P.centers ∩ D),
            c * ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, a m * e x y m)
        =
        c * ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
            a m * (∑' x : ↑(P.centers ∩ D), ∑' y : ↑(P.centers ∩ D), e x y m) := by
    simp only [tsum_fintype]
    simp_rw [← tsum_mul_left]
    simp_rw [show ∀ x : ↑(P.centers ∩ D),
        (∑ y : ↑(P.centers ∩ D),
            ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, c * (a m * e x y m))
          = ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
            ∑ y : ↑(P.centers ∩ D), c * (a m * e x y m) from fun x =>
      (Summable.tsum_finsetSum (fun y _ => by
        simpa [mul_assoc] using hSummable_c_mul_a_mul_e x y)).symm]
    rw [show (∑ x : ↑(P.centers ∩ D),
            ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
              ∑ y : ↑(P.centers ∩ D), c * (a m * e x y m))
          = ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
            ∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), c * (a m * e x y m) from
      (Summable.tsum_finsetSum (fun x _ => by
        simpa using
          (summable_sum fun y _ => by simpa [mul_assoc] using hSummable_c_mul_a_mul_e x y :
            Summable fun m : SchwartzMap.dualLattice (d := d) P.lattice =>
              ∑ y ∈ (Finset.univ : Finset ↑(P.centers ∩ D)),
                c * (a m * e x y m)))).symm]
    refine tsum_congr fun m => ?_
    calc
      (∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), c * (a m * e x y m))
          = ∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), (c * a m) * e x y m := by
              simp [mul_assoc]
      _ = (c * a m) * (∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), e x y m) := by
              simp_rw [← Finset.mul_sum]
      _ = c * (a m * (∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), e x y m)) := by ring
  simpa (config := { zeta := false }) [c, e, hFourierReal] using hmain

variable {d : ℕ} {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)}
variable {P : PeriodicSpherePacking d} {D : Set (EuclideanSpace ℝ (Fin d))}

/-- Pointwise bound on the lattice sum appearing in the Cohn-Elkies argument. -/
public lemma lattice_sum_re_le_ite (hP : P.separation = 1)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (x y : ↑(P.centers ∩ D)) :
    (∑' ℓ : P.lattice,
          (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re)
      ≤ ite (x = y) (f 0).re 0 := by
  -- If `x,y ∈ D` and `x + ℓ = y`, then `ℓ = 0` by uniqueness of the cover of `y`.
  have hℓ_eq_zero_of_vadd_eq {x y : ↑(P.centers ∩ D)} {ℓ : P.lattice}
      (hxy : (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) =
          (y : EuclideanSpace ℝ (Fin d))) : ℓ = 0 := by
    obtain ⟨_, -, hg0_unique⟩ := hD_unique_covers (y : EuclideanSpace ℝ (Fin d))
    have hy0 : (0 : P.lattice) +ᵥ (y : EuclideanSpace ℝ (Fin d)) ∈ D := by
      simpa [Submodule.vadd_def] using y.property.2
    have hyℓ : (-ℓ : P.lattice) +ᵥ (y : EuclideanSpace ℝ (Fin d)) ∈ D := by
      have hEq : ((-ℓ : P.lattice) : EuclideanSpace ℝ (Fin d)) + (y : EuclideanSpace ℝ (Fin d)) =
          (x : EuclideanSpace ℝ (Fin d)) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (eq_sub_of_add_eq hxy).symm
      simpa [Submodule.vadd_def] using (hEq ▸ x.property.2 :
        ((-ℓ : P.lattice) : EuclideanSpace ℝ (Fin d)) + _ ∈ D)
    simpa using neg_eq_zero.mp ((hg0_unique (-ℓ) hyℓ).trans (hg0_unique 0 hy0).symm)
  by_cases hxy : x = y
  · subst hxy
    have hs : Summable fun ℓ : P.lattice => (f (ℓ : EuclideanSpace ℝ (Fin d))).re := by
      simpa [zero_add] using SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_translate_re
        (Λ := P.lattice) (f := f) (a := (0 : EuclideanSpace ℝ (Fin d)))
    have htail : (∑' ℓ : P.lattice,
          ite (ℓ = (0 : P.lattice)) 0 (f (ℓ : EuclideanSpace ℝ (Fin d))).re) ≤ 0 := by
      refine tsum_nonpos fun ℓ => ?_
      by_cases hℓ : ℓ = 0
      · simp [hℓ]
      have hxℓ : (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) ∈ P.centers := by
        simpa [add_comm] using P.lattice_action ℓ.property x.property.1
      have hneq : (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) ≠
            (x : EuclideanSpace ℝ (Fin d)) := fun h => hℓ (hℓ_eq_zero_of_vadd_eq h)
      have hnorm : (1 : ℝ) ≤ ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ := by
        have : (1 : ℝ) ≤ dist
            ((x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)))
            (x : EuclideanSpace ℝ (Fin d)) := by
          simpa [hP] using P.centers_dist' _ _ hxℓ x.property.1 hneq
        simpa [dist_eq_norm, add_sub_cancel_left] using this
      simp [hℓ, hCohnElkies₁ (ℓ : EuclideanSpace ℝ (Fin d)) (by simpa [ge_iff_le] using hnorm)]
    simpa [hs.tsum_eq_add_tsum_ite (0 : P.lattice)] using add_le_add_left htail (f 0).re
  · have hnonpos : ∀ ℓ : P.lattice,
        (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re ≤ 0 := fun ℓ => by
      have hxℓ : (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) ∈ P.centers := by
        simpa [add_comm] using P.lattice_action ℓ.property x.property.1
      have hneq : (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) ≠
            (y : EuclideanSpace ℝ (Fin d)) := fun h => by
        have hℓ0 : ℓ = 0 := hℓ_eq_zero_of_vadd_eq (x := x) (y := y) (ℓ := ℓ) h
        exact hxy (Subtype.ext (by simpa [hℓ0] using h))
      have hdist := P.centers_dist' _ _ hxℓ y.property.1 hneq
      have hnorm : (1 : ℝ) ≤ ‖(x : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))‖ := by
        have : (1 : ℝ) ≤ dist
            ((x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)))
            (y : EuclideanSpace ℝ (Fin d)) := by simpa [hP] using hdist
        simpa [dist_eq_norm] using this
      have hle := hCohnElkies₁ _ (by simpa [ge_iff_le] using hnorm)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hle
    simpa [hxy] using tsum_nonpos hnonpos

end SpherePacking.CohnElkies

variable {d : ℕ}
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)} (hne_zero : f ≠ 0)
variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))
variable (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))
variable (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)

local notation "conj" => starRingEnd ℂ

theorem hIntegrable : MeasureTheory.Integrable (𝓕 ⇑f) :=
  (FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) f).integrable

include hReal hRealFourier hCohnElkies₂ hne_zero in
theorem f_zero_pos : 0 < (f 0).re := by
  refine lt_of_le_of_ne (show 0 ≤ (f 0).re by
    rw [← f.fourierInversion, fourierInv_eq]
    simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul, ← RCLike.re_eq_complex_re,
      ← integral_re hIntegrable]
    exact integral_nonneg fun v ↦ by simpa using hCohnElkies₂ v) fun hf0re => hne_zero <|
    (ContinuousLinearEquiv.map_eq_zero_iff (FourierTransform.fourierCLE ℂ _)).1 ?_
  have hfun := (Continuous.integral_zero_iff_zero_of_nonneg
    (Complex.continuous_re.comp (𝓕 f).continuous) hIntegrable.re hCohnElkies₂).1 (by
    rw [show (∫ v : EuclideanSpace ℝ (Fin d), (re ∘ 𝓕 ⇑f) v) =
        (∫ v : EuclideanSpace ℝ (Fin d), 𝓕 (⇑f) v).re by
      simpa using integral_re (f := fun v : EuclideanSpace ℝ (Fin d) => 𝓕 (⇑f) v) hIntegrable]
    simpa [fourierInv_eq, show f 0 = 0 from by simpa [hf0re.symm] using (hReal 0).symm] using
      congrArg Complex.re (congrArg (· 0) f.fourierInversion))
  ext x; simpa [show (𝓕 f x).re = 0 from by simpa using congrFun hfun x] using (hRealFourier x).symm

section Fundamental_Domain_Dependent

variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)

omit [Nonempty ↑P.centers] in include hD_isBounded in
private lemma summable_fourier_mul_norm_exp_sq (hd : 0 < d) :
    Summable (fun m : ↥(SchwartzMap.dualLattice (d := d) P.lattice) =>
      (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)) := by
  letI : Fintype (↑(P.centers ∩ D)) :=
    @Fintype.ofFinite _ <| finite_centers_inter_of_isBounded P D hD_isBounded hd
  refine Summable.of_norm_bounded (g := fun m => ‖(𝓕 ⇑f) (m : EuclideanSpace ℝ (Fin d))‖ *
    ((Fintype.card (↑(P.centers ∩ D)) : ℝ) ^ 2)) ?_ fun m => ?_
  · simpa [SchwartzMap.fourier_coe] using
      (SpherePacking.CohnElkies.LPBoundAux.summable_norm_comp_add_zlattice
        (Λ := SchwartzMap.dualLattice (d := d) P.lattice) (f := 𝓕 f)
        (a := (0 : EuclideanSpace ℝ (Fin d)))).mul_right _
  simp only [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]; gcongr
  · simpa [Real.norm_eq_abs] using abs_re_le_norm _
  · simpa [tsum_fintype, Complex.norm_exp, mul_re, mul_im, mul_assoc, mul_left_comm, mul_comm]
      using norm_sum_le (Finset.univ : Finset ↑(P.centers ∩ D)) fun x : ↑(P.centers ∩ D) =>
      exp (2 * π * I * ⟪(x : EuclideanSpace ℝ (Fin d)), (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])

include d f hP hRealFourier hCohnElkies₁ hD_unique_covers in
theorem calc_steps_part1 (hd : 0 < d) :
    ↑(P.numReps' hd hD_isBounded) * (f 0).re ≥
      (1 / ZLattice.covolume P.lattice volume) *
        ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
          (𝓕 ⇑f m).re *
            (norm (∑' x : ↑(P.centers ∩ D),
              exp (2 * π * I *
                ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2) := by
  calc ↑(P.numReps' hd hD_isBounded) * (f 0).re
  _ ≥ ∑' (x : P.centers) (y : ↑(P.centers ∩ D)), (f (x - ↑y)).re := by
        letI : Fintype ↑(P.centers ∩ D) := P.instFintypeNumReps' hd hD_isBounded
        classical
        simp_rw [SpherePacking.CohnElkies.tsum_centers_eq_tsum_centersInter_centersInter_lattice
          (f := f) (P := P) (D := D) hD_isBounded hD_unique_covers hd, tsum_fintype]
        exact (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ =>
          CohnElkies.lattice_sum_re_le_ite hP hD_unique_covers hCohnElkies₁ x i).trans
          (by simp [PeriodicSpherePacking.numReps'])
  _ = ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice), (f (↑x - ↑y + ↑ℓ)).re :=
        CohnElkies.tsum_centers_eq_tsum_centersInter_centersInter_lattice f P
          hD_isBounded hD_unique_covers hd
  _ = (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
      f (↑x - ↑y + ↑ℓ)).re := by
        haveI : Finite ↑(P.centers ∩ D) := finite_centers_inter_of_isBounded P D hD_isBounded hd
        rw [re_tsum Summable.of_finite]
        exact tsum_congr fun x => by
          rw [re_tsum Summable.of_finite]; exact tsum_congr fun y => by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              (re_tsum (SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_translate
                (Λ := P.lattice) (f := f) (a := (↑x - ↑y : EuclideanSpace ℝ (Fin d))))).symm
  _ = (∑' x : ↑(P.centers ∩ D),
      ∑' y : ↑(P.centers ∩ D), (1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, (𝓕 f m) *
      exp (2 * π * I * ⟪↑x - ↑y, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])).re := by
        congr! 5 with x y; exact SchwartzMap.poissonSummation_lattice P.lattice f _
  _ = ((1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
      (𝓕 f m).re * (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
      exp (2 * π * I * ⟪↑x - ↑y, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))).re := by
        simpa using SpherePacking.CohnElkies.calc_steps_swap_sums (f := f)
          (hRealFourier := hRealFourier) (P := P) (D := D) hD_isBounded hd
  _ = ((1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, (𝓕 f m).re * (
      ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) *
      exp (2 * π * I * ⟪-↑y, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))).re := by
        congr! 9 with m x y; simp [sub_eq_neg_add, RCLike.wInner_neg_left, ofReal_neg, mul_neg,
          mul_comm, RCLike.wInner_add_left, ofReal_add, mul_add, Complex.exp_add]
  _ = ((1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
      (𝓕 f m).re * (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) *
      (∑' y : ↑(P.centers ∩ D),
      exp (-(2 * π * I * ⟪↑y, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])))).re := by
        simp_rw [mul_assoc, ← tsum_mul_right, ← tsum_mul_left]
        congr! 9 with m x y; simp only [RCLike.wInner_neg_left, ofReal_neg, mul_neg]
  _ = ((1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, (𝓕 f m).re *
      (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) *
      conj (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))).re := by
        simp_rw [conj_tsum]
        congr! 7 with m x
        calc Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
              (⟪(x : EuclideanSpace ℝ (Fin d)), m⟫_[ℝ] : ℂ)))
            = Circle.exp (-2 * Real.pi * ⟪(x : EuclideanSpace ℝ (Fin d)), m⟫_[ℝ]) := by
              rw [Circle.coe_exp]; push_cast; ring_nf
          _ = conj (Circle.exp (2 * Real.pi * ⟪(x : EuclideanSpace ℝ (Fin d)), m⟫_[ℝ])) := by
              rw [mul_assoc, neg_mul, ← mul_assoc, ← Circle.coe_inv_eq_conj, Circle.exp_neg]
          _ = conj (Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                (⟪(x : EuclideanSpace ℝ (Fin d)), m⟫_[ℝ] : ℂ))) := by
              rw [Circle.coe_exp]; apply congrArg conj; push_cast; ring_nf
  _ = (1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
        (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2) := by
        rw [← ofReal_re (1 / ZLattice.covolume P.lattice volume *
          ∑' (m : ↥(LinearMap.BilinForm.dualSubmodule (innerₗ _) P.lattice)),
            (𝓕 ⇑f ↑m).re * norm (∑' (x : ↑(P.centers ∩ D)),
            cexp (2 * ↑π * I * ↑⟪(x : EuclideanSpace ℝ (Fin d)), ↑m⟫_[ℝ])) ^ 2)]
        congr 1; push_cast; congr! 3 with m
        rw [mul_assoc, mul_conj, Complex.normSq_eq_norm_sq]; norm_cast

include d f hCohnElkies₂ in omit [Nonempty ↑P.centers] in
theorem calc_steps_part2 (hd : 0 < d) :
    (1 / ZLattice.covolume P.lattice volume) *
        ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
          (𝓕 ⇑f m).re *
            (norm (∑' x : ↑(P.centers ∩ D),
              exp (2 * π * I *
                ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)
      ≥
      ↑(P.numReps' hd hD_isBounded) ^ 2 * (𝓕 f 0).re / ZLattice.covolume P.lattice volume := by
  calc (1 / ZLattice.covolume P.lattice volume) *
        ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
          (𝓕 ⇑f m).re *
            (norm (∑' x : ↑(P.centers ∩ D),
              exp (2 * π * I *
                ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)
    _ = (1 / ZLattice.covolume P.lattice volume) * (
        (∑' (m : SchwartzMap.dualLattice (d := d) P.lattice),
          if m = (0 : ↥(SchwartzMap.dualLattice (d := d) P.lattice)) then 0
          else (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)) +
        (𝓕 ⇑f (0 : EuclideanSpace ℝ (Fin d))).re *
        (norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I * ⟪↑x, (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)) :=
        congrArg ((1 / ZLattice.covolume P.lattice volume) * ·)
          ((Summable.tsum_eq_add_tsum_ite (summable_fourier_mul_norm_exp_sq (f := f) (P := P)
            (D := D) (hD_isBounded := hD_isBounded) hd) 0).trans (by ac_rfl))
    _ ≥ (1 / ZLattice.covolume P.lattice volume) * (𝓕 ⇑f (0 : EuclideanSpace ℝ (Fin d))).re *
        (norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I * ⟪↑x, (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2) := by
        rw [ge_iff_le, ← tsub_nonpos, mul_assoc, ← mul_sub (1 / _) _ _]
        simpa using mul_nonneg (one_div_nonneg.mpr (ZLattice.covolume_pos P.lattice volume).le)
          (tsum_nonneg fun m => by
            by_cases hm : m = (0 : ↥(SchwartzMap.dualLattice (d := d) P.lattice))
            · simp [hm]
            · simpa [hm] using mul_nonneg
                (by simpa using hCohnElkies₂ (m : EuclideanSpace ℝ (Fin d)))
                (sq_nonneg (norm (∑' x : ↑(P.centers ∩ D),
                  exp (2 * π * I * ⟪(x : EuclideanSpace ℝ (Fin d)),
                    (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])))))
    _ = (1 / ZLattice.covolume P.lattice volume) * (𝓕 ⇑f (0 : EuclideanSpace ℝ (Fin d))).re *
        ↑(P.numReps' hd hD_isBounded) ^ 2 := by
        letI := P.instFintypeNumReps' hd hD_isBounded
        simp [PeriodicSpherePacking.numReps']
    _ = ↑(P.numReps' hd hD_isBounded) ^ 2 * (𝓕 f 0).re / ZLattice.covolume P.lattice volume := by
      simp [div_eq_mul_inv, mul_left_comm, mul_comm,
        show 𝓕 (⇑f) (0 : EuclideanSpace ℝ (Fin d)) = 𝓕 f 0 from rfl]

include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ P hP D hD_isBounded
  hD_unique_covers

/-- Linear programming bound for a single periodic packing of separation `1`. -/
public theorem LinearProgrammingBound' (hd : 0 < d) :
    P.density ≤ (f 0).re.toNNReal / (𝓕 f 0).re.toNNReal *
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  haveI : Fact (0 < d) := ⟨hd⟩
  rw [P.density_eq' hd]
  suffices hCalc : (P.numReps' hd hD_isBounded) * (f 0).re ≥
    (P.numReps' hd hD_isBounded)^2 * (𝓕 f 0).re / ZLattice.covolume P.lattice volume by
    rw [hP]; rw [ge_iff_le] at hCalc
    have vol_ne_zero : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ≠ 0 :=
      (Metric.measure_ball_pos (μ := volume) _ one_half_pos).ne'
    rcases eq_or_ne (𝓕 f 0) 0 with h𝓕f | h𝓕f
    · rw [h𝓕f, zero_re, ENat.toENNReal_coe, toNNReal_zero, ENNReal.coe_zero,
        ENNReal.div_zero (ENNReal.coe_ne_zero.mpr (toNNReal_pos.mpr
          (f_zero_pos hne_zero hReal hRealFourier hCohnElkies₂)).ne'),
        ENNReal.top_mul vol_ne_zero]; exact le_top
    rw [← PeriodicSpherePacking.numReps_eq_numReps' (S := P) Fact.out hD_isBounded
      hD_unique_covers] at hCalc
    have hfouaux₁ : ((𝓕 f 0).re.toNNReal : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr <| by
      rw [ne_eq, Real.toNNReal_eq_zero, not_le]
      exact lt_of_le_of_ne (hCohnElkies₂ 0) fun heq => h𝓕f <|
        Complex.ext heq.symm (by simpa [eq_comm] using congrArg Complex.im (hRealFourier 0))
    haveI : Nonempty (Quotient (AddAction.orbitRel ↥P.lattice ↑P.centers)) :=
      (nonempty_quotient_iff _).2 ‹_›
    have hcov_pos : 0 < ZLattice.covolume P.lattice volume := ZLattice.covolume_pos P.lattice volume
    rw [ENat.toENNReal_coe, mul_div_assoc, div_eq_mul_inv (volume _), mul_comm (volume _),
      ← mul_assoc, ENNReal.mul_le_mul_iff_left vol_ne_zero measure_ball_lt_top.ne,
      ← ENNReal.mul_le_mul_iff_left hfouaux₁ ENNReal.coe_ne_top,
      div_eq_mul_inv ((f 0).re.toNNReal : ENNReal) _, mul_assoc ((f 0).re.toNNReal : ENNReal) _ _,
      ENNReal.inv_mul_cancel hfouaux₁ ENNReal.coe_ne_top, mul_one, mul_assoc,
      ← ENNReal.div_eq_inv_mul, ← ENNReal.mul_le_mul_iff_right
        (by simpa [ENat.toENNReal_coe] using Fintype.card_ne_zero :
          ENat.toENNReal (P.numReps : ENat) ≠ 0)
        (Ne.symm (ne_of_beq_false rfl) : ENat.toENNReal (P.numReps : ENat) ≠ ⊤),
      ENat.toENNReal_coe, ← mul_assoc, ← pow_two, ← mul_div_assoc,
      show (P.numReps : ENNReal) * ↑(f 0).re.toNNReal = (P.numReps * (f 0).re).toNNReal by
        simp [Real.toNNReal_mul (Nat.cast_nonneg _)],
      show (P.numReps : ENNReal) ^ 2 * ((𝓕 f 0).re.toNNReal : ENNReal) /
          ((ZLattice.covolume P.lattice volume).toNNReal : ENNReal) =
          ((P.numReps) ^ 2 * (𝓕 f 0).re / ZLattice.covolume P.lattice volume).toNNReal by
        simp only [div_eq_mul_inv, ← ENNReal.coe_inv (Real.toNNReal_pos.mpr hcov_pos).ne',
          Real.toNNReal_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (hCohnElkies₂ 0))
            (inv_nonneg.mpr hcov_pos.le))]
        norm_cast
        rw [Real.toNNReal_of_nonneg (hCohnElkies₂ 0), Real.toNNReal_of_nonneg hcov_pos.le]; rfl,
      ENNReal.coe_le_coe]
    exact Real.toNNReal_le_toNNReal hCalc
  exact ge_trans (calc_steps_part1 (P := P) (D := D) hRealFourier hCohnElkies₁ hP hD_isBounded
    hD_unique_covers hd) (calc_steps_part2 (P := P) (D := D) (hCohnElkies₂ := hCohnElkies₂)
      hD_isBounded hd)

end Fundamental_Domain_Dependent

include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂

/-- The Cohn-Elkies linear programming upper bound on `SpherePackingConstant d`. -/
public theorem LinearProgrammingBound (hd : 0 < d) : SpherePackingConstant d ≤
    (f 0).re.toNNReal / (𝓕 ⇑f 0).re.toNNReal *
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  rw [← periodic_constant_eq_constant hd,
    periodic_constant_eq_periodic_constant_normalized (d := d)]
  refine iSup_le fun P => iSup_le fun hP => ?_
  rcases isEmpty_or_nonempty ↑P.centers with _ | _
  · simp [P.density_of_centers_empty hd]
  exact LinearProgrammingBound' hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hP
    (ZSpan.fundamentalDomain_isBounded _) (PeriodicSpherePacking.fundamental_domain_unique_covers
      (S := P) (((ZLattice.module_free ℝ P.lattice).chooseBasis).reindex
        (PeriodicSpherePacking.basis_index_equiv P))) hd
