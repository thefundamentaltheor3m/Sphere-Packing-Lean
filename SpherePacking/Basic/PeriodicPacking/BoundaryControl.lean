module
public import SpherePacking.Basic.PeriodicPacking.PeriodicConstant
import Mathlib.Combinatorics.Pigeonhole

/-!
# Periodic packings: boundary control

This file develops a boundary control argument for approximating the density of an arbitrary sphere
packing by the density of an associated periodic packing.

The construction uses coordinate cubes together with a pigeonhole principle to choose a good
translate, and then bounds the error coming from points near the boundary. The main result is
`periodic_constant_eq_constant`, showing that the periodic sphere packing constant coincides with
the sphere packing constant.
-/

open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise Topology

variable {d : ℕ}

namespace PeriodicConstantApprox

section CoordCubeCover

open Metric

variable (L : ℝ) (hL : 0 < L)

/-- The unique lattice translate sending `x` into the coordinate cube `coordCube L`. -/
noncomputable def coordCubeCover (x : EuclideanSpace ℝ (Fin d)) : cubeLattice (d := d) L hL :=
  Classical.choose (PeriodicConstant.coordCube_unique_covers (d := d) L hL x)

lemma coordCubeCover_spec (x : EuclideanSpace ℝ (Fin d)) :
    coordCubeCover (d := d) L hL x +ᵥ x ∈ coordCube (d := d) L :=
  (Classical.choose_spec (PeriodicConstant.coordCube_unique_covers (d := d) L hL x)).1

lemma coordCubeCover_unique (x : EuclideanSpace ℝ (Fin d)) (g : cubeLattice (d := d) L hL)
    (hg : g +ᵥ x ∈ coordCube (d := d) L) :
    g = coordCubeCover (d := d) L hL x :=
  (Classical.choose_spec (PeriodicConstant.coordCube_unique_covers (d := d) L hL x)).2 g hg

lemma mem_neg_coordCubeCover_vadd_coordCube (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ (-coordCubeCover (d := d) L hL x) +ᵥ coordCube (d := d) L := by
  simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using coordCubeCover_spec (d := d) L hL x

lemma neg_coordCubeCover_mem_ball {C R : ℝ}
    (hC : coordCube (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ ball 0 R) :
    ((-coordCubeCover (d := d) L hL x : cubeLattice (d := d) L hL) :
        EuclideanSpace ℝ (Fin d)) ∈ ball 0 (R + C) := by
  have hx0 : ‖x‖ < R := by simpa [mem_ball_zero_iff] using hx
  have hxgC : ‖(coordCubeCover (d := d) L hL x : EuclideanSpace ℝ (Fin d)) + x‖ < C := by
    have hmem :
        (coordCubeCover (d := d) L hL x : EuclideanSpace ℝ (Fin d)) + x ∈ coordCube (d := d) L := by
      simpa [Submodule.vadd_def, vadd_eq_add] using coordCubeCover_spec (d := d) L hL x
    simpa [mem_ball_zero_iff] using (hC hmem)
  have htri :
      ‖(coordCubeCover (d := d) L hL x : EuclideanSpace ℝ (Fin d))‖ ≤
        ‖(coordCubeCover (d := d) L hL x : EuclideanSpace ℝ (Fin d)) + x‖ + ‖x‖ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (norm_sub_le (a := (coordCubeCover (d := d) L hL x : EuclideanSpace ℝ (Fin d)) + x) (b := x))
  have :
      ‖(- (coordCubeCover (d := d) L hL x : EuclideanSpace ℝ (Fin d)))‖ < R + C := by
    have : ‖(coordCubeCover (d := d) L hL x : EuclideanSpace ℝ (Fin d))‖ < C + R := by
      refine lt_of_le_of_lt htri ?_
      simpa [add_comm, add_left_comm, add_assoc] using add_lt_add hxgC hx0
    simpa [norm_neg, add_comm, add_left_comm, add_assoc] using this
  simpa [mem_ball_zero_iff] using this

lemma mem_vadd_coordCube_iff_eq_neg_coordCubeCover (g : cubeLattice (d := d) L hL)
    (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ g +ᵥ coordCube (d := d) L ↔ g = -coordCubeCover (d := d) L hL x := by
  constructor
  · intro hx
    have : (-g : cubeLattice (d := d) L hL) = coordCubeCover (d := d) L hL x :=
      coordCubeCover_unique (d := d) L hL x (-g)
        (by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hx)
    simpa using congrArg (fun t : cubeLattice (d := d) L hL => -t) this
  · rintro rfl; exact mem_neg_coordCubeCover_vadd_coordCube (d := d) L hL x

end CoordCubeCover

section CoverVolumeBound

open scoped BigOperators

lemma vadd_coordCube_subset_ball {L : ℝ} (hL : 0 < L) {R C : ℝ}
    (hC : coordCube (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C)
    {g : cubeLattice (d := d) L hL}
    (hg : (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 (R + C)) :
    g +ᵥ coordCube (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C)) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hx' : ‖x‖ < C := by
    simpa [mem_ball_zero_iff] using hC hx
  have hg' : ‖(g : EuclideanSpace ℝ (Fin d))‖ < R + C := by
    simpa [mem_ball_zero_iff] using hg
  have : ‖(g : EuclideanSpace ℝ (Fin d)) + x‖ < R + (2 * C) := by
    refine (lt_of_le_of_lt (norm_add_le _ _) ?_)
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using add_lt_add hg' hx'
  simpa [Submodule.vadd_def, vadd_eq_add, mem_ball_zero_iff] using this

lemma iUnion_finset_vadd_coordCube_subset_ball {L : ℝ} (hL : 0 < L) {R C : ℝ}
    (hC : coordCube (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C) :
    let htSet :=
      PeriodicConstantApprox.finite_lattice_in_ball (d := d) L hL (R + C)
    let t : Finset (cubeLattice (d := d) L hL) := htSet.toFinset
    (⋃ g ∈ t, g +ᵥ coordCube (d := d) L) ⊆
      ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C)) := by
  intro htSet t y hy
  rcases Set.mem_iUnion₂.1 hy with ⟨g, hgT, hy'⟩
  have hgBall :
      (g : EuclideanSpace ℝ (Fin d)) ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (R + C) :=
    htSet.mem_toFinset.1 (by simpa [t] using hgT)
  exact (vadd_coordCube_subset_ball (d := d) (hL := hL) (R := R) (C := C) hC hgBall) hy'

lemma card_finite_lattice_in_ball_mul_volume_coordCube_le_volume_ball {L : ℝ} (hL : 0 < L)
    {R C : ℝ} (hC : coordCube (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C) :
    let htSet :=
      PeriodicConstantApprox.finite_lattice_in_ball (d := d) L hL (R + C)
    let t : Finset (cubeLattice (d := d) L hL) := htSet.toFinset
    (t.card : ℝ≥0∞) * volume (coordCube (d := d) L) ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C))) := by
  intro htSet t
  have hdisj :
      Set.PairwiseDisjoint (↑t : Set (cubeLattice (d := d) L hL))
        (fun g : cubeLattice (d := d) L hL => g +ᵥ coordCube (d := d) L) := by
    intro g _ h _ hgh
    exact disjoint_vadd_of_unique_covers (d := d)
      (Λ := cubeLattice (d := d) L hL) (D := coordCube (d := d) L)
      (PeriodicConstant.coordCube_unique_covers (d := d) L hL) hgh
  have hmeas :
      ∀ g ∈ t, MeasurableSet (g +ᵥ coordCube (d := d) L) := by
    intro g _; simpa using
      (MeasurableSet.const_vadd (PeriodicConstant.measurableSet_coordCube (d := d) L hL) g)
  have hvol_union :
      volume (⋃ g ∈ t, g +ᵥ coordCube (d := d) L) =
        ∑ g ∈ t, volume (g +ᵥ coordCube (d := d) L) :=
    measure_biUnion_finset (μ := volume) hdisj hmeas
  have hsub :
      (⋃ g ∈ t, g +ᵥ coordCube (d := d) L) ⊆
        ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C)) :=
    iUnion_finset_vadd_coordCube_subset_ball (d := d) (hL := hL) (R := R) (C := C) hC
  have hle := volume.mono hsub
  simp_all

end CoverVolumeBound

section BoundaryControl

open scoped ENNReal Pointwise BigOperators

def constVec (c : ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun _ : Fin d => c)


lemma abs_coord_lt_of_norm_lt {x : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hx : ‖x‖ < r)
    (i : Fin d) : |x i| < r :=
  lt_of_le_of_lt (abs_coord_le_norm (d := d) x i) hx

/-- If `x` lies in the width-`1/2` boundary strip of `coordCube L`, then the `1/2`-ball around `x`
lies in a fixed set of finite volume independent of the translate. -/
lemma coordCube_boundary_half_add_ball_subset_outer_diff_inner (L : ℝ) :
    ((coordCube (d := d) L \ coordCubeInner (d := d) L (1 / 2)) +
        ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
      ⊆ ((constVec (d := d) (- (1 / 2 : ℝ))) +ᵥ coordCubeInner (d := d) (L + 1) 0) \
        coordCubeInner (d := d) L 1 := by
  intro z hz
  rcases hz with ⟨x, hx, y, hy, rfl⟩
  have hx_cube : x ∈ coordCube (d := d) L := hx.1
  refine ⟨?_, ?_⟩
  · have hy' : ‖y‖ < (1 / 2 : ℝ) := by
      simpa [mem_ball_zero_iff] using hy
    refine (Set.mem_vadd_set_iff_neg_vadd_mem).2 ?_
    simp only [coordCubeInner, coordCube, constVec, Set.mem_setOf_eq, vadd_eq_add] at hx_cube ⊢
    intro i
    have hxi : x i ∈ Set.Ico (0 : ℝ) L := hx_cube i
    have hyi : |y i| < (1 / 2 : ℝ) := abs_coord_lt_of_norm_lt (d := d) hy' i
    have hyi_le : -(1 / 2 : ℝ) ≤ y i ∧ y i ≤ (1 / 2 : ℝ) := by
      have : |y i| ≤ (1 / 2 : ℝ) := le_of_lt hyi
      simpa [abs_le] using this
    refine ⟨?_, ?_⟩
    · have : (0 : ℝ) ≤ x i + y i + (1 / 2 : ℝ) := by linarith [hxi.1, hyi_le.1]
      simpa [add_assoc, add_left_comm, add_comm] using this
    · have : x i + y i + (1 / 2 : ℝ) ≤ L + 1 := by linarith [hxi.2.le, hyi_le.2]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  · have hx_notInner : x ∉ coordCubeInner (d := d) L (1 / 2) := hx.2
    have hy' : ‖y‖ < (1 / 2 : ℝ) := by
      simpa [mem_ball_zero_iff] using hy
    have hy_abs : ∀ i : Fin d, |y i| < (1 / 2 : ℝ) := fun i =>
      abs_coord_lt_of_norm_lt (d := d) hy' i
    have : ∃ i : Fin d, x i < (1 / 2 : ℝ) ∨ (L - 1 / 2 : ℝ) < x i := by
      have : ∃ i : Fin d, ¬ x i ∈ Set.Icc (1 / 2 : ℝ) (L - 1 / 2) := by
        simpa [coordCubeInner, Set.mem_setOf_eq] using (not_forall.mp hx_notInner)
      rcases this with ⟨i, hi⟩
      have hi' : x i < (1 / 2 : ℝ) ∨ (L - 1 / 2 : ℝ) < x i := by
        have : ¬ ((1 / 2 : ℝ) ≤ x i ∧ x i ≤ (L - 1 / 2 : ℝ)) := by
          simpa [Set.mem_Icc] using hi
        have : ¬ (1 / 2 : ℝ) ≤ x i ∨ ¬ x i ≤ (L - 1 / 2 : ℝ) := not_and_or.mp this
        exact this.imp (fun h => lt_of_not_ge h) (fun h => lt_of_not_ge h)
      exact ⟨i, hi'⟩
    rcases this with ⟨i, hxi⟩
    intro hz_inner
    have hz_i : (x i + y i) ∈ Set.Icc (1 : ℝ) (L - 1) := by
      simpa [coordCubeInner, Set.mem_setOf_eq] using (hz_inner i)
    have hyi : |y i| < (1 / 2 : ℝ) := hy_abs i
    have hyi_lt : - (1 / 2 : ℝ) < y i ∧ y i < (1 / 2 : ℝ) := abs_lt.mp hyi
    cases hxi with
    | inl hlt =>
        have : x i + y i < (1 : ℝ) := by linarith
        exact (not_lt_of_ge hz_i.1) this
    | inr hgt =>
        have : (L - 1 : ℝ) < x i + y i := by linarith
        exact (not_lt_of_ge hz_i.2) this

variable (S : SpherePacking d)

lemma card_mul_volume_ball_le_volume_outer_diff_inner {L : ℝ} (hL : 0 < L)
    (hSsep : S.separation = 1)
    {g : cubeLattice (d := d) L hL} {s : Finset (EuclideanSpace ℝ (Fin d))}
    (hs_centers : ∀ x ∈ s, x ∈ S.centers)
    (hs_boundary : ∀ x ∈ s,
      x ∈ (g +ᵥ coordCube (d := d) L) \ (g +ᵥ coordCubeInner (d := d) L (1 / 2))) :
    (s.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ)) ≤
      volume (((constVec (d := d) (- (1 / 2 : ℝ))) +ᵥ coordCubeInner (d := d) (L + 1) 0) \
        coordCubeInner (d := d) L 1) := by
  let r : ℝ := (1 / 2 : ℝ)
  have hdisj :
      (s : Set (EuclideanSpace ℝ (Fin d))).PairwiseDisjoint fun x =>
        ball x r := by
    intro x hx y hy hxy
    have hxC : x ∈ S.centers := hs_centers x hx
    have hyC : y ∈ S.centers := hs_centers y hy
    have hdist : (1 : ℝ) ≤ dist x y := by
      simpa [hSsep] using (S.centers_dist' x y hxC hyC hxy)
    have hsum_eq : r + r = (1 : ℝ) := by
      simpa [r] using (by norm_num : (2⁻¹ : ℝ) + 2⁻¹ = 1)
    have hsum : r + r ≤ dist x y := by simpa [hsum_eq] using hdist
    exact ball_disjoint_ball hsum
  have hunion :
      volume (⋃ x ∈ s, ball x r) =
        (s.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) r) := by
    simpa [Measure.addHaar_ball_center, mul_comm, mul_assoc] using
      (measure_biUnion_finset (μ := volume) hdisj (by
        intro x _
        exact measurableSet_ball))
  have hle_union :
      (s.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) r) ≤
        volume (⋃ x ∈ s, ball x r) := by
    rw [hunion]
  have hsub :
      (⋃ x ∈ s, ball x r) ⊆
        g +ᵥ
          (((constVec (d := d) (- (1 / 2 : ℝ))) +ᵥ coordCubeInner (d := d) (L + 1) 0) \
              coordCubeInner (d := d) L 1) := by
    intro y hy
    rcases Set.mem_iUnion.1 hy with ⟨x, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hxS, hyBall⟩
    have hxB := hs_boundary x hxS
    have hx0 : (- (g : EuclideanSpace ℝ (Fin d))) +ᵥ x ∈ coordCube (d := d) L := by
      simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hxB.1
    have hx0_notInner :
        (- (g : EuclideanSpace ℝ (Fin d))) +ᵥ x ∉ coordCubeInner (d := d) L (1 / 2) := by
      intro hx0Inner
      apply hxB.2
      simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hx0Inner
    have hy0 :
        (- (g : EuclideanSpace ℝ (Fin d))) +ᵥ y ∈
          ball ((- (g : EuclideanSpace ℝ (Fin d))) +ᵥ x) r := by
      simpa [Metric.vadd_ball] using hyBall
    have hy0' :
        (- (g : EuclideanSpace ℝ (Fin d))) +ᵥ y ∈
          ((coordCube (d := d) L \ coordCubeInner (d := d) L (1 / 2)) +
              ball (0 : EuclideanSpace ℝ (Fin d)) r) := by
      let x0 : EuclideanSpace ℝ (Fin d) := (- (g : EuclideanSpace ℝ (Fin d))) +ᵥ x
      let y0 : EuclideanSpace ℝ (Fin d) := (- (g : EuclideanSpace ℝ (Fin d))) +ᵥ y
      have hy0' : y0 ∈ ball x0 r := by
        simpa [x0, y0] using hy0
      let z : EuclideanSpace ℝ (Fin d) := y0 - x0
      have hz : z ∈ ball (0 : EuclideanSpace ℝ (Fin d)) r := by
        have : dist y0 x0 < r := by simpa [Metric.mem_ball] using hy0'
        have : ‖y0 - x0‖ < r := by simpa [dist_eq_norm] using this
        simpa [z, Metric.mem_ball, dist_eq_norm] using this
      refine ⟨x0, ⟨?_, ?_⟩, z, hz, by
        simp [x0, y0, z, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]⟩
      · simpa [x0] using hx0
      · simpa [x0] using hx0_notInner
    have hy0'' :
        (- (g : EuclideanSpace ℝ (Fin d))) +ᵥ y ∈
          ((constVec (d := d) (- (1 / 2 : ℝ))) +ᵥ coordCubeInner (d := d) (L + 1) 0) \
            coordCubeInner (d := d) L 1 := by
      simpa [r] using
        (coordCube_boundary_half_add_ball_subset_outer_diff_inner (d := d) L
          (by simpa [r] using hy0'))
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hy0''
  have hle : volume (⋃ x ∈ s, ball x r) ≤
      volume (g +ᵥ
          (((constVec (d := d) (- (1 / 2 : ℝ))) +ᵥ coordCubeInner (d := d) (L + 1) 0) \
              coordCubeInner (d := d) L 1)) :=
    volume.mono hsub
  have htrans :
      volume (g +ᵥ
          (((constVec (d := d) (- (1 / 2 : ℝ))) +ᵥ coordCubeInner (d := d) (L + 1) 0) \
              coordCubeInner (d := d) L 1)) =
        volume (((constVec (d := d) (- (1 / 2 : ℝ))) +ᵥ coordCubeInner (d := d) (L + 1) 0) \
          coordCubeInner (d := d) L 1) := by
    simp [measure_vadd]
  have hr : (2⁻¹ : ℝ) = r := by
    dsimp [r]
    norm_num
  simpa [hr] using (hle_union.trans (hle.trans_eq htrans))

end BoundaryControl

end PeriodicConstantApprox

namespace SpherePacking

open Filter

variable {d : ℕ}

lemma frequently_lt_finiteDensity_of_lt_density (S : SpherePacking d) {b : ℝ≥0∞}
    (hb : b < S.density) : ∃ᶠ R in (atTop : Filter ℝ), b < S.finiteDensity R := by
  exact frequently_lt_of_lt_limsup (u := S.finiteDensity) (b := b)
    (h := by simpa [SpherePacking.density] using hb)

lemma finite_centers_inter_ball_set (S : SpherePacking d) (R : ℝ) :
    (S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).Finite := by
  simpa [Set.finite_coe_iff] using (SpherePacking.finite_centers_inter_ball (S := S) (R := R))

end SpherePacking

namespace PeriodicConstantApprox

open Filter

variable {d : ℕ}

def shellVec (d : ℕ) (c : ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun _ : Fin d => c)

lemma coordCubeInner_one_subset_shell (L : ℝ) :
    coordCubeInner (d := d) L 1 ⊆
      (shellVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner (d := d) (L + 1) 0 := by
  intro x hx
  refine (Set.mem_vadd_set_iff_neg_vadd_mem).2 ?_
  have hx' : ∀ i : Fin d, x.ofLp i ∈ Set.Icc (1 : ℝ) (L - 1) := by
    simpa [coordCubeInner, Set.mem_setOf_eq] using hx
  simp only [coordCubeInner, Set.mem_setOf_eq, shellVec, vadd_eq_add, one_div, WithLp.ofLp_add,
    WithLp.ofLp_neg, Pi.add_apply, Pi.neg_apply, neg_neg]
  exact fun i => by
    let hxi := hx' i
    refine ⟨by linarith [hxi.1], by linarith [hxi.2]⟩

lemma volume_cubeShell_eq (L : ℝ) :
    volume (((shellVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner (d := d) (L + 1) 0) \
        coordCubeInner (d := d) L 1) =
      volume (coordCubeInner (d := d) (L + 1) 0) - volume (coordCubeInner (d := d) L 1) := by
  have hsub :
      coordCubeInner (d := d) L 1 ⊆
        (shellVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner (d := d) (L + 1) 0 :=
    coordCubeInner_one_subset_shell (d := d) L
  have hmeas_inner : MeasurableSet (coordCubeInner (d := d) L 1) := by
    have hmeasPi :
        MeasurableSet (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc (1 : ℝ) (L - 1)) := by
      refine MeasurableSet.pi Set.countable_univ ?_
      intro _ _
      exact measurableSet_Icc
    have hmp : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) := by
      simpa using (PiLp.volume_preserving_ofLp (ι := Fin d))
    simpa [PeriodicConstant.coordCubeInner_eq_preimage_ofLp (d := d) (L := L) (r := (1 : ℝ))] using
      hmeasPi.preimage hmp.measurable
  have hfin : volume (coordCubeInner (d := d) L 1) ≠ ∞ := by
    simp [PeriodicConstant.volume_coordCubeInner]
  simpa [measure_vadd, shellVec] using
    (measure_diff (μ := volume) hsub hmeas_inner.nullMeasurableSet hfin)

lemma volume_cubeShell_eq_pow (L : ℝ) :
    volume (((shellVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner (d := d) (L + 1) 0) \
        coordCubeInner (d := d) L 1) =
      (ENNReal.ofReal (L + 1)) ^ d - (ENNReal.ofReal (L - 2)) ^ d := by
  rw [volume_cubeShell_eq (d := d) (L := L)]
  simp [PeriodicConstant.volume_coordCubeInner]

section BoundaryControlShellVec

open scoped ENNReal Pointwise BigOperators
open SpherePacking EuclideanSpace MeasureTheory Metric

variable {d : ℕ}
variable (S : SpherePacking d)

lemma card_mul_volume_ball_le_volume_cubeShell {L : ℝ} (hL : 0 < L)
    (hSsep : S.separation = 1)
    {g : cubeLattice (d := d) L hL} {s : Finset (EuclideanSpace ℝ (Fin d))}
    (hs_centers : ∀ x ∈ s, x ∈ S.centers)
    (hs_boundary : ∀ x ∈ s,
      x ∈ (g +ᵥ coordCube (d := d) L) \ (g +ᵥ coordCubeInner (d := d) L (1 / 2))) :
    (s.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ)) ≤
      volume (((shellVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner (d := d) (L + 1) 0) \
          coordCubeInner (d := d) L 1) := by simpa [shellVec, constVec] using
    card_mul_volume_ball_le_volume_outer_diff_inner (S := S) hL hSsep hs_centers hs_boundary

end BoundaryControlShellVec

section CubeLatticeCovolume

open scoped ENNReal
open ZSpan

lemma covolume_cubeLattice_eq_volume_coordCube_toReal (L : ℝ) (hL : 0 < L) :
    ZLattice.covolume (cubeLattice (d := d) L hL) volume =
      (volume (coordCube (d := d) L)).toReal := by
  letI : DiscreteTopology (cubeLattice (d := d) L hL) := by dsimp [cubeLattice]; infer_instance
  letI : IsZLattice ℝ (cubeLattice (d := d) L hL) := by dsimp [cubeLattice]; infer_instance
  have hfund :
      IsAddFundamentalDomain (cubeLattice (d := d) L hL)
        (fundamentalDomain (cubeBasis (d := d) L hL)) volume := by
    simpa [cubeLattice] using (ZSpan.isAddFundamentalDomain (cubeBasis (d := d) L hL) volume)
  simpa [Measure.real, fundamentalDomain_cubeBasis_eq_coordCube (d := d) (L := L) (hL := hL)] using
    (ZLattice.covolume_eq_measure_fundamentalDomain (L := cubeLattice (d := d) L hL)
      (μ := volume) hfund)

lemma toNNReal_covolume_cubeLattice (L : ℝ) (hL : 0 < L) :
    Real.toNNReal (ZLattice.covolume (cubeLattice (d := d) L hL) volume) =
      (volume (coordCube (d := d) L)).toNNReal := by
  simp [covolume_cubeLattice_eq_volume_coordCube_toReal (d := d) (L := L) hL]

end CubeLatticeCovolume

section PeriodizeCubeDensity

open scoped ENNReal Pointwise
open SpherePacking EuclideanSpace MeasureTheory Metric Bornology

variable {d : ℕ}

lemma periodize_cube_density_eq (hd : 0 < d) (S : SpherePacking d) (hSsep : S.separation = 1)
    {L : ℝ} (hL : 0 < L) {g : cubeLattice (d := d) L hL}
    (F : Finset (EuclideanSpace ℝ (Fin d)))
    (hF_centers : ∀ x ∈ F, x ∈ S.centers)
    (hF_inner : ∀ x ∈ F, x ∈ g +ᵥ coordCubeInner (d := d) L (2⁻¹ : ℝ)) :
    ∃ P : PeriodicSpherePacking d,
      P.separation = 1 ∧
        P.density =
          (F.card : ℝ≥0∞) *
              volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ)) /
            Real.toNNReal (ZLattice.covolume (cubeLattice (d := d) L hL) volume) := by
  let Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)) := cubeLattice (d := d) L hL
  let D : Set (EuclideanSpace ℝ (Fin d)) := g +ᵥ coordCube (d := d) L
  let Fset : Set (EuclideanSpace ℝ (Fin d)) := (F : Set (EuclideanSpace ℝ (Fin d)))
  letI : DiscreteTopology Λ := by
    dsimp [Λ, cubeLattice]
    infer_instance
  letI : IsZLattice ℝ Λ := by
    dsimp [Λ, cubeLattice]
    infer_instance
  let P : PeriodicSpherePacking d :=
    periodize_to_periodicSpherePacking (d := d) S (Λ := Λ) D Fset
      (hD_unique_covers := PeriodicConstantApprox.coordCube_unique_covers_vadd (d := d) L hL g)
      (hF_centers := by
        assumption)
      (hF_ball := by
        intro x hx
        have hx' : x ∈ F := by simpa [Fset] using hx
        have hxInner : x ∈ g +ᵥ coordCubeInner (d := d) L (S.separation / 2) := by
          simpa [hSsep] using (hF_inner x hx')
        exact ball_subset_vadd_coordCube_of_mem_vadd_inner hL hxInner)
  have hPsep : P.separation = 1 := by simpa [P, hSsep]
  refine ⟨P, hPsep, ?_⟩
  have hD_bounded : IsBounded D := by
    simpa [D, Submodule.vadd_def, vadd_eq_add] using
      (PeriodicConstant.isBounded_coordCube (d := d) L hL).vadd (g : EuclideanSpace ℝ (Fin d))
  have hD_unique : ∀ x, ∃! g0 : (cubeLattice (d := d) L hL), g0 +ᵥ x ∈ D :=
    PeriodicConstantApprox.coordCube_unique_covers_vadd (d := d) L hL g
  have hF_sub : Fset ⊆ D := by
    intro x hx
    have hx' : x ∈ F := by simpa [Fset] using hx
    rcases (hF_inner x hx') with ⟨a, ha, rfl⟩
    have ha' : a ∈ coordCube (d := d) L :=
      PeriodicConstant.coordCubeInner_subset_coordCube (d := d) (L := L) (r := (2⁻¹ : ℝ))
        (by norm_num) ha
    exact ⟨a, ha', rfl⟩
  have hcenters_inter :
      P.centers ∩ D = Fset := by
    simpa [P, periodize_to_periodicSpherePacking, Fset] using
      (periodizedCenters_inter_eq_of_subset (d := d) (Λ := cubeLattice (d := d) L hL) (D := D)
        (F := Fset) hF_sub hD_unique)
  have hnumReps : P.numReps = F.card := by
    have h' : (P.numReps : ENat) = (F.card : ENat) := by
      simpa [hcenters_inter, Fset, Set.encard_coe_eq_coe_finsetCard] using
        (P.encard_centers_inter_isFundamentalDomain (d := d) (D := D) hD_bounded hD_unique hd).symm
    exact_mod_cast h'
  simpa [hnumReps, hPsep] using P.density_eq' (d := d) hd

end PeriodizeCubeDensity

lemma tendsto_cubeShell_ratio_zero :
    Tendsto (fun L : ℝ => ((L + 1) ^ d - (L - 2) ^ d) / (L ^ d)) atTop (𝓝 (0 : ℝ)) := by
  have hL0 : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have htwo : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (𝓝 (2 : ℝ)) :=
    tendsto_const_nhds
  have h1 : Tendsto (fun L : ℝ => (1 + L⁻¹) ^ d) atTop (𝓝 (1 : ℝ)) := by
    simpa using (hone.add hL0).pow d
  have h2 : Tendsto (fun L : ℝ => (1 - 2 * L⁻¹) ^ d) atTop (𝓝 (1 : ℝ)) := by
    simpa using (hone.sub (htwo.mul hL0)).pow d
  have hdiff : Tendsto (fun L : ℝ => (1 + L⁻¹) ^ d - (1 - 2 * L⁻¹) ^ d) atTop (𝓝 (0 : ℝ)) := by
    simpa using (h1.sub h2)
  have hEq :
      (fun L : ℝ => ((L + 1) ^ d - (L - 2) ^ d) / (L ^ d)) =ᶠ[atTop]
        fun L : ℝ => (1 + L⁻¹) ^ d - (1 - 2 * L⁻¹) ^ d := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hLpos
    have hL : L ≠ 0 := ne_of_gt hLpos
    have hLd : L ^ d ≠ 0 := by positivity
    -- rewrite by dividing each term by `L^d` and using `div_pow`
    calc
      ((L + 1) ^ d - (L - 2) ^ d) / (L ^ d)
          = (L + 1) ^ d / (L ^ d) - (L - 2) ^ d / (L ^ d) := by
              simp [sub_div]
      _ = ((L + 1) / L) ^ d - ((L - 2) / L) ^ d := by
              simp [div_pow]
      _ = (1 + L⁻¹) ^ d - (1 - 2 * L⁻¹) ^ d := by
              have h1' : (L + 1) / L = (1 : ℝ) + L⁻¹ := by
                field_simp [hL]
              have h2' : (L - 2) / L = (1 : ℝ) - 2 * L⁻¹ := by
                field_simp [hL]
              simp [h1', h2']
  exact hdiff.congr' hEq.symm

lemma tendsto_volume_cubeShell_div_volume_coordCube_zero :
    Tendsto
        (fun L : ℝ =>
          volume (((shellVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner (d := d) (L + 1) 0) \
              coordCubeInner (d := d) L 1) /
            volume (coordCube (d := d) L))
        atTop (𝓝 (0 : ℝ≥0∞)) := by
  let f : ℝ → ℝ := fun L : ℝ => ((L + 1) ^ d - (L - 2) ^ d) / (L ^ d)
  have hf : Tendsto f atTop (𝓝 (0 : ℝ)) := by
    simpa [f] using (tendsto_cubeShell_ratio_zero (d := d))
  have hof : Tendsto (fun L : ℝ => ENNReal.ofReal (f L)) atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hf
  have hEq :
      (fun L : ℝ =>
          volume (((shellVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner (d := d) (L + 1) 0) \
              coordCubeInner (d := d) L 1) /
            volume (coordCube (d := d) L)) =ᶠ[atTop]
        fun L : ℝ => ENNReal.ofReal (f L) := by
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with L hL2
    have hL0 : 0 ≤ L := le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 2) hL2)
    have hL1 : 0 ≤ L + 1 := by linarith
    have hL2' : 0 ≤ L - 2 := by linarith
    have hLpos : 0 < L := lt_trans (by norm_num : (0 : ℝ) < 2) hL2
    have hLdpos : 0 < L ^ d := pow_pos hLpos d
    have hshell :
        volume (((shellVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner (d := d) (L + 1) 0) \
            coordCubeInner (d := d) L 1) =
          (ENNReal.ofReal (L + 1)) ^ d - (ENNReal.ofReal (L - 2)) ^ d := by
      simpa using (volume_cubeShell_eq_pow (d := d) (L := L))
    have hcube :
        volume (coordCube (d := d) L) = (ENNReal.ofReal L) ^ d := by
      simpa using (PeriodicConstant.volume_coordCube (d := d) (L := L))
    have hnum :
        (ENNReal.ofReal (L + 1)) ^ d - (ENNReal.ofReal (L - 2)) ^ d =
          ENNReal.ofReal ((L + 1) ^ d - (L - 2) ^ d) := by
      have hq : 0 ≤ (L - 2) ^ d := pow_nonneg hL2' d
      -- rewrite both powers as `ofReal` of real powers, then use `ofReal_sub`
      calc
        (ENNReal.ofReal (L + 1)) ^ d - (ENNReal.ofReal (L - 2)) ^ d
            = ENNReal.ofReal ((L + 1) ^ d) - ENNReal.ofReal ((L - 2) ^ d) := by
                rw [← ENNReal.ofReal_pow hL1 d, ← ENNReal.ofReal_pow hL2' d]
        _ = ENNReal.ofReal ((L + 1) ^ d - (L - 2) ^ d) := by
                simpa using
                  (ENNReal.ofReal_sub (p := (L + 1) ^ d) (q := (L - 2) ^ d) hq).symm
    have hden :
        (ENNReal.ofReal L) ^ d = ENNReal.ofReal (L ^ d) := by
      simpa using (ENNReal.ofReal_pow hL0 d).symm
    -- finish by rewriting in terms of `ENNReal.ofReal`
    rw [hshell, hcube, hnum, hden]
    simpa [f] using
      (ENNReal.ofReal_div_of_pos (x := (L + 1) ^ d - (L - 2) ^ d) (y := L ^ d) hLdpos).symm
  exact hof.congr' hEq.symm

end PeriodicConstantApprox

namespace SpherePacking

open Filter
open scoped ENNReal BigOperators

variable {d : ℕ}

lemma div_mul_div_cancel_right {a b c : ℝ≥0∞} (hb0 : b ≠ 0) (hb : b ≠ ∞) :
    ((a * b) / c) / b = a / c := by
  calc
    ((a * b) / c) / b = (a * b) * c⁻¹ * b⁻¹ := by
      simp [div_eq_mul_inv, mul_assoc]
    _ = a * c⁻¹ * (b * b⁻¹) := by
      ac_rfl
    _ = a / c := by
      simp [div_eq_mul_inv, ENNReal.mul_inv_cancel hb0 hb]

theorem exists_periodicSpherePacking_sep_one_density_gt_of_lt_density (hd : 0 < d)
    (S : SpherePacking d) (hSsep : S.separation = 1) {b : ℝ≥0∞} (hb : b < S.density) :
    ∃ P : PeriodicSpherePacking d, P.separation = 1 ∧ b < P.density := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  -- Choose `c` with `b < c < S.density`.
  rcases exists_between hb with ⟨c, hbc, hcS⟩
  have hc_sub : 0 < c - b := tsub_pos_of_lt hbc
  -- Cube-shell error as a function of `L`.
  let cubeShellErr : ℝ → ℝ≥0∞ := fun L : ℝ =>
    volume (((PeriodicConstantApprox.shellVec (d := d) (- (1 / 2 : ℝ))) +ᵥ
        coordCubeInner (d := d) (L + 1) 0) \ coordCubeInner (d := d) L 1) /
      volume (coordCube (d := d) L)
  have hLevent : ∀ᶠ L in (atTop : Filter ℝ), cubeShellErr L < c - b := by
    have htend : Tendsto cubeShellErr atTop (𝓝 (0 : ℝ≥0∞)) := by
      simpa [cubeShellErr] using
        (PeriodicConstantApprox.tendsto_volume_cubeShell_div_volume_coordCube_zero (d := d))
    exact htend.eventually (Iio_mem_nhds hc_sub)
  rcases ((eventually_gt_atTop (0 : ℝ)).and hLevent).exists with ⟨L, hLpos, hLerr⟩
  -- A bounding radius `C` for the coordinate cube.
  rcases PeriodicConstantApprox.coordCube_subset_ball (d := d) L hLpos with ⟨C, hC⟩
  have hCpos : 0 < C := by
    have : (0 : EuclideanSpace ℝ (Fin d)) ∈ ball (0 : EuclideanSpace ℝ (Fin d)) C :=
      hC (by simp [coordCube, hLpos])
    simpa [Metric.mem_ball, dist_eq_norm] using this
  let r : ℝ := (2⁻¹ : ℝ)
  let Cshift : ℝ := r + 2 * C
  let ratio : ℝ → ℝ≥0∞ := fun R : ℝ =>
    volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) /
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift))
  have hratio_tend : Tendsto ratio atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa [ratio, Cshift, add_zero] using
      (volume_ball_ratio_tendsto_nhds_one'' (d := d) (C := (0 : ℝ)) (C' := Cshift) hd)
  have hmul_tend : Tendsto (fun R : ℝ => c * ratio R) atTop (𝓝 c) := by
    simpa [mul_one] using (ENNReal.Tendsto.const_mul hratio_tend (a := c))
  have hb_add : b + cubeShellErr L < c := lt_tsub_iff_left.mp hLerr
  have hratio_event :
      ∀ᶠ R in (atTop : Filter ℝ), b + cubeShellErr L < c * ratio R :=
    hmul_tend.eventually (Ioi_mem_nhds hb_add)
  have hfreq : ∃ᶠ R in (atTop : Filter ℝ), c < S.finiteDensity R :=
    frequently_lt_finiteDensity_of_lt_density (S := S) (b := c) hcS
  have hfreq' :
      ∃ᶠ R in (atTop : Filter ℝ),
        c < S.finiteDensity R ∧ 0 < R ∧ b + cubeShellErr L < c * ratio R := by
    have hev : ∀ᶠ R in (atTop : Filter ℝ), 0 < R ∧ b + cubeShellErr L < c * ratio R :=
      (eventually_gt_atTop (0 : ℝ)).and hratio_event
    exact hfreq.and_eventually hev
  rcases hfreq'.exists with ⟨R, hcR, hRpos, hRratio⟩
  -- Abbreviations for volumes.
  let volBall : ℝ≥0∞ := volume (ball (0 : EuclideanSpace ℝ (Fin d)) r)
  let volCube : ℝ≥0∞ := volume (coordCube (d := d) L)
  let shellVol : ℝ≥0∞ :=
    volume (((PeriodicConstantApprox.shellVec (d := d) (- (1 / 2 : ℝ))) +ᵥ
        coordCubeInner (d := d) (L + 1) 0) \ coordCubeInner (d := d) L 1)
  have hcubeShell : cubeShellErr L = shellVol / volCube := by
    simp [cubeShellErr, shellVol, volCube]
  have hvolCube_ne0 : volCube ≠ 0 := by
    have hvol : volCube = (ENNReal.ofReal L) ^ d := by
      simpa [volCube] using (PeriodicConstant.volume_coordCube (d := d) (L := L))
    have hL' : (ENNReal.ofReal L) ≠ 0 := by
      exact (ne_of_gt (by simpa [ENNReal.ofReal_pos] using hLpos))
    simpa [hvol] using pow_ne_zero d hL'
  have hvolCube_ne_top : volCube ≠ ∞ := by
    have hbounded : IsBounded (coordCube (d := d) L) :=
      PeriodicConstant.isBounded_coordCube (d := d) L hLpos
    simpa [volCube] using (hbounded.measure_lt_top (μ := volume)).ne
  -- Convert `hcR` to a strict inequality involving `encard` of centers in `ball 0 (R+r)`.
  have hcR' :
      c <
        ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) *
            volBall /
          volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    have hle :
        S.finiteDensity R ≤
          (S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard *
              volBall /
            volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
      simpa [hSsep, volBall, r, add_assoc, add_left_comm, add_comm] using
        (S.finiteDensity_le (hd := hd) (R := R))
    exact lt_of_lt_of_le hcR hle
  have hvolR_ne0 : volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) ≠ 0 :=
    (volume_ball_pos _ hRpos).ne.symm
  have hvolR_ne_top : volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) ≠ ∞ :=
    (volume_ball_lt_top _).ne
  have hc_mul :
      c * volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) <
        ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) * volBall :=
    ENNReal.mul_lt_of_lt_div hcR'
  have hvolR2_ne0 : volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) ≠ 0 := by
    have hR2pos : 0 < R + Cshift := by positivity
    exact (volume_ball_pos _ hR2pos).ne.symm
  have hvolR2_ne_top : volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) ≠ ∞ :=
    (volume_ball_lt_top _).ne
  have hc_ratio :
      c * ratio R <
        ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) * volBall /
          volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) := by
    have hdiv :
        c * volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) /
              volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) <
          ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) *
              volBall /
            volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) :=
      ENNReal.div_lt_div_right hvolR2_ne0 hvolR2_ne_top hc_mul
    simpa [ratio, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
  -- Finite sets of centers and lattice translates.
  let R₁ : ℝ := R + r
  have hX : (S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R₁).Finite :=
    finite_centers_inter_ball_set (S := S) R₁
  let s : Finset (EuclideanSpace ℝ (Fin d)) := hX.toFinset
  let htSet := PeriodicConstantApprox.finite_lattice_in_ball (d := d) L hLpos (R₁ + C)
  let t : Finset (cubeLattice (d := d) L hLpos) := htSet.toFinset
  let f : EuclideanSpace ℝ (Fin d) → cubeLattice (d := d) L hLpos := fun x =>
    -PeriodicConstantApprox.coordCubeCover (d := d) L hLpos x
  have hf_maps : (s : Set (EuclideanSpace ℝ (Fin d))).MapsTo f t := by
    intro x hx
    have hx_mem : x ∈ S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R₁ := by
      simpa [s] using (hX.mem_toFinset.1 hx)
    have hx_ball : x ∈ ball 0 R₁ := hx_mem.2
    have hx_gball :
        (f x : EuclideanSpace ℝ (Fin d)) ∈ ball 0 (R₁ + C) :=
      PeriodicConstantApprox.neg_coordCubeCover_mem_ball L hLpos hC hx_ball
    have : f x ∈ {g : cubeLattice (d := d) L hLpos |
        (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 (R₁ + C)} := by
      simpa using hx_gball
    exact htSet.mem_toFinset.2 this
  have ht_nonempty : t.Nonempty := by
    refine ⟨0, ?_⟩
    have hpos : 0 < R₁ + C := by
      dsimp [R₁, r]
      nlinarith [hRpos, hCpos]
    have : (0 : cubeLattice (d := d) L hLpos) ∈ htSet.toFinset :=
      htSet.mem_toFinset.2 (by simp [Metric.mem_ball, hpos])
    simpa [t] using this
  let fiber : cubeLattice (d := d) L hLpos → ℕ := fun g =>
    (s.filter fun x : EuclideanSpace ℝ (Fin d) => f x = g).card
  rcases Finset.exists_max_image t fiber ht_nonempty with ⟨g0, hg0t, hg0max⟩
  let sg : Finset (EuclideanSpace ℝ (Fin d)) := s.filter fun x => f x = g0
  -- `sg` is the fiber at `g0`.
  have hsg_centers : ∀ x ∈ sg, x ∈ S.centers := by
    intro x hx
    have hx' : x ∈ S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R₁ := by
      simpa [sg, s] using hX.mem_toFinset.1 (Finset.mem_filter.1 hx).1
    exact hx'.1
  have hsg_memCube : ∀ x ∈ sg, x ∈ g0 +ᵥ coordCube (d := d) L := by
    intro x hx
    have hx_f : f x = g0 := (Finset.mem_filter.1 hx).2
    exact (PeriodicConstantApprox.mem_vadd_coordCube_iff_eq_neg_coordCubeCover L hLpos g0 x).mpr
      (id (Eq.symm hx_f))
  -- The maximal fiber gives a density lower bound.
  have hs_sum :
      s.card =
        Finset.sum t (fun g => (s.filter fun x : EuclideanSpace ℝ (Fin d) => f x = g).card) := by
    -- `card_eq_sum_card_fiberwise` counts elements fiberwise over `t`.
    simpa [fiber] using (Finset.card_eq_sum_card_fiberwise (f := f) (s := s) (t := t) hf_maps)
  have hs_le : (s.card : ℝ≥0∞) ≤ (t.card : ℝ≥0∞) * (sg.card : ℝ≥0∞) := by
    -- bound the sum of fibers by `t.card * maxFiber`
    have hsum_le :
        Finset.sum t (fun g => (s.filter fun x => f x = g).card) ≤
          Finset.sum t (fun _g => sg.card) := Finset.sum_le_sum hg0max
    have hsum_eq : Finset.sum t (fun _g => sg.card) = t.card * sg.card := by
      simp [Finset.sum_const]
    have hs_le_nat : s.card ≤ t.card * sg.card := by
      -- all the quantities here are naturals
      simpa [hs_sum, hsum_eq] using hsum_le
    exact_mod_cast hs_le_nat
  have ht_vol :
      ((t.card : ℝ≥0∞) * volCube) ≤
        volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R₁ + 2 * C)) := by
    simpa [volCube, R₁, r, t, htSet] using
      (PeriodicConstantApprox.card_finite_lattice_in_ball_mul_volume_coordCube_le_volume_ball
        (d := d) (hL := hLpos) (R := R₁) (C := C) hC)
  have hs_mul :
      ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) * volCube ≤
        (sg.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) := by
    have hs_enc :
        ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) = s.card := by
      -- `s` is the `toFinset` of this set
      have hfin : (S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).Finite := by
        simpa [R₁, r, add_assoc, add_left_comm, add_comm] using hX
      simpa [s] using congrArg (fun n : ENat => (n : ℝ≥0∞)) (hfin.encard_eq_coe_toFinset_card)
    have hs1 :
        ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) * volCube ≤
          (t.card : ℝ≥0∞) * (sg.card : ℝ≥0∞) * volCube := by
      have hs1' :
          volCube * (s.card : ℝ≥0∞) ≤ volCube * ((t.card : ℝ≥0∞) * (sg.card : ℝ≥0∞)) :=
        mul_le_mul_right hs_le volCube
      have hL : volCube * (s.card : ℝ≥0∞) = (s.card : ℝ≥0∞) * volCube := by
        ac_rfl
      have hR :
          volCube * ((t.card : ℝ≥0∞) * (sg.card : ℝ≥0∞)) =
            (t.card : ℝ≥0∞) * (sg.card : ℝ≥0∞) * volCube := by
        ac_rfl
      have hs1'' :
          (s.card : ℝ≥0∞) * volCube ≤ (t.card : ℝ≥0∞) * (sg.card : ℝ≥0∞) * volCube := by
        simpa [hL, hR] using hs1'
      simpa [hs_enc] using hs1''
    have hR2 : R + Cshift = R₁ + 2 * C := by
      simp [Cshift, R₁, r, add_left_comm, add_comm]
    have ht_vol' :
        (t.card : ℝ≥0∞) * volCube ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) := by
      simpa [hR2, volCube] using ht_vol
    have hs2 :
        (t.card : ℝ≥0∞) * (sg.card : ℝ≥0∞) * volCube ≤
          (sg.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) := by
      have hs2' :
          (sg.card : ℝ≥0∞) * ((t.card : ℝ≥0∞) * volCube) ≤
            (sg.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) :=
        mul_le_mul_right ht_vol' (sg.card : ℝ≥0∞)
      have hL :
          (sg.card : ℝ≥0∞) * ((t.card : ℝ≥0∞) * volCube) =
            (t.card : ℝ≥0∞) * (sg.card : ℝ≥0∞) * volCube := by
        ac_rfl
      simpa [hL] using hs2'
    exact hs1.trans hs2
  have hsg_density :
      b + cubeShellErr L < (sg.card : ℝ≥0∞) * volBall / volCube := by
    have hb1 : b + cubeShellErr L < c * ratio R := hRratio
    have hb2 : c * ratio R <
        ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) * volBall /
          volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) := hc_ratio
    have hb3 :
        ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) * volBall /
          volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) ≤
          (sg.card : ℝ≥0∞) * volBall / volCube := by
      -- First compare `encard / volR2 ≤ sg.card / volCube` using `hs_mul`
      -- then multiply by `volBall`.
      have hdiv₁ :
          ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) /
              volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) ≤
            (sg.card : ℝ≥0∞) / volCube := by
        have h₁ :
            (((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) * volCube) /
                volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) ≤
              (sg.card : ℝ≥0∞) :=
          ENNReal.div_le_of_le_mul hs_mul
        have h₂ :
            ((((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) * volCube) /
                    volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift))) /
                volCube ≤
              (sg.card : ℝ≥0∞) / volCube :=
          ENNReal.div_le_div_right h₁ volCube
        have hcancel :
            ((((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) * volCube) /
                    volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift))) /
                volCube =
              ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) /
                volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) :=
          div_mul_div_cancel_right hvolCube_ne0 hvolCube_ne_top
        simpa [hcancel] using h₂
      have hdiv₂ :
          (((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) /
                volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift))) *
              volBall ≤
            ((sg.card : ℝ≥0∞) / volCube) * volBall := mul_le_mul_left hdiv₁ volBall
      have hL :
          ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) * volBall /
              volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) =
            (((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) /
                  volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift))) *
                volBall := by
        simp [div_eq_mul_inv]
        ac_rfl
      have hR :
          (sg.card : ℝ≥0∞) * volBall / volCube = ((sg.card : ℝ≥0∞) / volCube) * volBall := by
        simp [div_eq_mul_inv]
        ac_rfl
      simpa [hL, hR] using hdiv₂
    have hb12 :
        b + cubeShellErr L <
          ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞) * volBall /
            volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) :=
      lt_trans hb1 hb2
    exact lt_of_lt_of_le hb12 hb3
  -- Periodize the interior points `F`.
  let innerSet : Set (EuclideanSpace ℝ (Fin d)) := g0 +ᵥ coordCubeInner (d := d) L r
  letI : DecidablePred (fun x : EuclideanSpace ℝ (Fin d) => x ∈ innerSet) := Classical.decPred _
  let F : Finset (EuclideanSpace ℝ (Fin d)) := sg.filter fun x => x ∈ innerSet
  let sb : Finset (EuclideanSpace ℝ (Fin d)) := sg.filter fun x => x ∉ innerSet
  have hF_centers : ∀ x ∈ F, x ∈ S.centers := by
    intro x hx
    have hx' := hx
    dsimp [F] at hx'
    exact hsg_centers x (Finset.mem_filter.1 hx').1
  have hF_inner : ∀ x ∈ F, x ∈ g0 +ᵥ coordCubeInner (d := d) L r := by
    intro x hx
    have hx' := hx
    dsimp [F] at hx'
    have hx' : x ∈ innerSet := (Finset.mem_filter.1 hx').2
    simpa [innerSet] using hx'
  have hsb_centers : ∀ x ∈ sb, x ∈ S.centers := by
    intro x hx
    have hx' := hx
    dsimp [sb] at hx'
    exact hsg_centers x (Finset.mem_filter.1 hx').1
  have hsb_boundary :
      ∀ x ∈ sb, x ∈ (g0 +ᵥ coordCube (d := d) L) \ (g0 +ᵥ coordCubeInner (d := d) L (1 / 2)) := by
    intro x hx
    have hx_sb := hx
    dsimp [sb] at hx_sb
    have hx_mem := Finset.mem_filter.1 hx_sb
    have hx_sg : x ∈ sg := hx_mem.1
    have hxCube : x ∈ g0 +ᵥ coordCube (d := d) L := hsg_memCube x hx_sg
    have hxnot : x ∉ innerSet := hx_mem.2
    have hr : (r : ℝ) = (1 / 2 : ℝ) := by
      dsimp [r]
      norm_num
    have hxnot' : x ∉ g0 +ᵥ coordCubeInner (d := d) L (1 / 2) := by
      simpa [innerSet, hr] using hxnot
    exact ⟨hxCube, hxnot'⟩
  have hsb_vol :
      (sb.card : ℝ≥0∞) * volBall ≤ shellVol := by
    simpa [volBall, shellVol, r] using
      (PeriodicConstantApprox.card_mul_volume_ball_le_volume_cubeShell (d := d) (S := S) hLpos hSsep
        (g := g0) (s := sb) hsb_centers hsb_boundary)
  rcases PeriodicConstantApprox.periodize_cube_density_eq (d := d) hd S hSsep hLpos (g := g0) F
      hF_centers hF_inner with ⟨P, hPsep, hPdens⟩
  -- Rewrite `P.density` with denominator `volCube`.
  have hden :
      (Real.toNNReal (ZLattice.covolume (cubeLattice (d := d) L hLpos) volume) : ℝ≥0∞) = volCube :=
      by
    have : Real.toNNReal (ZLattice.covolume (cubeLattice (d := d) L hLpos) volume) =
        volCube.toNNReal := by
      simpa [volCube] using (PeriodicConstantApprox.toNNReal_covolume_cubeLattice
        (d := d) (L := L) hLpos)
    simp [this, ENNReal.coe_toNNReal hvolCube_ne_top]
  have hPdens' : P.density = (F.card : ℝ≥0∞) * volBall / volCube := by
    simpa [hden, volBall] using hPdens
  refine ⟨P, hPsep, ?_⟩
  -- `b < sgDensity - cubeShellErr L ≤ P.density`.
  have hb_lt : b < (sg.card : ℝ≥0∞) * volBall / volCube - cubeShellErr L :=
    lt_tsub_iff_right.mpr hsg_density
  have hF_card_add : F.card + sb.card = sg.card :=
    Finset.card_filter_add_card_filter_not fun x => x ∈ innerSet
  have hP_lower :
      (sg.card : ℝ≥0∞) * volBall / volCube - cubeShellErr L ≤ P.density := by
    -- show `sgDensity ≤ P.density + cubeShellErr L`, then rewrite with `tsub_le_iff_right`
    have hsg_eq :
        (sg.card : ℝ≥0∞) * volBall =
          (F.card : ℝ≥0∞) * volBall + (sb.card : ℝ≥0∞) * volBall := by
      have : (sg.card : ℝ≥0∞) = (F.card : ℝ≥0∞) + (sb.card : ℝ≥0∞) := by
        exact_mod_cast hF_card_add.symm
      simp [this, add_mul]
    have hsg_le :
        (sg.card : ℝ≥0∞) * volBall ≤ (F.card : ℝ≥0∞) * volBall + shellVol := by
      have h_add :
          (F.card : ℝ≥0∞) * volBall + (sb.card : ℝ≥0∞) * volBall ≤
            (F.card : ℝ≥0∞) * volBall + shellVol :=
        add_le_add_right hsb_vol ((F.card : ℝ≥0∞) * volBall)
      simpa [hsg_eq] using h_add
    have hsg_div :
        (sg.card : ℝ≥0∞) * volBall / volCube ≤
          (F.card : ℝ≥0∞) * volBall / volCube + cubeShellErr L := by
      have hdiv := ENNReal.div_le_div_right hsg_le volCube
      have hdiv' :
          (sg.card : ℝ≥0∞) * volBall / volCube ≤
            (F.card : ℝ≥0∞) * volBall / volCube + shellVol / volCube := by
        simpa [div_eq_mul_inv, mul_add, add_mul, mul_assoc] using hdiv
      simpa [hcubeShell, shellVol] using hdiv'
    have hmain : (sg.card : ℝ≥0∞) * volBall / volCube ≤ P.density + cubeShellErr L := by
      simpa [hPdens'] using hsg_div
    exact (tsub_le_iff_right).2 (by simpa using hmain)
  exact hb_lt.trans_le hP_lower

end SpherePacking

/--
The periodic sphere packing constant equals the (a priori larger) sphere packing constant.

This packages the boundary control argument developed in this file.
-/
public theorem periodic_constant_eq_constant (hd : 0 < d) :
    PeriodicSpherePackingConstant d = SpherePackingConstant d := by
  -- Reduce to the normalized (`separation = 1`) version on both sides.
  rw [periodic_constant_eq_periodic_constant_normalized (d := d),
    SpherePacking.constant_eq_constant_normalized (d := d)]
  -- From now on, we compare the two normalized suprema.
  apply le_antisymm
  · -- periodic ≤ general
    refine iSup₂_le ?_
    intro P hPsep
    -- view a periodic packing as a (general) packing
    refine
      (le_iSup
          (fun _ : (P.toSpherePacking).separation = 1 ↦ (P.toSpherePacking).density)
          hPsep).trans ?_
    exact le_iSup (fun S : SpherePacking d ↦ ⨆ (_ : S.separation = 1), S.density) P.toSpherePacking
  · -- general ≤ periodic: approximate any packing by a periodic one
    refine iSup₂_le ?_
    intro S hSsep
    -- show `S.density ≤ sup_{periodic, sep=1} density` by approximation from below
    refine le_of_forall_lt ?_
    intro a ha
    -- choose `b` strictly between `a` and `S.density`
    rcases exists_between ha with ⟨b, hab, hbS⟩
    -- Approximate `S` by a periodic packing with (normalized) separation `= 1`.
    rcases SpherePacking.exists_periodicSpherePacking_sep_one_density_gt_of_lt_density
      (d := d) hd S hSsep hbS with
      ⟨P, hPsep, hbP⟩
    have hb_lt_sup : b < ⨆ (P : PeriodicSpherePacking d) (_ : P.separation = 1), P.density :=
      lt_of_lt_of_le hbP (le_iSup_of_le P (le_iSup_of_le hPsep le_rfl))
    exact hab.trans hb_lt_sup
