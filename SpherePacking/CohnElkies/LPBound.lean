/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module
public import Mathlib

public import SpherePacking.Basic.PeriodicPacking
public import SpherePacking.CohnElkies.PoissonSummationGeneral

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
public lemma abs_coord_le_norm (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |x i| ≤ ‖x‖ :=
  PiLp.norm_apply_le x i

/-- If `ball x r ⊆ A` and `ball y r ⊆ B` with `A` and `B` disjoint, then `2 * r ≤ dist x y`. -/
public lemma dist_le_of_disjoint_ball_subsets {x y : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    {A B : Set (EuclideanSpace ℝ (Fin d))}
    (hx : ball x r ⊆ A) (hy : ball y r ⊆ B) (hAB : Disjoint A B) : 2 * r ≤ dist x y := by
  by_cases hr : 0 < r
  · simpa [two_mul] using (disjoint_ball_ball_iff hr hr).1 (hAB.mono hx hy)
  · linarith [dist_nonneg (x := x) (y := y)]

/-- The union of all lattice translates `⋃ g : Λ, g +ᵥ F` of representatives `F`. Standalone as
the centre set of `periodize_to_periodicSpherePacking`, with its own membership/closure API. -/
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
  obtain ⟨g, f, hf, rfl⟩ := mem_periodizedCenters_iff.1 hy
  exact mem_periodizedCenters_iff.2 ⟨⟨x, hx⟩ + g, f, hf, (add_assoc x g f).symm⟩

/-- Translating a ball by a lattice vector stays inside the translate of the ambient set. -/
public lemma ball_vadd_subset_vadd {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {D : Set (EuclideanSpace ℝ (Fin d))} {r : ℝ} {g : Λ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : ball x r ⊆ D) : ball (g +ᵥ x) r ⊆ g +ᵥ D := by
  rw [Submodule.vadd_def, ← vadd_ball]
  exact Set.vadd_set_mono hx

/-- The periodic packing obtained by translating representatives `F ⊆ S.centers` along a lattice
`Λ`. The core construction turning a finite cell into a `PeriodicSpherePacking`. -/
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
    obtain ⟨ga, fa, hfa, ha⟩ := mem_periodizedCenters_iff.1 a.property
    obtain ⟨gb, fb, hfb, hb⟩ := mem_periodizedCenters_iff.1 b.property
    change S.separation ≤ dist (a : EuclideanSpace ℝ (Fin d)) b
    rw [ha, hb]
    by_cases hgg : ga = gb
    · subst hgg
      simp only [Submodule.vadd_def, dist_vadd_cancel_left]
      exact S.centers_dist' fa fb (hF_centers hfa) (hF_centers hfb)
        fun h => hab <| Subtype.ext <| by rw [ha, hb, h]
    · have hdist := dist_le_of_disjoint_ball_subsets
        (ball_vadd_subset_vadd (hF_ball fa hfa)) (ball_vadd_subset_vadd (hF_ball fb hfb))
        (disjoint_vadd_of_unique_covers (D := D) hD_unique_covers hgg)
      linarith [add_halves S.separation]
  lattice := Λ
  lattice_action := fun _ _ ↦ periodizedCenters_lattice_action
  lattice_discrete := inferInstance
  lattice_isZLattice := inferInstance

/-- The half-open coordinate cube `[0, L)^d`. Used pervasively as the fundamental domain of
`cubeLattice`; its membership API is `mem_coordCube`. -/
@[expose] public def coordCube (d : ℕ) (L : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, x i ∈ Set.Ico (0 : ℝ) L}

@[simp] public lemma mem_coordCube {L : ℝ} {x : EuclideanSpace ℝ (Fin d)} :
    x ∈ coordCube d L ↔ ∀ i, x i ∈ Set.Ico (0 : ℝ) L := Iff.rfl

/-- The closed inner cube `[r, L-r]^d`, the locus where a radius-`r` ball stays inside
`coordCube L`. Membership API: `mem_coordCubeInner`. -/
@[expose] public def coordCubeInner (d : ℕ) (L r : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, x i ∈ Set.Icc r (L - r)}

@[simp] public lemma mem_coordCubeInner {L r : ℝ} {x : EuclideanSpace ℝ (Fin d)} :
    x ∈ coordCubeInner d L r ↔ ∀ i, x i ∈ Set.Icc r (L - r) := Iff.rfl

/-- The standard basis of `EuclideanSpace ℝ (Fin d)` scaled by `L`; its span is `cubeLattice` and
its fundamental domain is `coordCube d L` (`fundamentalDomain_cubeBasis_eq_coordCube`). -/
@[expose] public noncomputable def cubeBasis (d : ℕ) (L : ℝ) (hL : 0 < L) :
    Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.isUnitSMul fun _ : Fin d ↦ IsUnit.mk0 L hL.ne'

/-- The cubic lattice `L • ℤ^d`, spanned by `cubeBasis d L hL`. Standalone so it can carry
`ZLattice`/`DiscreteTopology` instances and act as the period lattice of the cube packing. -/
@[expose] public noncomputable def cubeLattice (d : ℕ) (L : ℝ) (hL : 0 < L) :
    Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℤ (Set.range (cubeBasis d L hL))

instance instDiscreteTopology_cubeLattice (L : ℝ) (hL : 0 < L) :
    DiscreteTopology (cubeLattice d L hL) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (cubeBasis d L hL))))

instance instIsZLattice_cubeLattice (L : ℝ) (hL : 0 < L) :
    IsZLattice ℝ (cubeLattice d L hL) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (cubeBasis d L hL))))

/-- The fundamental domain of the scaled basis `cubeBasis d L hL` is the cube `[0, L)^d`. -/
public lemma fundamentalDomain_cubeBasis_eq_coordCube (L : ℝ) (hL : 0 < L) :
    fundamentalDomain (cubeBasis d L hL) = coordCube d L := by
  ext x
  simp only [ZSpan.mem_fundamentalDomain, coordCube, cubeBasis, Module.Basis.repr_isUnitSMul,
    Units.smul_def, Units.val_inv_eq_inv_val, IsUnit.unit_spec, smul_eq_mul,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr, Set.mem_setOf_eq,
    Set.mem_Ico]
  exact forall_congr' fun i =>
    and_congr (mul_nonneg_iff_of_pos_left (inv_pos.2 hL)) (inv_mul_lt_one₀ hL)

/-- A ball of radius `r` centred in the inner cube `[r, L-r]^d` is contained in `[0, L)^d`. -/
lemma ball_subset_coordCube_of_mem_inner {L r : ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ coordCubeInner d L r) : ball x r ⊆ coordCube d L := fun y hy i => by
  have h₁ : |y i - x i| ≤ ‖y - x‖ := by simpa using abs_coord_le_norm (y - x) i
  have h₂ : ‖y - x‖ < r := by simpa [dist_eq_norm] using hy
  obtain ⟨hlo, hhi⟩ := abs_lt.mp (h₁.trans_lt h₂)
  obtain ⟨hxl, hxr⟩ := hx i
  exact ⟨by linarith, by linarith⟩

/-- If `F ⊆ D` and every point has a unique lattice translate landing in `D`, then intersecting
the periodization of `F` with `D` recovers exactly `F`. -/
public lemma periodizedCenters_inter_eq_of_subset {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {D F : Set (EuclideanSpace ℝ (Fin d))}
    (hF_sub : F ⊆ D) (hD_unique_covers : ∀ x, ∃! g : Λ, g +ᵥ x ∈ D) :
    periodizedCenters (d := d) Λ F ∩ D = F := by
  ext x
  refine ⟨?_, fun hxF ↦
    ⟨mem_periodizedCenters_iff.2 ⟨0, x, hxF, (zero_vadd _ x).symm⟩, hF_sub hxF⟩⟩
  rintro ⟨hxP, hxD⟩
  obtain ⟨g, f, hfF, rfl⟩ := mem_periodizedCenters_iff.1 hxP
  obtain ⟨g₀, -, huniq⟩ := hD_unique_covers f
  have hg : g = 0 := (huniq g hxD).trans (huniq 0 (by simpa using hF_sub hfF)).symm
  simpa [hg] using hfF

namespace PeriodicConstant

private lemma volume_preimage_ofLp (s : Set (Fin d → ℝ)) (hs : MeasurableSet s) :
    volume ((fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹' s) = volume s :=
  (PiLp.volume_preserving_ofLp (ι := Fin d)).measure_preimage hs.nullMeasurableSet

/-- Every point has a unique `cubeLattice` translate lying in the cube `coordCube d L`. -/
public lemma coordCube_unique_covers (L : ℝ) (hL : 0 < L) :
    ∀ x, ∃! g : cubeLattice d L hL, g +ᵥ x ∈ coordCube d L := fun x => by
  simpa [cubeLattice, fundamentalDomain_cubeBasis_eq_coordCube L hL] using
    exist_unique_vadd_mem_fundamentalDomain (cubeBasis d L hL) x

/-- The cube `coordCube d L` is a bounded set. -/
public lemma isBounded_coordCube (L : ℝ) (hL : 0 < L) : IsBounded (coordCube d L) := by
  simpa [fundamentalDomain_cubeBasis_eq_coordCube L hL] using
    fundamentalDomain_isBounded (cubeBasis d L hL)

/-- The volume of the cube `[0, L)^d` is `L ^ d`. -/
public lemma volume_coordCube (L : ℝ) : volume (coordCube d L) = (ENNReal.ofReal L) ^ d := by
  have hcube : coordCube d L = (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
      (Set.pi Set.univ fun _ : Fin d ↦ Set.Ico (0 : ℝ) L) := by
    ext x; simp [mem_coordCube, Set.mem_pi]
  rw [hcube, volume_preimage_ofLp _ (.pi Set.countable_univ fun _ _ ↦ measurableSet_Ico),
    volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico, sub_zero]

/-- `coordCubeInner d L r` is the `ofLp`-preimage of the product set `[r, L - r]^d`. -/
public lemma coordCubeInner_eq_preimage_ofLp (L r : ℝ) :
    coordCubeInner d L r =
      (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
        (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc r (L - r)) := by
  ext x; simp [mem_coordCubeInner, Pi.le_def, forall_and]

/-- The volume of the closed inner cube `[r, L - r]^d` is `(L - 2r) ^ d`. -/
public lemma volume_coordCubeInner (L r : ℝ) :
    volume (coordCubeInner d L r) = (ENNReal.ofReal (L - 2 * r)) ^ d := by
  rw [coordCubeInner_eq_preimage_ofLp, volume_preimage_ofLp _
    (.pi Set.countable_univ fun _ _ ↦ measurableSet_Icc), volume_pi, Measure.pi_pi]
  simp [Real.volume_Icc, show L - r - r = L - 2 * r by ring]

end PeriodicConstant

namespace PeriodicConstantApprox

public lemma coordCube_unique_covers_vadd (L : ℝ) (hL : 0 < L) (v : cubeLattice d L hL) :
    ∀ x, ∃! g : cubeLattice d L hL, g +ᵥ x ∈ v +ᵥ coordCube d L := fun x => by
  have hvadd (a : cubeLattice d L hL) :
      a +ᵥ x ∈ v +ᵥ coordCube d L ↔ (a - v) +ᵥ x ∈ coordCube d L := by
    simp [Set.mem_vadd_set_iff_neg_vadd_mem, Submodule.vadd_def, vadd_eq_add, sub_eq_add_neg,
      add_assoc, add_comm]
  obtain ⟨g, hg, hguniq⟩ := PeriodicConstant.coordCube_unique_covers (d := d) L hL x
  exact ⟨g + v, (hvadd _).2 (by simpa),
    fun _ ha => sub_eq_iff_eq_add.1 (hguniq _ <| (hvadd _).1 ha)⟩

public lemma ball_subset_vadd_coordCube_of_mem_vadd_inner {L r : ℝ} (hL : 0 < L)
    {v : cubeLattice d L hL} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ v +ᵥ coordCubeInner d L r) :
    ball x r ⊆ v +ᵥ coordCube d L := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hball : ball y r ⊆ coordCube d L := ball_subset_coordCube_of_mem_inner hy
  intro z hz
  refine ⟨z - v, hball ?_, by simp [vadd_eq_add]⟩
  change dist z ((v : EuclideanSpace ℝ (Fin d)) + y) < r at hz
  simpa [mem_ball, dist_eq_norm, sub_sub] using hz

public lemma finite_lattice_in_ball (L : ℝ) (hL : 0 < L) (R : ℝ) :
    Set.Finite {g : cubeLattice d L hL | (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 R} := by
  refine (Set.Finite.preimage_embedding (f := ⟨fun g : cubeLattice d L hL =>
    (g : EuclideanSpace ℝ (Fin d)), Subtype.val_injective⟩) (by
      simpa [cubeLattice] using ZSpan.setFinite_inter (b := cubeBasis d L hL)
        (s := ball (0 : EuclideanSpace ℝ (Fin d)) R) Metric.isBounded_ball)).subset fun g hg => ?_
  exact ⟨hg, g.property⟩

section CoordCubeCover

variable (L : ℝ) (hL : 0 < L)

/-- The unique lattice vector translating `x` into `coordCube d L` (see `coordCubeCover_spec`).
The cell-assignment map underlying the pigeonhole argument; named to pair with its spec lemma. -/
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
  -- `g` is the (coerced) covering translate; the goal is `‖-g‖ = ‖g‖ < R + C`.
  set g := (coordCubeCover L hL x : EuclideanSpace ℝ (Fin d))
  rw [mem_ball_zero_iff, show ((-coordCubeCover L hL x : cubeLattice d L hL) :
    EuclideanSpace ℝ (Fin d)) = -g from rfl, norm_neg]
  have hx' : ‖x‖ < R := by simpa [mem_ball_zero_iff] using hx
  have hgx : ‖g + x‖ < C := by
    simpa [mem_ball_zero_iff] using hC (by
      simpa [Submodule.vadd_def, vadd_eq_add] using coordCubeCover_spec L hL x)
  have htri : ‖g‖ ≤ ‖g + x‖ + ‖x‖ := by
    simpa [add_sub_cancel_right] using norm_sub_le (g + x) x
  linarith

end CoordCubeCover

lemma card_finite_lattice_in_ball_mul_volume_coordCube_le_volume_ball {L : ℝ} (hL : 0 < L)
    {R C : ℝ} (hC : coordCube d L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C) :
    ((PeriodicConstantApprox.finite_lattice_in_ball (d := d) L hL (R + C)).toFinset.card :
        ℝ≥0∞) * volume (coordCube d L) ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C))) := by
  -- `htSet` abbreviates the finiteness fact whose `toFinset` indexes the cells.
  set htSet := PeriodicConstantApprox.finite_lattice_in_ball (d := d) L hL (R + C)
  have hvadd : ∀ g : ↥(cubeLattice d L hL),
      volume (g +ᵥ coordCube d L) = volume (coordCube d L) :=
    fun g => measure_vadd volume g _
  have hms : MeasurableSet (coordCube d L) :=
    fundamentalDomain_cubeBasis_eq_coordCube L hL ▸ fundamentalDomain_measurableSet _
  calc (↑htSet.toFinset.card : ℝ≥0∞) * volume (coordCube d L)
      = ∑ g ∈ htSet.toFinset, volume (g +ᵥ coordCube d L) := by
        simp_rw [hvadd, Finset.sum_const, nsmul_eq_mul]
    _ = volume (⋃ g ∈ htSet.toFinset, g +ᵥ coordCube d L) := (measure_biUnion_finset
        (fun _ _ _ _ hgh => disjoint_vadd_of_unique_covers (d := d)
          (PeriodicConstant.coordCube_unique_covers L hL) hgh)
        (fun g _ => hms.const_vadd g)).symm
    _ ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C))) := volume.mono <| by
        rintro y hy
        obtain ⟨g, hgT, x, hx, rfl⟩ := Set.mem_iUnion₂.1 hy
        have hg : (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 (R + C) :=
          htSet.mem_toFinset.1 hgT
        simp only [vadd_eq_add, mem_ball_zero_iff]
        linarith [norm_add_le (g : EuclideanSpace ℝ (Fin d)) x,
          mem_ball_zero_iff.mp (hC hx), mem_ball_zero_iff.mp hg]

section BoundaryControl

/-- The constant vector `(c, …, c)`. Used only to recentre the outer cube in the shell estimate;
kept (with `constVec_apply`) to avoid repeating the `WithLp.toLp` spelling at its many sites. -/
def constVec (d : ℕ) (c : ℝ) : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun _ : Fin d => c)

@[simp] lemma constVec_apply {c : ℝ} (i : Fin d) : constVec d c i = c := rfl

lemma coordCube_boundary_half_add_ball_subset_outer_diff_inner (L : ℝ) :
    ((coordCube d L \ coordCubeInner d L (1 / 2)) +
        ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
      ⊆ ((constVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner d (L + 1) 0) \
        coordCubeInner d L 1 := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  have hyi : ∀ i : Fin d, |y i| < (1 / 2 : ℝ) := fun i =>
    (abs_coord_le_norm y i).trans_lt (by simpa [mem_ball_zero_iff] using hy)
  rw [Set.mem_diff, mem_coordCube] at hx
  refine ⟨Set.mem_vadd_set_iff_neg_vadd_mem.2 fun i => ?_, fun hz_inner => ?_⟩
  · -- Each coordinate of `x + y`, shifted by `+ 1/2`, lands in `[0, L + 1]`.
    simp only [vadd_eq_add, neg_neg, constVec_apply, PiLp.add_apply, PiLp.neg_apply,
      Set.mem_Icc]
    refine ⟨?_, ?_⟩  -- lower bound `0`, upper bound `L + 1`
    · linarith [(hx.1 i).1, abs_lt.mp (hyi i)]
    · linarith [(hx.1 i).2.le, abs_lt.mp (hyi i)]
  · obtain ⟨i, hi⟩ : ∃ i : Fin d, ¬ x i ∈ Set.Icc (1 / 2 : ℝ) (L - 1 / 2) := by
      simpa [mem_coordCubeInner] using not_forall.mp hx.2
    rw [Set.mem_Icc, not_and_or] at hi
    have hz_i : (x i + y i) ∈ Set.Icc (1 : ℝ) (L - 1) := by
      simpa [mem_coordCubeInner] using hz_inner i
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
  -- `r` abbreviates the common ball radius, matching the statement's `2⁻¹`.
  let r : ℝ := (2⁻¹ : ℝ)
  have hdisj : (s : Set (EuclideanSpace ℝ (Fin d))).PairwiseDisjoint fun x => ball x r :=
    fun x hx y hy hxy => ball_disjoint_ball (by
      dsimp [r]; linarith [show (1 : ℝ) ≤ dist x y by
        simpa [hSsep] using S.centers_dist' x y (hs_centers x hx) (hs_centers y hy) hxy])
  have hsub : (⋃ x ∈ s, ball x r) ⊆
      g +ᵥ (((constVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner d (L + 1) 0) \
            coordCubeInner d L 1) := fun y hy => by
    obtain ⟨x, hxS, hyBall⟩ : ∃ x ∈ s, y ∈ ball x r := by aesop
    have hxB := hs_boundary x hxS
    -- `x0`, `y0`: pull `x`, `y` back by `-g` to the base cube (referenced repeatedly below).
    set x0 : EuclideanSpace ℝ (Fin d) := (-(g : EuclideanSpace ℝ (Fin d))) +ᵥ x
    set y0 : EuclideanSpace ℝ (Fin d) := (-(g : EuclideanSpace ℝ (Fin d))) +ᵥ y
    have hxB1' : x0 ∈ coordCube d L := Set.mem_vadd_set_iff_neg_vadd_mem.mp hxB.1
    have hxB2' : x0 ∉ coordCubeInner d L (1 / 2) :=
      fun h => hxB.2 (Set.mem_vadd_set_iff_neg_vadd_mem.mpr h)
    have hy0 : y0 ∈ ((constVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner d (L + 1) 0) \
        coordCubeInner d L 1 := by
      apply coordCube_boundary_half_add_ball_subset_outer_diff_inner (d := d) L
      refine ⟨x0, ⟨hxB1', hxB2'⟩, y0 - x0, ?_, by simp [sub_eq_add_neg, add_left_comm]⟩
      have : ‖y - x‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hyBall
      simpa [Metric.mem_ball, dist_eq_norm, x0, y0, r] using this
    exact Set.mem_vadd_set_iff_neg_vadd_mem.mpr hy0
  calc (s.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ))
      = volume (⋃ x ∈ s, ball x r) := by
        simpa [Measure.addHaar_ball_center, mul_comm, mul_assoc] using
          (measure_biUnion_finset (μ := volume) hdisj (fun _ _ => measurableSet_ball)).symm
    _ ≤ volume (g +ᵥ (((constVec d (-(1 / 2 : ℝ))) +ᵥ coordCubeInner d (L + 1) 0) \
          coordCubeInner d L 1)) := volume.mono hsub
    _ = _ := measure_vadd volume g _

end BoundaryControl

lemma volume_cubeShell_eq_pow (L : ℝ) :
    volume (((constVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner d (L + 1) 0) \
        coordCubeInner d L 1) =
      (ENNReal.ofReal (L + 1)) ^ d - (ENNReal.ofReal (L - 2)) ^ d := by
  have hsub : coordCubeInner d L 1 ⊆
      (constVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner d (L + 1) 0 := fun x hx =>
    Set.mem_vadd_set_iff_neg_vadd_mem.2 fun i => by
      simp only [mem_coordCubeInner, constVec, vadd_eq_add, one_div,
        WithLp.ofLp_add, WithLp.ofLp_neg, Pi.add_apply, Pi.neg_apply, neg_neg] at hx ⊢
      exact ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩
  have hmeas : MeasurableSet (coordCubeInner d L 1) := by
    simpa [PeriodicConstant.coordCubeInner_eq_preimage_ofLp] using
      (MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Icc).preimage
        (PiLp.volume_preserving_ofLp (ι := Fin d)).measurable
  simpa [measure_vadd, constVec, PeriodicConstant.volume_coordCubeInner] using
    measure_diff (μ := volume) hsub hmeas.nullMeasurableSet
      (by simp [PeriodicConstant.volume_coordCubeInner])

lemma toNNReal_covolume_cubeLattice (L : ℝ) (hL : 0 < L) :
    Real.toNNReal (ZLattice.covolume (cubeLattice d L hL) volume) =
      (volume (coordCube d L)).toNNReal := by
  have hcov : ZLattice.covolume (cubeLattice d L hL) volume = (volume (coordCube d L)).toReal := by
    simpa [Measure.real, fundamentalDomain_cubeBasis_eq_coordCube L hL] using
      ZLattice.covolume_eq_measure_fundamentalDomain (L := cubeLattice d L hL) (μ := volume)
        (by simpa [cubeLattice] using ZSpan.isAddFundamentalDomain (cubeBasis d L hL) volume :
          IsAddFundamentalDomain (cubeLattice d L hL)
            (fundamentalDomain (cubeBasis d L hL)) volume)
  simp [hcov]

lemma periodize_cube_density_eq (hd : 0 < d) (S : SpherePacking d) (hSsep : S.separation = 1)
    {L : ℝ} (hL : 0 < L) {g : cubeLattice d L hL}
    (F : Finset (EuclideanSpace ℝ (Fin d)))
    (hF_centers : ∀ x ∈ F, x ∈ S.centers)
    (hF_inner : ∀ x ∈ F, x ∈ g +ᵥ coordCubeInner d L (2⁻¹ : ℝ)) :
    ∃ P : PeriodicSpherePacking d, P.separation = 1 ∧ P.density =
        (F.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ)) /
          Real.toNNReal (ZLattice.covolume (cubeLattice d L hL) volume) := by
  -- Assemble the periodic packing `P` from the cube cell `D` and the representatives `Fset`.
  let D : Set (EuclideanSpace ℝ (Fin d)) := g +ᵥ coordCube d L
  let Fset : Set (EuclideanSpace ℝ (Fin d)) := (F : Set (EuclideanSpace ℝ (Fin d)))
  have hD_unique := PeriodicConstantApprox.coordCube_unique_covers_vadd L hL g
  let P : PeriodicSpherePacking d :=
    periodize_to_periodicSpherePacking (d := d) S (Λ := cubeLattice d L hL) D Fset
      (hD_unique_covers := hD_unique) (hF_centers := by assumption)
      (hF_ball := fun x hx => ball_subset_vadd_coordCube_of_mem_vadd_inner hL <| by
        simpa [hSsep] using hF_inner x (by simpa [Fset] using hx))
  have hPsep : P.separation = 1 := by simpa [P, hSsep]
  -- The translated inner cube `Fset` sits inside the translated full cube `D`.
  have hFsubD : Fset ⊆ D := fun x hx => by
    rcases hF_inner x (by simpa [Fset] using hx) with ⟨a, ha, rfl⟩
    exact ⟨a, fun i => ⟨(by norm_num : (0 : ℝ) < _).le.trans (ha i).1,
      (ha i).2.trans_lt (sub_lt_self _ (by norm_num))⟩, rfl⟩
  -- The periodized centers meet `D` in exactly `Fset` (`P.centers = periodizedCenters Λ Fset`).
  have hPcD : P.centers ∩ D = Fset := by
    simpa [P, periodize_to_periodicSpherePacking, Fset] using
      periodizedCenters_inter_eq_of_subset (d := d) (Λ := cubeLattice d L hL) (D := D)
        (F := Fset) hFsubD hD_unique
  -- `D` is bounded, being a translate of the cube.
  have hD_bounded : IsBounded D := by
    simpa [D, Submodule.vadd_def, vadd_eq_add] using
      (PeriodicConstant.isBounded_coordCube L hL).vadd (g : EuclideanSpace ℝ (Fin d))
  have hnumReps : P.numReps = F.card := by
    exact_mod_cast show (P.numReps : ENat) = (F.card : ENat) by
      simpa [hPcD, Fset, Set.encard_coe_eq_coe_finsetCard] using
        (P.encard_centers_inter_isFundamentalDomain (d := d) (D := D)
          hD_bounded hD_unique hd).symm
  exact ⟨P, hPsep, by simpa [hnumReps, hPsep] using P.density_eq' (d := d) hd⟩

/-- The cube-shell error ratio `volume(shell) / volume(coordCube d L)` tends to `0` as `L → ∞`:
the shell volume grows like `(L + 1) ^ d - (L - 2) ^ d` while the cube volume grows like `L ^ d`. -/
lemma tendsto_volume_cubeShell_div_volume_coordCube_zero :
    Tendsto
        (fun L : ℝ =>
          volume (((constVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner d (L + 1) 0) \
              coordCubeInner d L 1) /
            volume (coordCube d L))
        atTop (𝓝 (0 : ℝ≥0∞)) := by
  -- `f` is the real shell/cube volume ratio, whose `→ 0` limit we transfer to `ℝ≥0∞`.
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
  have hvol : volume (coordCube d L) = (ENNReal.ofReal L) ^ d := by
    simpa using PeriodicConstant.volume_coordCube L
  rw [volume_cubeShell_eq_pow L, hvol,
    ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ L + 1), ← ENNReal.ofReal_pow hL2',
    ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ L), ← ENNReal.ofReal_sub _ (pow_nonneg hL2' d)]
  simpa [f] using ENNReal.ofReal_div_of_pos (x := (L + 1)^d - (L - 2)^d) (pow_pos (by linarith) d)

/-- Pick `L > 0` and `C > 0` with `coordCube d L ⊆ ball 0 C` and the cube-shell error
`volume(shell) / volume(coordCube)` smaller than the headroom `c - b`. -/
private lemma exists_L_and_C_for_cubeShellErr_lt {b c : ℝ≥0∞} (hbc : b < c) :
    ∃ L : ℝ, 0 < L ∧ ∃ C : ℝ, 0 < C ∧
      coordCube d L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C ∧
      volume (((constVec (d := d) (-(1 / 2 : ℝ))) +ᵥ coordCubeInner d (L + 1) 0) \
          coordCubeInner d L 1) / volume (coordCube d L) < c - b := by
  obtain ⟨L, hLpos, hLerr⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (tendsto_volume_cubeShell_div_volume_coordCube_zero.eventually
      (Iio_mem_nhds (tsub_pos_of_lt hbc)))).exists
  obtain ⟨C, hC⟩ : ∃ C : ℝ, coordCube d L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C := by
    simpa using (PeriodicConstant.isBounded_coordCube L hLpos).subset_ball 0
  have hCpos : 0 < C := by
    simpa [Metric.mem_ball, dist_eq_norm] using
      hC (by simp [coordCube, hLpos] : (0 : EuclideanSpace ℝ (Fin d)) ∈ coordCube d L)
  exact ⟨L, hLpos, C, hCpos, hC, hLerr⟩

/-- Given `c < S.density` and headroom `δ < c`, find `R > 0` with `c < S.finiteDensity R` and the
ball-volume ratio bound `δ < c * volume(ball R) / volume(ball (R + Cshift))`. -/
private lemma exists_R_finiteDensity_gt_and_ratio_gt (hd : 0 < d)
    (S : SpherePacking d) {c : ℝ≥0∞} (hcS : c < S.density) {δ : ℝ≥0∞} (hδc : δ < c) (Cshift : ℝ) :
    ∃ R : ℝ, c < S.finiteDensity R ∧ 0 < R ∧
      δ < c * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) /
        volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift))) := by
  -- `ratio R` is the ball-volume ratio `vol(ball R) / vol(ball (R + Cshift))`, tending to `1`.
  let ratio : ℝ → ℝ≥0∞ := fun R : ℝ =>
    volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) /
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift))
  -- `c < S.finiteDensity R` for arbitrarily large `R`, since `c < S.density = limsup`.
  have hfreq : ∃ᶠ R in (atTop : Filter ℝ), c < S.finiteDensity R :=
    frequently_lt_of_lt_limsup (h := by simpa [SpherePacking.density] using hcS)
  -- The ball-volume ratio tends to `1`, so `c * ratio R → c`.
  have hratio : Tendsto ratio atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa [ratio, add_zero] using
      volume_ball_ratio_tendsto_nhds_one'' (C := (0 : ℝ)) (C' := Cshift) hd
  have hmul : Tendsto (fun R : ℝ => c * ratio R) atTop (𝓝 c) := by
    simpa [mul_one] using ENNReal.Tendsto.const_mul (a := c) hratio (Or.inl one_ne_zero)
  -- Eventually `c * ratio R > δ` (limit `c > δ`); combine with the frequent and positivity facts.
  exact (hfreq.and_eventually ((eventually_gt_atTop (0 : ℝ)).and
    (hmul.eventually (Ioi_mem_nhds hδc)))).exists

/-- Pigeonhole step: among the finitely many lattice translates of `coordCube d L` meeting
`ball 0 (R₁ + C)`, some translate `g0` contains at least `s.card / t.card` of the centers in
`s = S.centers ∩ ball 0 R₁`. The resulting cell `sg ⊆ s` satisfies the volume comparison
`s.encard * volume(coordCube) ≤ sg.card * volume(ball (R₁ + 2 * C))`. -/
private lemma exists_pigeonhole_lattice_cell {L : ℝ} (hL : 0 < L) {C : ℝ}
    (hC : coordCube d L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C)
    (S : SpherePacking d) {R₁ : ℝ} (hR₁ : 0 < R₁ + C) :
    ∃ g0 : cubeLattice d L hL, ∃ sg : Finset (EuclideanSpace ℝ (Fin d)),
      (∀ x ∈ sg, x ∈ S.centers) ∧ (∀ x ∈ sg, x ∈ g0 +ᵥ coordCube d L) ∧
        ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R₁).encard : ℝ≥0∞) *
            volume (coordCube d L) ≤
          (sg.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R₁ + 2 * C)) := by
  have hX : (S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R₁).Finite :=
    SpherePacking.finite_centers_inter_ball S R₁
  -- Pigeonhole: `s` = centres in `ball 0 R₁`, `t` = lattice translates meeting `ball 0 (R₁+C)`,
  -- `f` sends each centre to its covering translate; `sg` (below) is the fullest fibre.
  let s : Finset (EuclideanSpace ℝ (Fin d)) := hX.toFinset
  let htSet := finite_lattice_in_ball (d := d) L hL (R₁ + C)
  let t : Finset (cubeLattice d L hL) := htSet.toFinset
  let f : EuclideanSpace ℝ (Fin d) → cubeLattice d L hL := fun x => -coordCubeCover L hL x
  have hf_maps : (s : Set (EuclideanSpace ℝ (Fin d))).MapsTo f t := fun _ hx =>
    htSet.mem_toFinset.2 <| neg_coordCubeCover_mem_ball L hL hC (hX.mem_toFinset.1 hx).2
  obtain ⟨g0, _, hg0max⟩ := Finset.exists_max_image t (fun g => (s.filter fun x => f x = g).card)
    ⟨0, htSet.mem_toFinset.2 (by simpa only [Set.mem_setOf_eq, Metric.mem_ball,
      ZeroMemClass.coe_zero, dist_self] using hR₁)⟩
  let sg : Finset (EuclideanSpace ℝ (Fin d)) := s.filter fun x => f x = g0
  refine ⟨g0, sg, fun x hx => (hX.mem_toFinset.1 (Finset.mem_filter.1 hx).1).1,
    fun x hx => ?_, ?_⟩
  · have h : g0 = -coordCubeCover L hL x := (Finset.mem_filter.1 hx).2.symm
    refine h ▸ Set.mem_vadd_set_iff_neg_vadd_mem.mpr ?_
    simpa [neg_neg] using coordCubeCover_spec L hL x
  · have hs_le : (s.card : ℝ≥0∞) ≤ (t.card : ℝ≥0∞) * (sg.card : ℝ≥0∞) := by
      have hcard : s.card ≤ t.card * sg.card := by
        simpa [Finset.card_eq_sum_card_fiberwise hf_maps, Finset.sum_const] using
          Finset.sum_le_sum hg0max
      exact_mod_cast hcard
    have ht_vol : ((t.card : ℝ≥0∞) * volume (coordCube d L)) ≤
        volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R₁ + 2 * C)) :=
      card_finite_lattice_in_ball_mul_volume_coordCube_le_volume_ball hL hC
    have hs_enc : ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R₁).encard : ℝ≥0∞) = s.card :=
      congrArg ((↑) : ENat → ℝ≥0∞) hX.encard_eq_coe_toFinset_card
    calc ((S.centers ∩ ball _ R₁).encard : ℝ≥0∞) * volume (coordCube d L)
        = (s.card : ℝ≥0∞) * volume (coordCube d L) := by rw [hs_enc]
      _ ≤ (t.card : ℝ≥0∞) * (sg.card : ℝ≥0∞) * volume (coordCube d L) :=
          mul_le_mul_left hs_le _
      _ = (sg.card : ℝ≥0∞) * ((t.card : ℝ≥0∞) * volume (coordCube d L)) := by ac_rfl
      _ ≤ _ := mul_le_mul_right ht_vol _

/-- From the pigeonhole volume comparison, a density-ratio lower bound, and a finite-density bound,
derive that `δ < sg.card * volBall / volCube` where `volBall = volume(ball 0 (2⁻¹))` and
`volCube = volume(coordCube d L)`. -/
private lemma sg_card_mul_volBall_div_volCube_gt (hd : 0 < d)
    (S : SpherePacking d) (hSsep : S.separation = 1) {L : ℝ} (hL : 0 < L) {R Cshift : ℝ}
    (hRC : 0 < R + Cshift) {c δ : ℝ≥0∞} (hcR : c < S.finiteDensity R)
    (hRratio : δ < c * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) /
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift))))
    {sg : Finset (EuclideanSpace ℝ (Fin d))}
    (hs_mul : ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + 2⁻¹)).encard : ℝ≥0∞) *
        volume (coordCube d L) ≤
          (sg.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift))) :
    δ < (sg.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ)) /
      volume (coordCube d L) := by
  -- Abbreviations for the three volumes appearing in the inequality chase.
  set volCube := volume (coordCube d L)
  set volBall := volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ))
  set V := volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift))
  have hvolCube_ne0 : volCube ≠ 0 := by
    simpa [volCube, PeriodicConstant.volume_coordCube L] using
      pow_ne_zero d (ENNReal.ofReal_pos.mpr hL).ne'
  have hvolCube_ne_top : volCube ≠ ∞ :=
    (PeriodicConstant.isBounded_coordCube L hL).measure_lt_top.ne
  -- Cancelling a common factor of `volCube` from the numerator and an outer division.
  have hcancel : ∀ a c : ℝ≥0∞, a * volCube / c / volCube = a / c := fun a c => by
    simp only [div_eq_mul_inv,
      show a * volCube * c⁻¹ * volCube⁻¹ = a * c⁻¹ * (volCube * volCube⁻¹) by ring,
      ENNReal.mul_inv_cancel hvolCube_ne0 hvolCube_ne_top, mul_one]
  -- The numerator inequality, from the finite-density bound on `S`.
  have hnum : c * volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) <
      ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + 2⁻¹)).encard : ℝ≥0∞) * volBall :=
    ENNReal.mul_lt_of_lt_div <| hcR.trans_le <| by
      simpa [hSsep, volBall, add_assoc, add_left_comm, add_comm] using S.finiteDensity_le hd R
  have hc_ratio : c * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) / V) <
      ((S.centers ∩ ball 0 (R + 2⁻¹)).encard : ℝ≥0∞) * volBall / V := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      ENNReal.div_lt_div_right ((Metric.measure_ball_pos volume _ hRC).ne.symm : V ≠ 0)
        (MeasureTheory.measure_ball_lt_top (μ := volume)).ne hnum
  refine (hRratio.trans hc_ratio).trans_le ?_
  have hratio_le : ((S.centers ∩ ball 0 (R + 2⁻¹)).encard : ℝ≥0∞) / V ≤
      (sg.card : ℝ≥0∞) / volCube := by
    have h := ENNReal.div_le_div_right (ENNReal.div_le_of_le_mul hs_mul) volCube
    rwa [hcancel] at h
  have := mul_le_mul_left hratio_le volBall
  simp only [div_eq_mul_inv] at this ⊢
  convert this using 1 <;> ring

/-- From a finset `sg` of centers in `g0 +ᵥ coordCube d L` satisfying `sg.card * volBall / volCube`
exceeding some bound `δ + shellVol / volCube`, construct a periodic packing `P` with separation `1`
and density `> δ`. The inner-cube filtering bounds the boundary contribution by `shellVol`. -/
private lemma exists_periodicSpherePacking_density_gt_aux (hd : 0 < d)
    (S : SpherePacking d) (hSsep : S.separation = 1) {L : ℝ} (hL : 0 < L)
    {g0 : cubeLattice d L hL} {sg : Finset (EuclideanSpace ℝ (Fin d))} {δ : ℝ≥0∞}
    (hsg_centers : ∀ x ∈ sg, x ∈ S.centers) (hsg_memCube : ∀ x ∈ sg, x ∈ g0 +ᵥ coordCube d L)
    (hsg_density : δ + volume (((constVec (d := d) (-(1 / 2 : ℝ))) +ᵥ
            coordCubeInner d (L + 1) 0) \ coordCubeInner d L 1) / volume (coordCube d L) <
        (sg.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ)) /
          volume (coordCube d L)) :
    ∃ P : PeriodicSpherePacking d, P.separation = 1 ∧ δ < P.density := by
  -- Abbreviations for the shell, cube, and unit-ball volumes used in the density bound.
  set shellVol : ℝ≥0∞ := volume (((constVec (d := d) (-(1 / 2 : ℝ))) +ᵥ
      coordCubeInner d (L + 1) 0) \ coordCubeInner d L 1)
  set volCube : ℝ≥0∞ := volume (coordCube d L)
  set volBall : ℝ≥0∞ := volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ))
  have hvolCube_ne_top : volCube ≠ ∞ :=
    (PeriodicConstant.isBounded_coordCube L hL).measure_lt_top.ne
  -- Split `sg` by the inner cube: `F` (kept representatives) and `sb` (boundary, bounded by shell).
  let innerSet : Set (EuclideanSpace ℝ (Fin d)) := g0 +ᵥ coordCubeInner d L (1 / 2 : ℝ)
  letI : DecidablePred (fun x : EuclideanSpace ℝ (Fin d) => x ∈ innerSet) := Classical.decPred _
  let F : Finset (EuclideanSpace ℝ (Fin d)) := sg.filter fun x => x ∈ innerSet
  let sb : Finset (EuclideanSpace ℝ (Fin d)) := sg.filter fun x => x ∉ innerSet
  have hsb_vol : (sb.card : ℝ≥0∞) * volBall ≤ shellVol := by
    simpa [volBall, shellVol, constVec] using
      card_mul_volume_ball_le_volume_outer_diff_inner S hL hSsep
        (fun x hx => hsg_centers x (Finset.mem_filter.1 hx).1)
        (fun x hx => ⟨hsg_memCube x (Finset.mem_filter.1 hx).1, by
          simpa [innerSet] using (Finset.mem_filter.1 hx).2⟩)
  obtain ⟨P, hPsep, hPdens⟩ := periodize_cube_density_eq hd S hSsep hL F
    (fun x hx => hsg_centers x (Finset.mem_filter.1 hx).1)
    (fun x hx => by simpa [innerSet] using (Finset.mem_filter.1 hx).2)
  have hcov_eq : (Real.toNNReal (ZLattice.covolume (cubeLattice d L hL) volume) : ℝ≥0∞) =
      volCube := by
    rw [show Real.toNNReal (ZLattice.covolume (cubeLattice d L hL) volume) = volCube.toNNReal by
        simpa [volCube] using toNNReal_covolume_cubeLattice (d := d) L hL,
      ENNReal.coe_toNNReal hvolCube_ne_top]
  have hPdens' : P.density = (F.card : ℝ≥0∞) * volBall / volCube := by
    simpa [volBall, hcov_eq] using hPdens
  refine ⟨P, hPsep, (lt_tsub_iff_right.mpr hsg_density).trans_le (tsub_le_iff_right.2 ?_)⟩
  have hcard : (sg.card : ℝ≥0∞) = (F.card : ℝ≥0∞) + (sb.card : ℝ≥0∞) := by
    exact_mod_cast
      (Finset.card_filter_add_card_filter_not (s := sg) (p := fun x => x ∈ innerSet)).symm
  have hsplit : (sg.card : ℝ≥0∞) * volBall =
      (F.card : ℝ≥0∞) * volBall + (sb.card : ℝ≥0∞) * volBall := by
    rw [hcard, add_mul]
  simpa [hPdens', div_eq_mul_inv, mul_add, add_mul, mul_assoc, shellVol] using
    ENNReal.div_le_div_right (hsplit ▸ add_le_add_right hsb_vol _ :
      (sg.card : ℝ≥0∞) * volBall ≤ (F.card : ℝ≥0∞) * volBall + shellVol) volCube

end PeriodicConstantApprox

namespace SpherePacking

theorem exists_periodicSpherePacking_sep_one_density_gt_of_lt_density (hd : 0 < d)
    (S : SpherePacking d) (hSsep : S.separation = 1) {b : ℝ≥0∞} (hb : b < S.density) :
    ∃ P : PeriodicSpherePacking d, P.separation = 1 ∧ b < P.density := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  obtain ⟨c, hbc, hcS⟩ := exists_between hb
  obtain ⟨L, hLpos, C, hCpos, hC, hLerr⟩ :=
    PeriodicConstantApprox.exists_L_and_C_for_cubeShellErr_lt (d := d) hbc
  obtain ⟨R, hcR, hRpos, hRratio⟩ := PeriodicConstantApprox.exists_R_finiteDensity_gt_and_ratio_gt
    hd S hcS (lt_tsub_iff_left.mp hLerr) ((2⁻¹ : ℝ) + 2 * C)
  obtain ⟨g0, sg, hsg_centers, hsg_memCube, hs_mul⟩ :=
    PeriodicConstantApprox.exists_pigeonhole_lattice_cell hLpos hC S
      (show (0 : ℝ) < R + 2⁻¹ + C by positivity)
  exact PeriodicConstantApprox.exists_periodicSpherePacking_density_gt_aux hd S hSsep hLpos
    hsg_centers hsg_memCube
    (PeriodicConstantApprox.sg_card_mul_volBall_div_volCube_gt hd S hSsep hLpos
      (by positivity) hcR hRratio
      (by simpa [show R + 2⁻¹ + 2 * C = R + ((2⁻¹ : ℝ) + 2 * C) by ring] using hs_mul))

end SpherePacking

/-- The periodic sphere packing constant equals the sphere packing constant. -/
public theorem periodic_constant_eq_constant (hd : 0 < d) :
    PeriodicSpherePackingConstant d = SpherePackingConstant d := by
  rw [periodic_constant_eq_periodic_constant_normalized,
    SpherePacking.constant_eq_constant_normalized]
  refine le_antisymm
    (iSup₂_le fun P hPsep => le_iSup₂_of_le P.toSpherePacking hPsep le_rfl)
    (iSup₂_le fun S hSsep => le_of_forall_lt fun a ha => ?_)
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
public theorem fourierInversion : 𝓕⁻ (𝓕 ⇑f) = f := by simp [← fourier_coe, ← fourierInv_coe]

end SchwartzMap
section Integration

open MeasureTheory Filter

variable {E : Type*} [TopologicalSpace E] [AddGroup E] [IsTopologicalAddGroup E]
  [MeasureSpace E] [BorelSpace E]
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


namespace SpherePacking.CohnElkies
variable {d : ℕ}

namespace LPBoundAux

variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]

/-- A Schwartz function has summable norms on any translate of a `ℤ`-lattice. The
`EuclideanSpace`-specialised name kept for use throughout this file; the content is
`SchwartzMap.summable_norm_comp_add`. -/
public lemma summable_norm_comp_add_zlattice (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (a : EuclideanSpace ℝ (Fin d)) :
    Summable (fun ℓ : Λ => ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖) :=
  f.summable_norm_comp_add Λ a

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
  -- `bZ` is an integral basis of `Λ`; its inner-product dual basis spans the dual submodule.
  let bZ : Basis (Module.Free.ChooseBasisIndex ℤ Λ) ℤ Λ := Module.Free.chooseBasis ℤ Λ
  have hB : LinearMap.BilinForm.Nondegenerate (innerₗ (EuclideanSpace ℝ (Fin d)) :
      LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin d))) := by
    constructor <;> intro x hx <;>
      exact inner_self_eq_zero.1 (by simpa [innerₗ_apply_apply] using hx x : ⟪x, x⟫ = (0 : ℝ))
  have hspan : LinearMap.BilinForm.dualSubmodule (B := innerₗ (EuclideanSpace ℝ (Fin d))) Λ =
      Submodule.span ℤ (Set.range
        (LinearMap.BilinForm.dualBasis (B := innerₗ (EuclideanSpace ℝ (Fin d)))
          hB (bZ.ofZLatticeBasis ℝ Λ))) := by
    simpa [bZ.ofZLatticeBasis_span (K := ℝ) (L := Λ)] using
      LinearMap.BilinForm.dualSubmodule_span_of_basis (B := innerₗ (EuclideanSpace ℝ (Fin d)))
        (R := ℤ) (S := ℝ) (M := EuclideanSpace ℝ (Fin d)) hB (bZ.ofZLatticeBasis ℝ Λ)
  exact hspan ▸ inferInstance

noncomputable section

/-- The equivalence `(P.centers ∩ D) × P.lattice ≃ P.centers` from a unique-covering hypothesis,
realising the orbit decomposition of the centres; API: `centersInterProdEquiv_sub`. -/
@[expose] public def centersInterProdEquiv (P : PeriodicSpherePacking d) [Nonempty P.centers]
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) :
    (↑(P.centers ∩ D) × P.lattice) ≃ P.centers := by
  have hcover :
      ∀ x : P.centers, ∃! g : P.lattice, g +ᵥ (x : EuclideanSpace ℝ (Fin d)) ∈ P.centers ∩ D :=
    fun x =>
      let ⟨g, hg, hguniq⟩ := hD_unique_covers (x : EuclideanSpace ℝ (Fin d))
      ⟨g, ⟨P.lattice_action g.property x.property, hg⟩, fun g' hg' => hguniq g' hg'.2⟩
  -- `toCenter`/`toPair` are the two directions of the equivalence; `cover x` is `x`'s covering
  -- translate and `repr x` its representative in `P.centers ∩ D`.
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
        (by
          simp only [toCenter]
          rw [neg_vadd_vadd]
          exact p.1.property)).symm
    refine Prod.ext (Subtype.ext ?_) ?_
    · simp only [toPair, repr, toCenter, hcov]
      exact neg_vadd_vadd _ _
    · simp only [toPair, hcov, neg_neg]
  · exact fun x => Subtype.ext (by
      simp only [toPair, repr, toCenter]
      exact neg_vadd_vadd _ _)

/-- Image of `centersInterProdEquiv` differs from `(x, ℓ)` by adding `ℓ`. -/
private lemma centersInterProdEquiv_sub (P : PeriodicSpherePacking d) [Nonempty P.centers]
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice) :
    ((centersInterProdEquiv (P := P) (D := D) hD_unique_covers (x, ℓ) :
        EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))) =
      (x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
        (ℓ : EuclideanSpace ℝ (Fin d)) := by
  simp [centersInterProdEquiv, Submodule.vadd_def, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm]

/-- Summability for the product reindexed Schwartz sum used in
`tsum_centers_eq_tsum_centersInter_centersInter_lattice`. -/
private lemma summable_prod_schwartz_re (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (P : PeriodicSpherePacking d) [Nonempty P.centers]
    {D : Set (EuclideanSpace ℝ (Fin d))} [Finite ↑(P.centers ∩ D)]
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) :
    Summable (fun p : ↑(P.centers ∩ D) × P.lattice => ∑' y : ↑(P.centers ∩ D),
      (f ((centersInterProdEquiv (P := P) (D := D) hD_unique_covers p :
        EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re) := by
  letI : Fintype ↑(P.centers ∩ D) := Fintype.ofFinite _
  simp_rw [tsum_fintype]
  refine summable_sum fun y _ => Summable.of_norm_bounded
    (g := fun p : ↑(P.centers ∩ D) × P.lattice =>
      ‖f ((p.1 : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
        (p.2 : EuclideanSpace ℝ (Fin d)))‖) ?_ ?_
  · refine (summable_prod_of_nonneg fun _ => norm_nonneg _).2
      ⟨fun x => by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (LPBoundAux.summable_norm_comp_add_zlattice (Λ := P.lattice) f
          ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))), Summable.of_finite⟩
  · rintro ⟨x, ℓ⟩
    simpa [centersInterProdEquiv_sub P hD_unique_covers x y ℓ, Real.norm_eq_abs] using
      Complex.abs_re_le_norm (f ((centersInterProdEquiv (P := P) (D := D)
        hD_unique_covers (x, ℓ) : EuclideanSpace ℝ (Fin d)) -
          (y : EuclideanSpace ℝ (Fin d))))

/-- Commute the `ℓ`-sum past the finite `y`-sum after reindexing by `centersInterProdEquiv`. -/
private lemma tsum_lattice_tsum_centersInter_swap (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (P : PeriodicSpherePacking d) [Nonempty P.centers]
    {D : Set (EuclideanSpace ℝ (Fin d))} [Finite ↑(P.centers ∩ D)]
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (x : ↑(P.centers ∩ D)) :
    (∑' (ℓ : P.lattice), ∑' (y : ↑(P.centers ∩ D)),
      (f ((centersInterProdEquiv (P := P) (D := D) hD_unique_covers (x, ℓ) :
        EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re) =
      ∑' (y : ↑(P.centers ∩ D)), ∑' (ℓ : P.lattice),
        (f ((centersInterProdEquiv (P := P) (D := D) hD_unique_covers (x, ℓ) :
          EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re := by
  letI : Fintype ↑(P.centers ∩ D) := Fintype.ofFinite _
  simpa [tsum_fintype] using
    (Summable.tsum_finsetSum (s := Finset.univ) (fun y _ =>
      (summable_congr fun b => congrArg Complex.re (congrArg (⇑f)
          (centersInterProdEquiv_sub P hD_unique_covers x y b))).mpr
        (LPBoundSummability.summable_lattice_translate_re (Λ := P.lattice) (f := f)
          ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))))))

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
  -- `e` is the orbit-decomposition equivalence used to reindex the centre sum.
  let e : (↑(P.centers ∩ D) × P.lattice) ≃ P.centers :=
    centersInterProdEquiv (P := P) (D := D) hD_unique_covers
  have he_sub := centersInterProdEquiv_sub P hD_unique_covers
  -- Reindex the `x : P.centers` sum along the equiv `e` as a sum over `(x₀, ℓ)`.
  have hreindex :
      (∑' x : P.centers, ∑' y : ↑(P.centers ∩ D), (f (x - (y : EuclideanSpace ℝ (Fin d)))).re)
        = ∑' (x : ↑(P.centers ∩ D)) (ℓ : P.lattice), ∑' y : ↑(P.centers ∩ D),
            (f ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re := by
    rw [← (summable_prod_schwartz_re f P hD_unique_covers).tsum_prod]
    simpa [e] using (e.tsum_eq (f := fun x : P.centers =>
      ∑' y : ↑(P.centers ∩ D), (f (x - (y : EuclideanSpace ℝ (Fin d)))).re)).symm
  rw [hreindex]
  refine tsum_congr fun x => ?_
  rw [tsum_lattice_tsum_centersInter_swap f P hD_unique_covers x]
  exact tsum_congr₂ fun b c => congrArg Complex.re (congrArg (⇑f) (he_sub x b c))

end


/-- Swap a constant-scaled doubly-finite sum past an infinite sum, given pointwise summability.
The infinite sum `∑' m, c * (a m * e x y m)` is pushed outside the finite `x, y` sums. -/
private lemma tsum_finset_finset_const_mul_swap {ι κ μ : Type*} [Finite ι] [Finite κ]
    (c : ℂ) (a : μ → ℂ) (e : ι → κ → μ → ℂ)
    (hSummable : ∀ x : ι, ∀ y : κ, Summable fun m : μ => c * a m * e x y m) :
    (∑' x : ι, ∑' y : κ, c * ∑' m : μ, a m * e x y m)
      = c * ∑' m : μ, a m * (∑' x : ι, ∑' y : κ, e x y m) := by
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype κ := Fintype.ofFinite κ
  -- Commute the finite `y`-sum past the `m`-sum for each fixed `x`.
  have hswap_y : ∀ x : ι, (∑ y : κ, ∑' m : μ, c * (a m * e x y m))
      = ∑' m : μ, ∑ y : κ, c * (a m * e x y m) := fun x =>
    (Summable.tsum_finsetSum fun y _ => by simpa [mul_assoc] using hSummable x y).symm
  -- Commute the finite `x`-sum past the `m`-sum.
  have hswap_x : (∑ x : ι, ∑' m : μ, ∑ y : κ, c * (a m * e x y m))
      = ∑' m : μ, ∑ x : ι, ∑ y : κ, c * (a m * e x y m) :=
    (Summable.tsum_finsetSum fun x _ =>
      summable_sum fun y _ => by simpa [mul_assoc] using hSummable x y).symm
  simp only [tsum_fintype]
  simp_rw [← tsum_mul_left, hswap_y]
  rw [hswap_x]
  exact tsum_congr fun m => by simp_rw [← Finset.mul_sum]

/-- Summability on the dual lattice of `c * (𝓕 f m).re * exp(2πi⟪x - y, m⟫)`. -/
private lemma summable_const_mul_re_fourier_mul_exp {d : ℕ}
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (P : PeriodicSpherePacking d) (c : ℂ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    Summable fun m : SchwartzMap.dualLattice (d := d) P.lattice =>
      c * (((𝓕 f m).re : ℂ)) *
        exp (2 * π * I * ⟪x - y, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) := by
  have hFNorm : Summable fun m : SchwartzMap.dualLattice (d := d) P.lattice =>
      ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖ := by
    simpa using SpherePacking.CohnElkies.LPBoundAux.summable_norm_comp_add_zlattice
      (Λ := SchwartzMap.dualLattice (d := d) P.lattice) (f := 𝓕 f)
      (a := (0 : EuclideanSpace ℝ (Fin d)))
  refine Summable.of_norm_bounded
    (g := fun m => ‖c‖ * ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖)
    (by simpa [mul_assoc] using hFNorm.mul_left ‖c‖) fun m => by
    have hnexp : ‖exp (2 * π * I *
        ⟪x - y, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])‖ = (1 : ℝ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_exp_I_mul_ofReal (x := 2 * π *
          ⟪x - y, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))
    simp only [norm_mul, hnexp, mul_one, Complex.norm_real, Real.norm_eq_abs]
    gcongr; exact abs_re_le_norm _

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
  refine congrArg Complex.re ?_
  -- Package the covolume scalar `c`, Fourier coefficients `a`, and exponentials `e` for
  -- `tsum_finset_finset_const_mul_swap`.
  let c : ℂ := (1 / ZLattice.covolume P.lattice volume : ℂ)
  let a : SchwartzMap.dualLattice (d := d) P.lattice → ℂ := fun m => ((𝓕 f m).re : ℂ)
  let e : ↑(P.centers ∩ D) → ↑(P.centers ∩ D) →
      SchwartzMap.dualLattice (d := d) P.lattice → ℂ := fun x y m =>
    exp (2 * π * I * ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
      (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])
  have hFourierReal : ∀ m : SchwartzMap.dualLattice (d := d) P.lattice, (𝓕 f m) = a m :=
    fun m => by simpa [a] using (hRealFourier (m : EuclideanSpace ℝ (Fin d))).symm
  simpa [c, e, hFourierReal] using
    tsum_finset_finset_const_mul_swap c a e fun x y =>
      summable_const_mul_re_fourier_mul_exp f P c x y

variable {d : ℕ} {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)}
variable {P : PeriodicSpherePacking d} {D : Set (EuclideanSpace ℝ (Fin d))}

/-- If `D` uniquely covers each orbit and `x + ℓ = y` for some lattice element `ℓ`, then `ℓ = 0`. -/
private lemma lattice_translate_eq_zero (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    {x y : ↑(P.centers ∩ D)} {ℓ : P.lattice}
    (hxy : (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) =
        (y : EuclideanSpace ℝ (Fin d))) : ℓ = 0 := by
  obtain ⟨_, -, hg0_unique⟩ := hD_unique_covers (y : EuclideanSpace ℝ (Fin d))
  have hy0 : (0 : P.lattice) +ᵥ (y : EuclideanSpace ℝ (Fin d)) ∈ D := by
    simpa [Submodule.vadd_def] using y.property.2
  have hyℓ : (-ℓ : P.lattice) +ᵥ (y : EuclideanSpace ℝ (Fin d)) ∈ D := by
    -- `(-ℓ) +ᵥ y = -ℓ + y = x`, and `x ∈ D` by `x.property.2`.
    have hEq : ((-ℓ : P.lattice) : EuclideanSpace ℝ (Fin d)) + (y : EuclideanSpace ℝ (Fin d)) =
        (x : EuclideanSpace ℝ (Fin d)) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (eq_sub_of_add_eq hxy).symm
    simp only [Submodule.vadd_def, vadd_eq_add, hEq]
    exact x.property.2
  simpa using neg_eq_zero.mp ((hg0_unique (-ℓ) hyℓ).trans (hg0_unique 0 hy0).symm)

/-- If `x + ℓ ≠ y` as centers in `P`, then `f` evaluated on the shifted difference is `≤ 0`. -/
private lemma re_f_shifted_nonpos (hP : P.separation = 1)
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ P.centers) (hy : y ∈ P.centers) (ℓ : P.lattice)
    (hxℓy : x + (ℓ : EuclideanSpace ℝ (Fin d)) ≠ y) :
    (f (x - y + (ℓ : EuclideanSpace ℝ (Fin d)))).re ≤ 0 := by
  have hxℓ : x + (ℓ : EuclideanSpace ℝ (Fin d)) ∈ P.centers := by
    simpa [add_comm] using P.lattice_action ℓ.property hx
  have hnorm : (1 : ℝ) ≤ ‖x + (ℓ : EuclideanSpace ℝ (Fin d)) - y‖ := by
    simpa [hP, dist_eq_norm] using P.centers_dist' _ _ hxℓ hy hxℓy
  have hle := hCohnElkies₁ _ hnorm
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hle

/-- Diagonal case `x = y` of `lattice_sum_re_le_ite`: the lattice sum at the origin equals
the `ℓ = 0` value plus a nonpositive tail. -/
private lemma lattice_sum_re_le_ite_diag (hP : P.separation = 1)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (x : ↑(P.centers ∩ D)) :
    (∑' ℓ : P.lattice, (f (ℓ : EuclideanSpace ℝ (Fin d))).re) ≤ (f 0).re := by
  have hs : Summable fun ℓ : P.lattice => (f (ℓ : EuclideanSpace ℝ (Fin d))).re := by
    simpa [zero_add] using
      SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_translate_re
        (Λ := P.lattice) (f := f) (a := (0 : EuclideanSpace ℝ (Fin d)))
  have htail : (∑' ℓ : P.lattice,
        ite (ℓ = (0 : P.lattice)) 0 (f (ℓ : EuclideanSpace ℝ (Fin d))).re) ≤ 0 := by
    refine tsum_nonpos fun ℓ => ?_
    by_cases hℓ : ℓ = 0
    · simp [hℓ]
    have hxℓ : (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) ≠
        (x : EuclideanSpace ℝ (Fin d)) :=
      fun h => hℓ (lattice_translate_eq_zero hD_unique_covers h)
    simpa [hℓ, sub_self, zero_add] using
      re_f_shifted_nonpos hP hCohnElkies₁ x.property.1 x.property.1 ℓ hxℓ
  simpa [hs.tsum_eq_add_tsum_ite (0 : P.lattice)] using add_le_add_left htail (f 0).re

public lemma lattice_sum_re_le_ite (hP : P.separation = 1)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (x y : ↑(P.centers ∩ D)) :
    (∑' ℓ : P.lattice,
          (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re)
      ≤ ite (x = y) (f 0).re 0 := by
  by_cases hxy : x = y
  · subst hxy
    simpa [sub_self, zero_add] using
      lattice_sum_re_le_ite_diag (P := P) hP hD_unique_covers hCohnElkies₁ x
  · rw [if_neg hxy]
    refine tsum_nonpos fun ℓ => re_f_shifted_nonpos hP hCohnElkies₁
      x.property.1 y.property.1 ℓ (fun h => ?_)
    -- From `↑x + ↑ℓ = ↑y` we get `ℓ = 0`, hence `↑x = ↑y`, contradicting `x ≠ y`.
    have hℓ : ℓ = 0 := lattice_translate_eq_zero hD_unique_covers h
    exact hxy (Subtype.ext (by simpa [hℓ] using h))

end SpherePacking.CohnElkies

variable {d : ℕ}
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)} (hne_zero : f ≠ 0)
variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))
variable (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))
variable (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)

local notation "conj" => starRingEnd ℂ

/-- The Fourier transform of a Schwartz function is integrable. -/
theorem integrable_fourier : MeasureTheory.Integrable (𝓕 ⇑f) :=
  (FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) f).integrable

include hReal hRealFourier hCohnElkies₂ hne_zero in
theorem f_zero_pos : 0 < (f 0).re := by
  -- `f 0` is the integral of `𝓕 f`, which is nonnegative by `hCohnElkies₂`.
  have hnonneg : 0 ≤ (f 0).re := by
    rw [← f.fourierInversion, fourierInv_eq]
    simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul, ← RCLike.re_eq_complex_re]
    rw [show RCLike.re (∫ (v : EuclideanSpace ℝ (Fin d)), 𝓕 (⇑f) v) =
        ∫ v : EuclideanSpace ℝ (Fin d), RCLike.re ((𝓕 f) v) from
      (integral_re integrable_fourier).symm]
    exact integral_nonneg fun v ↦ by simpa using hCohnElkies₂ v
  -- If `(f 0).re = 0`, then `∫ 𝓕 f = 0`, hence `𝓕 f = 0`, hence `f = 0`, contradicting `hne_zero`.
  refine lt_of_le_of_ne hnonneg fun hf0re => hne_zero <|
    (ContinuousLinearEquiv.map_eq_zero_iff (FourierTransform.fourierCLE ℂ _)).1 ?_
  have hintegral_zero : ∫ v : EuclideanSpace ℝ (Fin d), (re ∘ 𝓕 ⇑f) v = 0 := by
    rw [show (∫ v : EuclideanSpace ℝ (Fin d), (re ∘ 𝓕 ⇑f) v) =
        (∫ v : EuclideanSpace ℝ (Fin d), 𝓕 (⇑f) v).re by
      simpa using integral_re (f := fun v : EuclideanSpace ℝ (Fin d) => 𝓕 (⇑f) v)
        integrable_fourier]
    simpa [fourierInv_eq, show f 0 = 0 by simpa [hf0re.symm] using (hReal 0).symm] using
      congrArg Complex.re (congrArg (· 0) f.fourierInversion)
  have hfun := (Continuous.integral_zero_iff_zero_of_nonneg
    (Complex.continuous_re.comp (𝓕 f).continuous) integrable_fourier.re hCohnElkies₂).1
    hintegral_zero
  ext x; simpa [show (𝓕 f x).re = 0 by simpa using congrFun hfun x] using (hRealFourier x).symm

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
      (CohnElkies.LPBoundAux.summable_norm_comp_add_zlattice
        (Λ := SchwartzMap.dualLattice (d := d) P.lattice) (f := 𝓕 f)
        (a := (0 : EuclideanSpace ℝ (Fin d)))).mul_right _
  simp only [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]; gcongr
  · simpa [Real.norm_eq_abs] using abs_re_le_norm _
  · simpa [tsum_fintype, Complex.norm_exp, mul_re, mul_im, mul_assoc, mul_left_comm, mul_comm]
      using norm_sum_le (Finset.univ : Finset ↑(P.centers ∩ D)) fun x : ↑(P.centers ∩ D) =>
      exp (2 * π * I * ⟪(x : EuclideanSpace ℝ (Fin d)), (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])

omit hRealFourier in include hP hCohnElkies₁ hD_unique_covers in
/-- Bound `numReps * (f 0).re` by the double sum of `f` values via `lattice_sum_re_le_ite`. -/
private lemma numReps_mul_f_zero_ge_double_tsum (hd : 0 < d) :
    ↑(P.numReps' hd hD_isBounded) * (f 0).re ≥
      ∑' (x : P.centers) (y : ↑(P.centers ∩ D)), (f (x - ↑y)).re := by
  letI : Fintype ↑(P.centers ∩ D) := P.instFintypeNumReps' hd hD_isBounded
  simp_rw [CohnElkies.tsum_centers_eq_tsum_centersInter_centersInter_lattice
    (f := f) (P := P) (D := D) hD_isBounded hD_unique_covers hd, tsum_fintype]
  exact (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ =>
    CohnElkies.lattice_sum_re_le_ite hP hD_unique_covers hCohnElkies₁ x i).trans
    (by simp [PeriodicSpherePacking.numReps'])

omit [Nonempty ↑P.centers] in include hD_isBounded in
/-- Pull `Complex.re` outside the triply-nested centers/centers/lattice sum. -/
private lemma re_tsum_triple_centers_inter_lattice (hd : 0 < d) :
    (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
        (f (↑x - ↑y + ↑ℓ : EuclideanSpace ℝ (Fin d))).re) =
      (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
        f (↑x - ↑y + ↑ℓ : EuclideanSpace ℝ (Fin d))).re := by
  haveI : Finite ↑(P.centers ∩ D) := finite_centers_inter_of_isBounded P D hD_isBounded hd
  rw [re_tsum Summable.of_finite]
  exact tsum_congr fun x => by
    rw [re_tsum Summable.of_finite]; exact tsum_congr fun y => by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (re_tsum (CohnElkies.LPBoundSummability.summable_lattice_translate
          (Λ := P.lattice) (f := f) (a := (↑x - ↑y : EuclideanSpace ℝ (Fin d))))).symm

/-- `exp(-(2πi⟪x, m⟫)) = conj (exp(2πi⟪x, m⟫))`. -/
private lemma exp_neg_two_pi_I_inner_eq_conj {d : ℕ} (x m : EuclideanSpace ℝ (Fin d)) :
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (⟪x, m⟫_[ℝ] : ℂ)))
      = conj (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (⟪x, m⟫_[ℝ] : ℂ))) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- Reduce `((c * ∑' m, a m * (z * conj z)).re : ℂ) = ↑((c * ∑' m, a m * ‖z‖^2).re)`,
the final normSq-identity step in the LP-bound calculation. -/
private lemma re_mul_conj_eq_norm_sq_step {d : ℕ}
    (P : PeriodicSpherePacking d) {D : Set (EuclideanSpace ℝ (Fin d))}
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    ((1 / ZLattice.covolume P.lattice volume) *
        ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, (𝓕 f m).re *
          (∑' x : ↑(P.centers ∩ D),
            exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) *
          conj (∑' x : ↑(P.centers ∩ D),
            exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))).re =
      (1 / ZLattice.covolume P.lattice volume) *
        ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
          (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
            exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2) := by
  rw [← ofReal_re (1 / ZLattice.covolume P.lattice volume *
    ∑' (m : ↥(LinearMap.BilinForm.dualSubmodule (innerₗ _) P.lattice)),
      (𝓕 ⇑f ↑m).re * norm (∑' (x : ↑(P.centers ∩ D)),
      cexp (2 * ↑π * I * ↑⟪(x : EuclideanSpace ℝ (Fin d)), ↑m⟫_[ℝ])) ^ 2)]
  congr 1; push_cast; congr! 3 with m
  rw [mul_assoc, mul_conj, Complex.normSq_eq_norm_sq]; norm_cast


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
  _ ≥ ∑' (x : P.centers) (y : ↑(P.centers ∩ D)), (f (x - ↑y)).re :=
        numReps_mul_f_zero_ge_double_tsum hCohnElkies₁ hP hD_isBounded hD_unique_covers hd
  _ = ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
      (f (↑x - ↑y + ↑ℓ)).re :=
        CohnElkies.tsum_centers_eq_tsum_centersInter_centersInter_lattice f P
          hD_isBounded hD_unique_covers hd
  _ = (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
      f (↑x - ↑y + ↑ℓ)).re := re_tsum_triple_centers_inter_lattice hD_isBounded hd
  _ = (∑' x : ↑(P.centers ∩ D),
      ∑' y : ↑(P.centers ∩ D), (1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, (𝓕 f m) *
      exp (2 * π * I * ⟪↑x - ↑y, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])).re := by
        congr! 5 with x y; exact SchwartzMap.poissonSummation_lattice P.lattice f _
  _ = ((1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
      (𝓕 f m).re * (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
      exp (2 * π * I * ⟪↑x - ↑y, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))).re := by
        simpa using CohnElkies.calc_steps_swap_sums (f := f)
          (hRealFourier := hRealFourier) (P := P) (D := D) hD_isBounded hd
  _ = ((1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, (𝓕 f m).re * (
      ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) *
      exp (2 * π * I * ⟪-↑y, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))).re := by
        congr! 9 with m x y
        simp [sub_eq_neg_add, RCLike.wInner_neg_left, ofReal_neg, mul_neg,
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
        simp_rw [conj_tsum]; congr! 7 with m x
        exact exp_neg_two_pi_I_inner_eq_conj _ _
  _ = (1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
        (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2) :=
        re_mul_conj_eq_norm_sq_step P f

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

omit [Nonempty ↑P.centers] in include hne_zero hReal hRealFourier hCohnElkies₂ in
/-- Degenerate case of the LP bound when `𝓕 f 0 = 0`: the right-hand side is `∞`. -/
private lemma density_le_of_𝓕_zero (h𝓕f : 𝓕 f 0 = 0) :
    ENat.toENNReal (P.numReps : ENat) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) /
        (ZLattice.covolume P.lattice volume).toNNReal ≤
      (f 0).re.toNNReal / (𝓕 f 0).re.toNNReal *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  have vol_ne_zero : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ≠ 0 :=
    (Metric.measure_ball_pos (μ := volume) _ one_half_pos).ne'
  have hf0_pos : 0 < (f 0).re := f_zero_pos hne_zero hReal hRealFourier hCohnElkies₂
  rw [h𝓕f, zero_re, toNNReal_zero, ENNReal.coe_zero,
    ENNReal.div_zero (ENNReal.coe_ne_zero.mpr (toNNReal_pos.mpr hf0_pos).ne'),
    ENNReal.top_mul vol_ne_zero]
  exact le_top

omit [Nonempty ↑P.centers] in include hRealFourier hCohnElkies₂ in
/-- Cast the real-valued LP inequality `numReps² * (𝓕 f 0).re / covolume ≤ numReps * (f 0).re`
to the ENNReal density bound, given `𝓕 f 0 ≠ 0`. -/
private lemma density_le_of_hCalc_of_ne_zero
    (hcov_pos : 0 < ZLattice.covolume P.lattice volume)
    [Nonempty (Quotient (AddAction.orbitRel ↥P.lattice ↑P.centers))]
    (h𝓕f : 𝓕 f 0 ≠ 0)
    (hCalc : (P.numReps : ℝ) ^ 2 * (𝓕 f 0).re / ZLattice.covolume P.lattice volume ≤
      (P.numReps : ℝ) * (f 0).re) :
    ENat.toENNReal (P.numReps : ENat) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) /
        (ZLattice.covolume P.lattice volume).toNNReal ≤
      (f 0).re.toNNReal / (𝓕 f 0).re.toNNReal *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  have vol_ne_zero : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ≠ 0 :=
    (Metric.measure_ball_pos (μ := volume) _ one_half_pos).ne'
  have hfouaux₁ : ((𝓕 f 0).re.toNNReal : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr <| by
    rw [ne_eq, Real.toNNReal_eq_zero, not_le]
    exact lt_of_le_of_ne (hCohnElkies₂ 0) fun heq => h𝓕f <|
      Complex.ext heq.symm (by simpa [eq_comm] using congrArg Complex.im (hRealFourier 0))
  -- Pull the casts of the two products out of the `ENNReal` arithmetic into `Real.toNNReal`.
  have hcast_num : (P.numReps : ENNReal) * ↑(f 0).re.toNNReal =
      ↑(P.numReps * (f 0).re).toNNReal := by
    simp [Real.toNNReal_mul (Nat.cast_nonneg _)]
  have hcast_sq : (P.numReps : ENNReal) ^ 2 * ((𝓕 f 0).re.toNNReal : ENNReal) /
      ((ZLattice.covolume P.lattice volume).toNNReal : ENNReal) =
      ↑((P.numReps : ℝ) ^ 2 * (𝓕 f 0).re / ZLattice.covolume P.lattice volume).toNNReal := by
    simp only [div_eq_mul_inv, ← ENNReal.coe_inv (Real.toNNReal_pos.mpr hcov_pos).ne',
      Real.toNNReal_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (hCohnElkies₂ 0))
        (inv_nonneg.mpr hcov_pos.le))]
    norm_cast
    rw [Real.toNNReal_of_nonneg (hCohnElkies₂ 0), Real.toNNReal_of_nonneg hcov_pos.le]; rfl
  rw [ENat.toENNReal_coe, mul_div_assoc, div_eq_mul_inv (volume _), mul_comm (volume _),
    ← mul_assoc, ENNReal.mul_le_mul_iff_left vol_ne_zero measure_ball_lt_top.ne,
    ← ENNReal.mul_le_mul_iff_left hfouaux₁ ENNReal.coe_ne_top,
    div_eq_mul_inv ((f 0).re.toNNReal : ENNReal) _, mul_assoc ((f 0).re.toNNReal : ENNReal) _ _,
    ENNReal.inv_mul_cancel hfouaux₁ ENNReal.coe_ne_top, mul_one, mul_assoc,
    ← ENNReal.div_eq_inv_mul, ← ENNReal.mul_le_mul_iff_right
      (by simpa [ENat.toENNReal_coe] using Fintype.card_ne_zero :
        ENat.toENNReal (P.numReps : ENat) ≠ 0)
      (Ne.symm (ne_of_beq_false rfl) : ENat.toENNReal (P.numReps : ENat) ≠ ⊤),
    ENat.toENNReal_coe, ← mul_assoc, ← pow_two, ← mul_div_assoc, hcast_num, hcast_sq,
    ENNReal.coe_le_coe]
  exact Real.toNNReal_le_toNNReal hCalc

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
    rw [hP]
    rw [ge_iff_le] at hCalc
    by_cases h𝓕f : 𝓕 f 0 = 0
    · exact density_le_of_𝓕_zero (P := P) hne_zero hReal hRealFourier hCohnElkies₂ h𝓕f
    rw [← PeriodicSpherePacking.numReps_eq_numReps' (S := P) Fact.out hD_isBounded
      hD_unique_covers] at hCalc
    haveI : Nonempty (Quotient (AddAction.orbitRel ↥P.lattice ↑P.centers)) :=
      (nonempty_quotient_iff _).2 ‹_›
    exact density_le_of_hCalc_of_ne_zero (P := P) hRealFourier hCohnElkies₂
      (ZLattice.covolume_pos P.lattice volume) h𝓕f hCalc
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
