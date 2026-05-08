module
public import SpherePacking.Basic.PeriodicPacking.DensityFormula

/-!
# Periodizing a sphere packing
-/

open scoped ENNReal Pointwise
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module

variable {d : ℕ}

/-- Any coordinate of a vector is bounded in absolute value by the Euclidean norm. -/
public lemma abs_coord_le_norm (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |x i| ≤ ‖x‖ := by
  simpa [EuclideanSpace.inner_single_left, EuclideanSpace.norm_single] using
    abs_real_inner_le_norm (EuclideanSpace.single i (1 : ℝ)) x

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
  refine ⟨?_, fun hxF => ⟨mem_periodizedCenters_iff.2 ⟨0, x, hxF, by simp⟩, hF_sub hxF⟩⟩
  rintro ⟨⟨_, ⟨g, rfl⟩, ⟨f, hfF, rfl⟩⟩, hxD⟩
  obtain ⟨_, _, hg0uniq⟩ := hD_unique_covers f
  simpa [hg0uniq g (by simpa using hxD), (hg0uniq 0 (by simpa using hF_sub hfF)).symm] using hfF

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

public lemma coordCube_eq_preimage_ofLp (L : ℝ) :
    coordCube d L =
      (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
        (Set.pi Set.univ fun _ : Fin d ↦ Set.Ico (0 : ℝ) L) := by
  ext x; simp [coordCube, Set.mem_pi]

public lemma volume_coordCube (L : ℝ) : volume (coordCube d L) = (ENNReal.ofReal L) ^ d := by
  rw [coordCube_eq_preimage_ofLp, volume_preimage_ofLp _
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
  simpa [add_vadd, Submodule.vadd_def, vadd_eq_add, add_assoc, add_comm] using
    ball_vadd_subset_vadd (d := d) (Λ := cubeLattice d L hL) (D := coordCube d L)
      (g := v) (x := (- (v : EuclideanSpace ℝ (Fin d))) +ᵥ x) (r := r)
      (ball_subset_coordCube_of_mem_inner
        (by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hx))

public lemma finite_lattice_in_ball (L : ℝ) (hL : 0 < L) (R : ℝ) :
    Set.Finite {g : cubeLattice d L hL | (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 R} := by
  refine (Set.Finite.preimage_embedding (f := ⟨fun g : cubeLattice d L hL =>
    (g : EuclideanSpace ℝ (Fin d)), Subtype.val_injective⟩) (by
      simpa [cubeLattice] using ZSpan.setFinite_inter (b := cubeBasis d L hL)
        (s := ball (0 : EuclideanSpace ℝ (Fin d)) R) Metric.isBounded_ball)).subset fun g hg => ?_
  exact ⟨hg, g.property⟩

end PeriodicConstantApprox
