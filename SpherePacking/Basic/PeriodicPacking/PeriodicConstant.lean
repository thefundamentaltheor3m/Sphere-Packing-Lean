module
public import SpherePacking.Basic.PeriodicPacking.DensityFormula

/-!
# Periodizing a sphere packing

This file defines a few auxiliary geometric constructions (coordinate cubes and their inner
subcubes) and uses them to "periodize" a sphere packing with respect to a lattice.

The key construction is `periodize_to_periodicSpherePacking`: given a sphere packing `S`, a lattice
`Λ`, a measurable domain `D` meeting each orbit in exactly one point, and a set of representatives
`F ⊆ S.centers` whose separation balls lie in `D`, we obtain a periodic sphere packing with lattice
`Λ` and centers `⋃ g : Λ, g +ᵥ F`.
-/

open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module

section PeriodicConstantAux

open MeasureTheory Metric EuclideanSpace
open scoped Pointwise

variable {d : ℕ}

/-- Any coordinate of a vector is bounded in absolute value by the Euclidean norm. -/
public lemma abs_coord_le_norm (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |x i| ≤ ‖x‖ := by
  simpa [EuclideanSpace.inner_single_left, EuclideanSpace.norm_single] using
    abs_real_inner_le_norm (EuclideanSpace.single i (1 : ℝ)) x

lemma abs_coord_sub_lt_of_mem_ball {x y : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hy : y ∈ ball x r)
    (i : Fin d) : |y i - x i| < r := by
  have hnorm : ‖y - x‖ < r := by simpa [Metric.mem_ball, dist_eq_norm, dist_comm] using hy
  exact lt_of_le_of_lt (by simpa using abs_coord_le_norm (d := d) (y - x) i) hnorm

lemma ball_subset_coordCube {x : EuclideanSpace ℝ (Fin d)} {r L : ℝ}
    (hx : ∀ i : Fin d, x i ∈ Set.Icc r (L - r)) :
    ball x r ⊆ {y : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, y i ∈ Set.Ico (0 : ℝ) L} := by
  intro y hy i
  have hxi := hx i
  have hsub : |y i - x i| < r := abs_coord_sub_lt_of_mem_ball (d := d) hy i
  have hsub' : -r < y i - x i ∧ y i - x i < r := abs_lt.mp hsub
  have hy_lower : 0 ≤ y i := by
    have hx0 : 0 ≤ x i - r := sub_nonneg.mpr hxi.1
    have hy_ge : x i - r < y i := by linarith [hsub'.1]
    exact hx0.trans (le_of_lt hy_ge)
  have hy_upper : y i < L := by
    have hy_lt : y i < x i + r := by linarith [hsub'.2]
    have hx_le : x i + r ≤ L := by linarith [hxi.2]
    exact lt_of_lt_of_le hy_lt hx_le
  exact ⟨hy_lower, hy_upper⟩

/--
If `ball x r ⊆ A` and `ball y r ⊆ B` with `A` and `B` disjoint, then the centers satisfy
`2 * r ≤ dist x y`.
-/
public lemma dist_le_of_disjoint_ball_subsets {x y : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    {A B : Set (EuclideanSpace ℝ (Fin d))}
    (hx : ball x r ⊆ A) (hy : ball y r ⊆ B) (hAB : Disjoint A B) :
    2 * r ≤ dist x y := by
  by_contra hlt
  have hlt' : dist x y < 2 * r := lt_of_not_ge hlt
  let m : EuclideanSpace ℝ (Fin d) := midpoint ℝ x y
  have hhalf : (1 / 2 : ℝ) * dist x y < r := by nlinarith
  have hmx : m ∈ ball x r := by
    have : dist m x < r := by simpa [m] using hhalf
    simpa [Metric.mem_ball, dist_comm] using this
  have hmy : m ∈ ball y r := by
    have : dist m y < r := by simpa [m, dist_comm] using hhalf
    simpa [Metric.mem_ball, dist_comm] using this
  exact (Set.disjoint_left.1 hAB (hx hmx) (hy hmy))

open scoped Pointwise in
/-- The union of all lattice translates of a set `F` of representatives. -/
@[expose] public noncomputable def periodizedCenters (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    (F : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) :=
  ⋃ g : Λ, g +ᵥ F

/-- Membership in `periodizedCenters` is equivalent to being a translate of a point in `F`. -/
public lemma mem_periodizedCenters_iff {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {F : Set (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)} :
    x ∈ periodizedCenters (d := d) Λ F ↔ ∃ g : Λ, ∃ f ∈ F, x = g +ᵥ f := by
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨g : Λ, hg⟩
    rcases Set.mem_vadd_set.1 hg with ⟨f, hf, rfl⟩
    exact ⟨g, f, hf, rfl⟩
  · rintro ⟨g, f, hf, rfl⟩
    exact Set.mem_iUnion.2 ⟨g, Set.mem_vadd_set.2 ⟨f, hf, rfl⟩⟩

/-! ## Basic closure properties -/

/-- `periodizedCenters` is closed under addition by lattice vectors. -/
public lemma periodizedCenters_lattice_action {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {F : Set (EuclideanSpace ℝ (Fin d))} {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ Λ) (hy : y ∈ periodizedCenters (d := d) Λ F) :
    x + y ∈ periodizedCenters (d := d) Λ F := by
  rcases (mem_periodizedCenters_iff (d := d) (Λ := Λ) (F := F) (x := y)).1 hy with ⟨g, f, hf, rfl⟩
  refine (mem_periodizedCenters_iff (d := d) (Λ := Λ) (F := F)).2 ⟨(⟨x, hx⟩ : Λ) + g, f, hf, ?_⟩
  simp [Submodule.vadd_def, vadd_eq_add, add_assoc]

/-- Translating a ball by a lattice vector stays inside the translate of the ambient set. -/
public lemma ball_vadd_subset_vadd {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {D : Set (EuclideanSpace ℝ (Fin d))} {r : ℝ} {g : Λ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : ball x r ⊆ D) :
    ball (g +ᵥ x) r ⊆ g +ᵥ D := by
  intro y hy
  have hback : (- (g : EuclideanSpace ℝ (Fin d))) +ᵥ y ∈ ball x r := by
    have :
        (- (g : EuclideanSpace ℝ (Fin d))) +ᵥ y ∈
          (- (g : EuclideanSpace ℝ (Fin d))) +ᵥ ball (g +ᵥ x) r := by
      refine Set.mem_vadd_set.2 ⟨y, ?_, rfl⟩
      simpa [Submodule.vadd_def, vadd_eq_add] using hy
    -- `(-g)+ᵥ ball (g+ᵥ x) r = ball x r`
    simpa [Metric.vadd_ball, add_vadd, Submodule.vadd_def, vadd_eq_add] using this
  have hzD : (-g : Λ) +ᵥ y ∈ D := by
    apply hx
    simpa [Submodule.vadd_def, vadd_eq_add] using hback
  refine Set.mem_vadd_set.2 ⟨(-g : Λ) +ᵥ y, hzD, ?_⟩
  simp [Submodule.vadd_def, vadd_eq_add]

/--
Construct a periodic sphere packing by translating a set of representatives `F ⊆ S.centers`
along a lattice `Λ`.
-/
@[expose] public noncomputable def periodize_to_periodicSpherePacking
    (S : SpherePacking d)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (D F : Set (EuclideanSpace ℝ (Fin d)))
    (hD_unique_covers : ∀ x, ∃! g : Λ, g +ᵥ x ∈ D)
    (hF_centers : F ⊆ S.centers)
    (hF_ball : ∀ x ∈ F, ball x (S.separation / 2) ⊆ D) :
    PeriodicSpherePacking d := by
  refine
    { centers := periodizedCenters (d := d) Λ F
      separation := S.separation
      separation_pos := S.separation_pos
      centers_dist := ?_
      lattice := Λ
      lattice_action := ?_
      lattice_discrete := inferInstance
      lattice_isZLattice := inferInstance }
  · -- `centers_dist`
    intro a b hab
    change S.separation ≤ dist (a : EuclideanSpace ℝ (Fin d)) (b : EuclideanSpace ℝ (Fin d))
    rcases (mem_periodizedCenters_iff (d := d) (Λ := Λ) (F := F)
      (x := (a : EuclideanSpace ℝ (Fin d)))).1
        a.property with ⟨ga, fa, hfa, ha⟩
    rcases (mem_periodizedCenters_iff (d := d) (Λ := Λ) (F := F)
      (x := (b : EuclideanSpace ℝ (Fin d)))).1
        b.property with ⟨gb, fb, hfb, hb⟩
    by_cases hgg : ga = gb
    · subst hgg
      have hne : fa ≠ fb := by
        intro h
        apply hab
        apply Subtype.ext
        simp [ha, hb, h]
      have hdist := S.centers_dist' fa fb (hF_centers hfa) (hF_centers hfb) hne
      -- rewrite the distance using translation invariance
      have : S.separation ≤ dist (ga +ᵥ fa) (ga +ᵥ fb) := by
        have htrans : dist (ga +ᵥ fa) (ga +ᵥ fb) = dist fa fb := by
          exact dist_vadd_cancel_left (ga : EuclideanSpace ℝ (Fin d)) fa fb
        simpa [htrans] using hdist
      simpa [ha, hb] using this
    · -- different lattice translates: use disjointness of translated domains + midpoint argument
      have hballa : ball (ga +ᵥ fa) (S.separation / 2) ⊆ ga +ᵥ D :=
        ball_vadd_subset_vadd (d := d) (Λ := Λ) (D := D) (g := ga) (x := fa) (r := S.separation / 2)
          (hF_ball fa hfa)
      have hballb : ball (gb +ᵥ fb) (S.separation / 2) ⊆ gb +ᵥ D :=
        ball_vadd_subset_vadd (d := d) (Λ := Λ) (D := D) (g := gb) (x := fb) (r := S.separation / 2)
          (hF_ball fb hfb)
      have hdisj : Disjoint (ga +ᵥ D) (gb +ᵥ D) :=
        disjoint_vadd_of_unique_covers (d := d) (Λ := Λ) (D := D) hD_unique_covers hgg
      have : 2 * (S.separation / 2) ≤ dist (ga +ᵥ fa) (gb +ᵥ fb) :=
        dist_le_of_disjoint_ball_subsets (d := d) hballa hballb hdisj
      have : S.separation ≤ dist (ga +ᵥ fa) (gb +ᵥ fb) := by
        simpa [two_mul, add_halves] using this
      simpa [ha, hb] using this
  · -- lattice_action
    intro x y hx hy
    exact periodizedCenters_lattice_action (d := d) (Λ := Λ) (F := F) hx hy

end PeriodicConstantAux

section PeriodicConstantCube

open scoped Pointwise

variable {d : ℕ}

/-- The coordinate cube `[0,L)^d` as a set in `EuclideanSpace`. -/
@[expose] public def coordCube (L : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, x i ∈ Set.Ico (0 : ℝ) L}

/-- The "inner cube" `[r, L-r]^d` (closed intervals) used to keep radius-`r` balls inside
`coordCube L`. -/
@[expose] public def coordCubeInner (L r : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, x i ∈ Set.Icc r (L - r)}

/-- A scaled basis used to realize `coordCube L` as a fundamental domain. -/
@[expose] public noncomputable def cubeBasis (L : ℝ) (hL : 0 < L) :
    Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis).isUnitSMul
    (fun _ : Fin d ↦ IsUnit.mk0 L (ne_of_gt hL))

/-- The lattice generated by `cubeBasis L hL`. -/
@[expose] public noncomputable def cubeLattice (L : ℝ) (hL : 0 < L) :
    Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℤ (Set.range (cubeBasis (d := d) L hL))

public lemma fundamentalDomain_cubeBasis_eq_coordCube (L : ℝ) (hL : 0 < L) :
    fundamentalDomain (cubeBasis (d := d) L hL) = coordCube (d := d) L := by
  ext x
  -- unfold the definition of `ZSpan.fundamentalDomain` and compute coordinates on the scaled basis
  simp only [ZSpan.mem_fundamentalDomain, coordCube, cubeBasis, Module.Basis.repr_isUnitSMul,
    Units.smul_def, Units.val_inv_eq_inv_val, Set.mem_setOf_eq,
    Set.mem_Ico]
  constructor
  · intro hx i
    specialize hx i
    have hmul (t : ℝ) : (L : ℝ) * (L⁻¹ * t) = t := by
      calc
        (L : ℝ) * (L⁻¹ * t) = (L * L⁻¹) * t := by simp [mul_assoc]
        _ = (1 : ℝ) * t := by simp [mul_inv_cancel₀ (ne_of_gt hL)]
        _ = t := by simp
    refine ⟨?_, ?_⟩
    · have : 0 ≤ (L : ℝ) * (L⁻¹ * x i) := mul_nonneg (le_of_lt hL) hx.1
      simpa [hmul] using this
    · have : (L : ℝ) * (L⁻¹ * x i) < (L : ℝ) * 1 := mul_lt_mul_of_pos_left hx.2 hL
      simpa [hmul] using this
  · intro hx i
    specialize hx i
    have hLinv : 0 < (L⁻¹ : ℝ) := inv_pos.mpr hL
    refine ⟨mul_nonneg (le_of_lt hLinv) hx.1, ?_⟩
    have : (L⁻¹ : ℝ) * x i < (L⁻¹ : ℝ) * L := mul_lt_mul_of_pos_left hx.2 hLinv
    simpa [mul_assoc, inv_mul_cancel₀ (ne_of_gt hL), one_mul] using this

lemma ball_subset_coordCube_of_mem_inner {L r : ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ coordCubeInner (d := d) L r) :
    ball x r ⊆ coordCube (d := d) L := by
  simpa [coordCube, coordCubeInner] using
    (ball_subset_coordCube (d := d) (x := x) (r := r) (L := L) hx)

public lemma periodizedCenters_inter_eq_of_subset {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {D F : Set (EuclideanSpace ℝ (Fin d))}
    (hF_sub : F ⊆ D) (hD_unique_covers : ∀ x, ∃! g : Λ, g +ᵥ x ∈ D) :
    periodizedCenters (d := d) Λ F ∩ D = F := by
  ext x
  constructor
  · rintro ⟨hxPer, hxD⟩
    rcases (mem_periodizedCenters_iff (d := d) (Λ := Λ) (F := F) (x := x)).1 hxPer with
      ⟨g, f, hfF, rfl⟩
    obtain ⟨g0, hg0, hg0uniq⟩ := hD_unique_covers f
    have hg : g = g0 := hg0uniq g (by simpa using hxD)
    have hg0 : g0 = 0 := by
      simpa using (hg0uniq 0 (by simpa using hF_sub hfF)).symm
    simpa [hg, hg0] using hfF
  · intro hxF
    refine ⟨?_, hF_sub hxF⟩
    refine (mem_periodizedCenters_iff (d := d) (Λ := Λ) (F := F) (x := x)).2 ?_
    refine ⟨0, x, hxF, ?_⟩
    simp

end PeriodicConstantCube

section Periodic_Constant_Eq_Constant

open scoped Pointwise

namespace PeriodicConstant

variable {d : ℕ}

private lemma volume_preimage_ofLp (s : Set (Fin d → ℝ)) (hs : MeasurableSet s) :
    volume ((fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹' s) = volume s := by
  simpa using
    (PiLp.volume_preserving_ofLp (ι := Fin d)).measure_preimage hs.nullMeasurableSet

public lemma coordCube_unique_covers (L : ℝ) (hL : 0 < L) :
    ∀ x, ∃! g : cubeLattice (d := d) L hL, g +ᵥ x ∈ coordCube (d := d) L := by
  intro x
  -- use the library fundamental-domain fact, then rewrite by our explicit cube description
  simpa [cubeLattice, fundamentalDomain_cubeBasis_eq_coordCube (d := d) (L := L) (hL := hL)] using
    (exist_unique_vadd_mem_fundamentalDomain (cubeBasis (d := d) L hL) x)

public lemma isBounded_coordCube (L : ℝ) (hL : 0 < L) : IsBounded (coordCube (d := d) L) := by
  simpa [fundamentalDomain_cubeBasis_eq_coordCube (d := d) (L := L) (hL := hL)] using
    (fundamentalDomain_isBounded (cubeBasis (d := d) L hL))

public lemma measurableSet_coordCube (L : ℝ) (hL : 0 < L) :
    MeasurableSet (coordCube (d := d) L) := by
  simpa [fundamentalDomain_cubeBasis_eq_coordCube (d := d) (L := L) (hL := hL)] using
    (fundamentalDomain_measurableSet (cubeBasis (d := d) L hL))

public lemma coordCube_eq_preimage_ofLp (L : ℝ) :
    coordCube (d := d) L =
      (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
        (Set.pi Set.univ fun _ : Fin d ↦ Set.Ico (0 : ℝ) L) := by
  ext x
  simp [coordCube, Set.mem_pi]

public lemma volume_coordCube (L : ℝ) :
    volume (coordCube (d := d) L) = (ENNReal.ofReal L) ^ d := by
  have hmeas : MeasurableSet (Set.pi Set.univ fun _ : Fin d ↦ Set.Ico (0 : ℝ) L) := by
    simpa using (MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_Ico)
  have hpre :
      volume (coordCube (d := d) L) =
        volume (Set.pi Set.univ fun _ : Fin d ↦ Set.Ico (0 : ℝ) L) := by
    simpa [coordCube_eq_preimage_ofLp (d := d) (L := L)] using
      (volume_preimage_ofLp (d := d) (s := Set.pi Set.univ fun _ : Fin d ↦ Set.Ico (0 : ℝ) L)
        hmeas)
  -- compute the product volume
  rw [hpre, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico, sub_zero]

public lemma coordCubeInner_eq_preimage_ofLp (L r : ℝ) :
    coordCubeInner (d := d) L r =
      (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
        (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc r (L - r)) := by
  ext x
  simp [coordCubeInner, Pi.le_def, forall_and]

public lemma volume_coordCubeInner (L r : ℝ) :
    volume (coordCubeInner (d := d) L r) = (ENNReal.ofReal (L - 2 * r)) ^ d := by
  have hmeas : MeasurableSet (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc r (L - r)) := by
    exact MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_Icc
  have hpre :
      volume (coordCubeInner (d := d) L r) =
        volume (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc r (L - r)) := by
    simpa [coordCubeInner_eq_preimage_ofLp (d := d) (L := L) (r := r)] using
      (volume_preimage_ofLp (d := d) (s := Set.pi Set.univ fun _ : Fin d ↦ Set.Icc r (L - r))
        hmeas)
  rw [hpre, volume_pi, Measure.pi_pi]
  -- each coordinate contributes `(L - r) - r = L - 2r`
  simp [Real.volume_Icc, sub_eq_add_neg, add_left_comm, add_comm, two_mul]

public lemma coordCubeInner_subset_coordCube {L r : ℝ} (hr : 0 < r) :
    coordCubeInner (d := d) L r ⊆ coordCube (d := d) L := by
  intro x hx i
  have hxi : x i ∈ Set.Icc r (L - r) := hx i
  exact ⟨le_trans hr.le hxi.1, lt_of_le_of_lt hxi.2 (sub_lt_self L hr)⟩

end PeriodicConstant

section PeriodicConstantApprox

open scoped Pointwise
open MeasureTheory Metric

namespace PeriodicConstantApprox

variable {d : ℕ}

public lemma coordCube_unique_covers_vadd (L : ℝ) (hL : 0 < L)
    (v : cubeLattice (d := d) L hL) :
    ∀ x, ∃! g : cubeLattice (d := d) L hL, g +ᵥ x ∈ v +ᵥ coordCube (d := d) L := by
  intro x
  have hvadd (a : cubeLattice (d := d) L hL) :
      a +ᵥ x ∈ v +ᵥ coordCube (d := d) L ↔ (a - v) +ᵥ x ∈ coordCube (d := d) L := by
    -- translate by `-v` and simplify `(-v) + (a + x) = (a - v) + x`
    simp [Set.mem_vadd_set_iff_neg_vadd_mem, Submodule.vadd_def, vadd_eq_add, sub_eq_add_neg,
      add_assoc, add_comm]
  obtain ⟨g, hg, hguniq⟩ := PeriodicConstant.coordCube_unique_covers (d := d) L hL x
  refine ⟨g + v, (hvadd (a := g + v)).2 (by simpa using hg), ?_⟩
  intro a ha
  have ha' : (a - v) +ᵥ x ∈ coordCube (d := d) L := (hvadd a).1 ha
  have : a - v = g := hguniq _ ha'
  exact (sub_eq_iff_eq_add).1 this

public lemma ball_subset_vadd_coordCube_of_mem_vadd_inner {L r : ℝ} (hL : 0 < L)
    {v : cubeLattice (d := d) L hL} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ v +ᵥ coordCubeInner (d := d) L r) :
    ball x r ⊆ v +ᵥ coordCube (d := d) L := by
  -- translate back to the origin cell
  have hx' : (- (v : EuclideanSpace ℝ (Fin d))) +ᵥ x ∈ coordCubeInner (d := d) L r := by
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hx
  have hball : ball ((- (v : EuclideanSpace ℝ (Fin d))) +ᵥ x) r ⊆ coordCube (d := d) L :=
    ball_subset_coordCube_of_mem_inner (d := d) (L := L) (r := r) hx'
  -- translate forward by `v`
  have h :=
    ball_vadd_subset_vadd (d := d) (Λ := cubeLattice (d := d) L hL) (D := coordCube (d := d) L)
      (g := v) (x := (- (v : EuclideanSpace ℝ (Fin d))) +ᵥ x) (r := r) hball
  simpa [add_vadd, Submodule.vadd_def, vadd_eq_add, add_assoc, add_comm] using h

public lemma coordCube_subset_ball (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, coordCube (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C := by
  simpa using (PeriodicConstant.isBounded_coordCube (d := d) L hL).subset_ball 0

public lemma finite_lattice_in_ball (L : ℝ) (hL : 0 < L) (R : ℝ) :
    Set.Finite {g : cubeLattice (d := d) L hL | (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 R} := by
  -- first show finiteness of the corresponding subset of `EuclideanSpace`
  have hfinE : Set.Finite ((ball (0 : EuclideanSpace ℝ (Fin d)) R) ∩
      (cubeLattice (d := d) L hL : Set (EuclideanSpace ℝ (Fin d)))) := by
    simpa [cubeLattice] using
      (ZSpan.setFinite_inter (b := cubeBasis (d := d) L hL)
        (s := ball (0 : EuclideanSpace ℝ (Fin d)) R) Metric.isBounded_ball)
  -- pull back along the coercion `cubeLattice → EuclideanSpace`
  let s : Set (cubeLattice (d := d) L hL) := {g | (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 R}
  have hfinImage :
      Set.Finite ((fun g : cubeLattice (d := d) L hL => (g : EuclideanSpace ℝ (Fin d))) '' s) := by
    refine hfinE.subset ?_
    rintro x ⟨g, hg, rfl⟩
    exact ⟨hg, g.property⟩
  refine Set.Finite.of_finite_image (s := s) (f := fun g : cubeLattice (d := d) L hL =>
      (g : EuclideanSpace ℝ (Fin d))) hfinImage
      (Set.injOn_of_injective Subtype.val_injective)

end PeriodicConstantApprox

end PeriodicConstantApprox

end Periodic_Constant_Eq_Constant
