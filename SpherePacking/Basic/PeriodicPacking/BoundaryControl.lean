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
noncomputable def coordCubeCover (x : EuclideanSpace ℝ (Fin d)) : cubeLattice d L hL :=
  Classical.choose (PeriodicConstant.coordCube_unique_covers L hL x)

lemma coordCubeCover_spec (x : EuclideanSpace ℝ (Fin d)) :
    coordCubeCover L hL x +ᵥ x ∈ coordCube d L :=
  (Classical.choose_spec (PeriodicConstant.coordCube_unique_covers L hL x)).1

lemma coordCubeCover_unique (x : EuclideanSpace ℝ (Fin d)) (g : cubeLattice d L hL)
    (hg : g +ᵥ x ∈ coordCube d L) :
    g = coordCubeCover L hL x :=
  (Classical.choose_spec (PeriodicConstant.coordCube_unique_covers L hL x)).2 g hg

lemma neg_coordCubeCover_mem_ball {C R : ℝ}
    (hC : coordCube d L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ ball 0 R) :
    ((-coordCubeCover L hL x : cubeLattice d L hL) :
        EuclideanSpace ℝ (Fin d)) ∈ ball 0 (R + C) := by
  set g := (coordCubeCover L hL x : EuclideanSpace ℝ (Fin d))
  rw [mem_ball_zero_iff, show ((-coordCubeCover L hL x : cubeLattice d L hL) :
    EuclideanSpace ℝ (Fin d)) = -g from rfl, norm_neg]
  have htri : ‖g‖ ≤ ‖g + x‖ + ‖x‖ := by
    simpa [add_sub_cancel_right] using norm_sub_le (g + x) x
  linarith [show ‖x‖ < R by simpa [mem_ball_zero_iff] using hx,
    show ‖g + x‖ < C by simpa [mem_ball_zero_iff] using hC (by
      simpa [Submodule.vadd_def, vadd_eq_add] using coordCubeCover_spec L hL x)]

lemma mem_vadd_coordCube_iff_eq_neg_coordCubeCover (g : cubeLattice d L hL)
    (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ g +ᵥ coordCube d L ↔ g = -coordCubeCover L hL x :=
  ⟨fun hx => by rw [← neg_neg g, coordCubeCover_unique L hL x (-g)
      (by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hx)],
   fun h => h ▸ by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using coordCubeCover_spec L hL x⟩

end CoordCubeCover

section CoverVolumeBound

open scoped BigOperators

lemma card_finite_lattice_in_ball_mul_volume_coordCube_le_volume_ball {L : ℝ} (hL : 0 < L)
    {R C : ℝ} (hC : coordCube d L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C) :
    let htSet :=
      PeriodicConstantApprox.finite_lattice_in_ball (d := d) L hL (R + C)
    let t : Finset (cubeLattice d L hL) := htSet.toFinset
    (t.card : ℝ≥0∞) * volume (coordCube d L) ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C))) := by
  intro htSet t
  calc (↑t.card : ℝ≥0∞) * volume (coordCube d L)
      = ∑ g ∈ t, volume (g +ᵥ coordCube d L) := by simp [measure_vadd, Finset.sum_const]
    _ = volume (⋃ g ∈ t, g +ᵥ coordCube d L) := (measure_biUnion_finset
        (fun _ _ _ _ hgh => disjoint_vadd_of_unique_covers (d := d)
          (PeriodicConstant.coordCube_unique_covers L hL) hgh)
        (fun g _ => by simpa using
          MeasurableSet.const_vadd (PeriodicConstant.measurableSet_coordCube L hL) g)).symm
    _ ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C))) := volume.mono <| by
        rintro y hy
        obtain ⟨g, hgT, x, hx, rfl⟩ := Set.mem_iUnion₂.1 hy
        have hg : (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 (R + C) :=
          htSet.mem_toFinset.1 (by simpa [t] using hgT)
        simp only [vadd_eq_add, mem_ball_zero_iff]
        linarith [norm_add_le (g : EuclideanSpace ℝ (Fin d)) x,
          mem_ball_zero_iff.mp (hC hx), mem_ball_zero_iff.mp hg]

end CoverVolumeBound

section BoundaryControl

open scoped ENNReal Pointwise BigOperators

def constVec (d : ℕ) (c : ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun _ : Fin d => c)

/-- If `x` lies in the width-`1/2` boundary strip of `coordCube L`, then the `1/2`-ball around `x`
lies in a fixed set of finite volume independent of the translate. -/
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
    obtain ⟨hyi_l, hyi_r⟩ := abs_le.mp (hyi i).le
    exact ⟨by simpa [add_assoc, add_left_comm, add_comm] using
        (by linarith [(hx.1 i).1] : (0:ℝ) ≤ x i + y i + (1/2:ℝ)),
      by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (by linarith [(hx.1 i).2.le] : x i + y i + (1/2:ℝ) ≤ L + 1)⟩
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
            coordCubeInner d L 1) := by
    intro y hy
    obtain ⟨x, hxS, hyBall⟩ : ∃ x ∈ s, y ∈ ball x r := by simpa using hy
    have hxB := hs_boundary x hxS
    set x0 : EuclideanSpace ℝ (Fin d) := (-(g : EuclideanSpace ℝ (Fin d))) +ᵥ x
    set y0 : EuclideanSpace ℝ (Fin d) := (-(g : EuclideanSpace ℝ (Fin d))) +ᵥ y
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, y0] using
      coordCube_boundary_half_add_ball_subset_outer_diff_inner (d := d) L
        (by simpa [r] using (show y0 ∈ (coordCube d L \ coordCubeInner d L (1 / 2)) +
            ball (0 : EuclideanSpace ℝ (Fin d)) r from
          ⟨x0, ⟨by simpa [Set.mem_vadd_set_iff_neg_vadd_mem, x0] using hxB.1,
            fun h => hxB.2 (by simpa [Set.mem_vadd_set_iff_neg_vadd_mem, x0] using h)⟩,
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

open Filter

lemma volume_cubeShell_eq_pow (L : ℝ) :
    volume (((constVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner d (L + 1) 0) \
        coordCubeInner d L 1) =
      (ENNReal.ofReal (L + 1)) ^ d - (ENNReal.ofReal (L - 2)) ^ d := by
  have hsub : coordCubeInner d L 1 ⊆
      (constVec d (- (1 / 2 : ℝ))) +ᵥ coordCubeInner d (L + 1) 0 := fun x hx =>
    Set.mem_vadd_set_iff_neg_vadd_mem.2 fun i => by
      simp only [coordCubeInner, Set.mem_setOf_eq, constVec, vadd_eq_add, one_div,
        WithLp.ofLp_add, WithLp.ofLp_neg, Pi.add_apply, Pi.neg_apply, neg_neg] at hx ⊢
      exact ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩
  simpa [measure_vadd, constVec, PeriodicConstant.volume_coordCubeInner] using
    measure_diff (μ := volume) hsub
      (show MeasurableSet (coordCubeInner d L 1) by
        simpa [PeriodicConstant.coordCubeInner_eq_preimage_ofLp] using
          (MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Icc).preimage
            (PiLp.volume_preserving_ofLp (ι := Fin d)).measurable).nullMeasurableSet
      (by simp [PeriodicConstant.volume_coordCubeInner])

section CubeLatticeCovolume

open scoped ENNReal
open ZSpan

lemma toNNReal_covolume_cubeLattice (L : ℝ) (hL : 0 < L) :
    Real.toNNReal (ZLattice.covolume (cubeLattice d L hL) volume) =
      (volume (coordCube d L)).toNNReal := by
  letI : DiscreteTopology (cubeLattice d L hL) := by dsimp [cubeLattice]; infer_instance
  letI : IsZLattice ℝ (cubeLattice d L hL) := by dsimp [cubeLattice]; infer_instance
  simp [show ZLattice.covolume (cubeLattice d L hL) volume = (volume (coordCube d L)).toReal by
    simpa [Measure.real, fundamentalDomain_cubeBasis_eq_coordCube L hL] using
      ZLattice.covolume_eq_measure_fundamentalDomain (L := cubeLattice d L hL) (μ := volume)
        (by simpa [cubeLattice] using ZSpan.isAddFundamentalDomain (cubeBasis d L hL) volume :
          IsAddFundamentalDomain (cubeLattice d L hL)
            (fundamentalDomain (cubeBasis d L hL)) volume)]

end CubeLatticeCovolume

section PeriodizeCubeDensity

open scoped ENNReal Pointwise
open SpherePacking EuclideanSpace MeasureTheory Metric Bornology

variable {d : ℕ}

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
  letI : DiscreteTopology (cubeLattice d L hL) := by dsimp [cubeLattice]; infer_instance
  letI : IsZLattice ℝ (cubeLattice d L hL) := by dsimp [cubeLattice]; infer_instance
  have hD_unique := PeriodicConstantApprox.coordCube_unique_covers_vadd L hL g
  let P : PeriodicSpherePacking d :=
    periodize_to_periodicSpherePacking (d := d) S (Λ := cubeLattice d L hL) D Fset
      (hD_unique_covers := hD_unique) (hF_centers := by assumption)
      (hF_ball := fun x hx => ball_subset_vadd_coordCube_of_mem_vadd_inner hL <| by
        simpa [hSsep] using hF_inner x (by simpa [Fset] using hx))
  have hPsep : P.separation = 1 := by simpa [P, hSsep]
  have hcenters_inter : P.centers ∩ D = Fset := by
    simpa [P, periodize_to_periodicSpherePacking, Fset] using
      periodizedCenters_inter_eq_of_subset (d := d) (Λ := cubeLattice d L hL) (D := D)
        (F := Fset) (fun x hx => by
          rcases hF_inner x (by simpa [Fset] using hx) with ⟨a, ha, rfl⟩
          exact ⟨a, PeriodicConstant.coordCubeInner_subset_coordCube (by norm_num) ha, rfl⟩)
        hD_unique
  have hnumReps : P.numReps = F.card := by
    exact_mod_cast show (P.numReps : ENat) = (F.card : ENat) by
      simpa [hcenters_inter, Fset, Set.encard_coe_eq_coe_finsetCard] using
        (P.encard_centers_inter_isFundamentalDomain (d := d) (D := D)
          (by simpa [D, Submodule.vadd_def, vadd_eq_add] using
            (PeriodicConstant.isBounded_coordCube L hL).vadd (g : EuclideanSpace ℝ (Fin d)) :
            IsBounded D) hD_unique hd).symm
  exact ⟨P, hPsep, by simpa [hnumReps, hPsep] using P.density_eq' (d := d) hd⟩

end PeriodizeCubeDensity

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

open Filter
open scoped ENNReal BigOperators

variable {d : ℕ}

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
  obtain ⟨C, hC⟩ := PeriodicConstantApprox.coordCube_subset_ball L hLpos
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
  have hcubeShell : cubeShellErr L = shellVol / volCube := by simp [cubeShellErr, shellVol, volCube]
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
  obtain ⟨g0, hg0t, hg0max⟩ := Finset.exists_max_image t (fun g => (s.filter fun x => f x = g).card)
    ⟨0, htSet.mem_toFinset.2 (by simp [Metric.mem_ball]; positivity)⟩
  let sg : Finset (EuclideanSpace ℝ (Fin d)) := s.filter fun x => f x = g0
  have hsg_centers : ∀ x ∈ sg, x ∈ S.centers := fun x hx =>
    (hX.mem_toFinset.1 (Finset.mem_filter.1 hx).1).1
  have hsg_memCube : ∀ x ∈ sg, x ∈ g0 +ᵥ coordCube d L := fun x hx =>
    (PeriodicConstantApprox.mem_vadd_coordCube_iff_eq_neg_coordCubeCover L hLpos g0 x).mpr
      (Finset.mem_filter.1 hx).2.symm
  have hs_le : (s.card : ℝ≥0∞) ≤ (t.card : ℝ≥0∞) * (sg.card : ℝ≥0∞) := by
    exact_mod_cast by simpa [Finset.card_eq_sum_card_fiberwise hf_maps, Finset.sum_const] using
      Finset.sum_le_sum hg0max
  have ht_vol : ((t.card : ℝ≥0∞) * volCube)
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R₁ + 2 * C)) := by
    simpa [volCube, R₁, r, t, htSet] using
      PeriodicConstantApprox.card_finite_lattice_in_ball_mul_volume_coordCube_le_volume_ball
        hLpos hC
  have hs_enc : ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞)
      = s.card := congrArg ((↑) : ENat → ℝ≥0∞)
    (show (S.centers ∩ ball 0 (R + r)).Finite by
      simpa [R₁, r, add_assoc, add_left_comm, add_comm] using hX).encard_eq_coe_toFinset_card
  have hR2 : R + Cshift = R₁ + 2 * C := by simp [Cshift, R₁, r, add_left_comm, add_comm]
  have hs_mul : ((S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + r)).encard : ℝ≥0∞)
      * volCube ≤ (sg.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + Cshift)) :=
    calc ((S.centers ∩ ball _ (R + r)).encard : ℝ≥0∞) * volCube
        = (s.card : ℝ≥0∞) * volCube := by rw [hs_enc]
      _ ≤ (t.card : ℝ≥0∞) * (sg.card : ℝ≥0∞) * volCube := mul_le_mul_left hs_le volCube
      _ = (sg.card : ℝ≥0∞) * ((t.card : ℝ≥0∞) * volCube) := by ac_rfl
      _ ≤ _ := mul_le_mul_right (by simpa [hR2, volCube] using ht_vol) _
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
    simpa [volBall, show (Real.toNNReal (ZLattice.covolume (cubeLattice d L hLpos) volume) : ℝ≥0∞)
        = volCube by rw [show Real.toNNReal (ZLattice.covolume (cubeLattice d L hLpos) volume) =
          volCube.toNNReal by simpa [volCube] using
        PeriodicConstantApprox.toNNReal_covolume_cubeLattice (d := d) L hLpos,
        ENNReal.coe_toNNReal hvolCube_ne_top]] using hPdens
  refine ⟨P, hPsep, (lt_tsub_iff_right.mpr hsg_density).trans_le (tsub_le_iff_right.2 ?_)⟩
  have hsplit : (sg.card : ℝ≥0∞) * volBall =
      (F.card : ℝ≥0∞) * volBall + (sb.card : ℝ≥0∞) * volBall := by
    simp [show (sg.card : ℝ≥0∞) = (F.card : ℝ≥0∞) + (sb.card : ℝ≥0∞) by
      exact_mod_cast (Finset.card_filter_add_card_filter_not (s := sg)
        (p := fun x => x ∈ innerSet)).symm, add_mul]
  simpa [hPdens', div_eq_mul_inv, mul_add, add_mul, mul_assoc, hcubeShell, shellVol] using
    ENNReal.div_le_div_right (hsplit ▸ add_le_add_right hsb_vol _ :
      (sg.card : ℝ≥0∞) * volBall ≤ (F.card : ℝ≥0∞) * volBall + shellVol) volCube

end SpherePacking

/-- The periodic sphere packing constant equals the sphere packing constant; packages the
boundary control argument developed in this file. -/
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
