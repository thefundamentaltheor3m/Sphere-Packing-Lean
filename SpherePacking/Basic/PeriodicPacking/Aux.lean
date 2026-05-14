/-
Copyright (c) 2024 Gareth Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gareth Ma
-/
module
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Order.Filter.Defs
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Instances.ENat
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Order.T5
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Periodic packings: definitions, auxiliary finiteness, and disjointness lemmas
(blueprint Theorem 2.2)
-/

/-! ## Density of Sphere Packings: definitions and basic notions for periodic packings. -/

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

attribute [instance] PeriodicSpherePacking.lattice_discrete PeriodicSpherePacking.lattice_isZLattice

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
public theorem PeriodicSpherePacking.addAction_vadd (S : PeriodicSpherePacking d) {x : S.lattice}
    {y : S.centers} : x +ᵥ y = ⟨x.val + y.val, S.lattice_action x.prop y.prop⟩ := rfl

/-- Balls of radius `S.separation / 2` around the centers of a packing. -/
@[expose, reducible] public def SpherePacking.balls (S : SpherePacking d) :
    Set (EuclideanSpace ℝ (Fin d)) := ⋃ x : S.centers, ball (x.val) (S.separation / 2)

/-- Volume of packing balls inside `ball 0 R`, normalized by `volume (ball 0 R)`. -/
@[expose] public noncomputable def SpherePacking.finiteDensity (S : SpherePacking d) (R : ℝ) :
    ℝ≥0∞ := volume (S.balls ∩ ball 0 R) / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)

/-- The (upper) density: `limsup` of `finiteDensity` as `R → ∞`. -/
@[expose] public noncomputable def SpherePacking.density (S : SpherePacking d) : ℝ≥0∞ :=
  limsup S.finiteDensity atTop

public theorem PeriodicSpherePacking.basis_Z_span (S : PeriodicSpherePacking d) {ι : Type*}
    (b : Basis ι ℤ S.lattice) : Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) = S.lattice :=
  Basis.ofZLatticeBasis_span ℝ S.lattice b

public theorem PeriodicSpherePacking.mem_basis_Z_span (S : PeriodicSpherePacking d) {ι : Type*}
    (b : Basis ι ℤ S.lattice) (v) :
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
    obtain ⟨x', hx', rfl⟩ := Set.mem_smul_set.mp hx; obtain ⟨y', hy', rfl⟩ := Set.mem_smul_set.mp hy
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
        Submodule.smul_mem_pointwise_smul _ c⁻¹ _ (Submodule.smul_mem (c • p) c (h _ <| by
          rw [Submodule.coe_pointwise_smul]; exact Set.smul_set_mono hp))
    · simpa [smul_smul, mul_inv_cancel₀ hc.ne.symm] using
        Submodule.smul_mem_pointwise_smul _ c _ (Submodule.smul_mem (c⁻¹ • p) c⁻¹ (h _ <| by
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
@[expose] public def _root_.SpherePackingConstant (d : ℕ) : ℝ≥0∞ := ⨆ S : SpherePacking d, S.density

@[simp]
public lemma scale_finiteDensity {d : ℕ} (S : SpherePacking d) {c : ℝ} (hc : 0 < c) (R : ℝ) :
    (S.scale hc).finiteDensity (c * R) = S.finiteDensity R := by
  rw [finiteDensity, scale_balls, show ball (0 : EuclideanSpace ℝ (Fin d)) (c * R) = c • ball 0 R by
      simpa [Real.norm_eq_abs, abs_of_pos hc, mul_assoc] using
        (smul_ball hc.ne.symm (0 : EuclideanSpace ℝ (Fin d)) R).symm, ← Set.smul_set_inter₀ hc.ne.symm,
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

theorem SpherePacking.volume_iUnion_balls_eq_tsum (R : ℝ) {r' : ℝ} (hr' : r' ≤ S.separation / 2) :
    volume (⋃ x : ↑(S.centers ∩ ball 0 R), ball (x : EuclideanSpace ℝ (Fin d)) r')
      = ∑' x : ↑(S.centers ∩ ball 0 R), volume (ball (x : EuclideanSpace ℝ (Fin d)) r') :=
  have _ : Countable ↑(S.centers ∩ ball 0 R) := Set.Countable.mono Set.inter_subset_left
    (countable_of_Lindelof_of_discrete (X := S.centers))
  measure_iUnion (fun ⟨x, hx⟩ ⟨y, hy⟩ h ↦ ball_disjoint_ball <| by
    linarith [S.centers_dist' x y hx.1 hy.1 (by simpa using h)]) fun _ ↦ measurableSet_ball

theorem SpherePacking.inter_ball_encard_le (R : ℝ) :
    (S.centers ∩ ball 0 R).encard ≤ volume (S.balls ∩ ball 0 (R + S.separation / 2))
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) := by
  have h : volume _ ≤ volume _ := volume.mono <|
    show ⋃ x ∈ S.centers ∩ ball 0 R, ball x (S.separation / 2) ⊆
        (⋃ x ∈ S.centers, ball x (S.separation / 2)) ∩ ball 0 (R + S.separation / 2) from
      fun x hx => by
        simp only [Set.mem_inter_iff, Set.mem_iUnion, mem_ball, exists_prop, dist_zero_right]
          at hx ⊢
        obtain ⟨y, hy₁, hy₂⟩ := hx
        exact ⟨⟨y, hy₁.1, hy₂⟩, (norm_le_norm_add_norm_sub' x y).trans_lt (by gcongr <;> tauto)⟩
  simp_rw [Set.biUnion_eq_iUnion, S.volume_iUnion_balls_eq_tsum R le_rfl,
    Measure.addHaar_ball_center, ENNReal.tsum_set_const] at h
  rwa [← ENNReal.le_div_iff_mul_le
    (.inl (Metric.measure_ball_pos volume _ (by linarith [S.separation_pos])).ne.symm)
    (.inl MeasureTheory.measure_ball_lt_top.ne)] at h

theorem SpherePacking.inter_ball_encard_ge (R : ℝ) :
    (S.centers ∩ ball 0 R).encard ≥ volume (S.balls ∩ ball 0 (R - S.separation / 2))
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) := by
  have h : volume _ ≤ volume _ := volume.mono <|
    show (⋃ x ∈ S.centers, ball x (S.separation / 2)) ∩ ball 0 (R - S.separation / 2) ⊆
        ⋃ x ∈ S.centers ∩ ball 0 R, ball x (S.separation / 2) from fun x hx => by
      simp only [Set.mem_inter_iff, Set.mem_iUnion, mem_ball, exists_prop, dist_zero_right]
        at hx ⊢
      obtain ⟨⟨y, hy₁, hy₂⟩, hx⟩ := hx
      refine ⟨y, ⟨hy₁, ?_⟩, hy₂⟩
      rw [← sub_add_cancel R (S.separation / 2)]
      exact (norm_le_norm_add_norm_sub x y).trans_lt <| add_lt_add hx
        (by simpa [dist_eq_norm, norm_sub_rev] using hy₂)
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
    (.inl MeasureTheory.measure_ball_lt_top.ne)).1
    (by simpa [sub_add_cancel] using S.inter_ball_encard_le (R - S.separation / 2))) _

public theorem SpherePacking.finiteDensity_le (_hd : 0 < d) (R : ℝ) :
    S.finiteDensity R ≤ (S.centers ∩ ball 0 (R + S.separation / 2)).encard
      * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
  rw [finiteDensity, balls]
  exact ENNReal.div_le_div_right ((ENNReal.div_le_iff_le_mul
    (.inl (Metric.measure_ball_pos volume _ (by linarith [S.separation_pos])).ne.symm)
    (.inl MeasureTheory.measure_ball_lt_top.ne)).1
    (by simpa [add_sub_cancel_right] using S.inter_ball_encard_ge (R + S.separation / 2))) _

end BasicResults

/-!
The following ENat/Set.encard helpers are taken from mathlib4 PR #23503 by Peter Nelson,
and should be removed once that PR is merged.
-/

namespace ENat

open Function Set

/-- The infinite sum of a constant `c : ENat` over a type `α` is `ENat.card α * c`. -/
public theorem tsum_const {α : Type*} (c : ENat) :
    ∑' (_ : α), c = ENat.card α * c := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  obtain hfin | hinf := fintypeOrInfinite α
  · simp [tsum_fintype]
  simp only [card_eq_top_of_infinite]
  refine HasSum.tsum_eq (by
    change Filter.Tendsto _ _ _
    simp only [Finset.sum_const, nsmul_eq_mul, ne_eq, hc, not_false_eq_true, top_mul]
    refine (tendsto_nhds_top_iff_natCast_lt.2 fun n => ?_)
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α (n + 1)
    filter_upwards [Filter.eventually_ge_atTop s] with t ht
    exact lt_of_lt_of_le (lt_of_lt_of_le
      (by simp only [Nat.cast_lt, hs, Nat.lt_succ_self n] : (n : ℕ∞) < s.card)
      (by simpa using Finset.card_le_card ht))
      (le_mul_of_one_le_right' (ENat.one_le_iff_ne_zero.2 hc)))

/-- The infinite sum of a constant `c : ENat` over a set `s` is `s.encard * c`. -/
public theorem tsum_set_const {α : Type*} (s : Set α) (c : ENat) :
    ∑' (_ : s), c = s.encard * c := by rw [tsum_const, Set.encard]

variable {α β : Type*} {f : α → ℕ∞}

private theorem summable : Summable f :=
  HasSum.summable (a := ⨆ s : Finset α, ∑ a ∈ s, f a)
    (tendsto_atTop_iSup fun _ _ ↦ Finset.sum_le_sum_of_subset)

private theorem tsum_comp_le_tsum_of_injective {φ : α → β} (hφ : Injective φ) (g : β → ℕ∞) :
    ∑' x, g (φ x) ≤ ∑' y, g y :=
  (summable (f := fun x => g (φ x))).tsum_le_tsum_of_inj φ hφ (fun _ _ ↦ zero_le _)
    (fun _ ↦ le_rfl) (summable (f := g))

private theorem tsum_subtype_iUnion_eq_tsum {ι : Type*} (f : α → ℕ∞) (t : ι → Set α)
    (ht : Pairwise (Disjoint on t)) :
    ∑' x : ⋃ i, t i, f x = ∑' i, ∑' x : t i, f x :=
  have hbij := sigmaToiUnion_bijective t (fun _ _ hij ↦ ht hij)
  calc ∑' x : ⋃ i, t i, f x = ∑' x : Σ i, t i, f x.2 :=
    ((tsum_comp_le_tsum_of_injective hbij.injective fun x : ⋃ i, t i => f x).antisymm <|
      calc ∑' y : ⋃ i, t i, f y
            = ∑' y : ⋃ i, t i, f (sigmaToiUnion t (surjInv hbij.surjective y)) := by
              simp [surjInv_eq hbij.surjective]
        _ ≤ _ := tsum_comp_le_tsum_of_injective (injective_surjInv hbij.surjective) _).symm
    _ = _ := Summable.tsum_sigma' (fun _ ↦ summable) summable

end ENat

/-- `encard` is additive on pairwise disjoint unions. -/
public theorem Set.encard_iUnion_of_pairwiseDisjoint {ι α : Type*} {s : ι → Set α}
    (hs : Set.PairwiseDisjoint Set.univ s) : (⋃ i, s i).encard = ∑' i, (s i).encard := by
  simpa [ENat.tsum_set_const, mul_one] using
    (ENat.tsum_subtype_iUnion_eq_tsum (f := fun _ : α => (1 : ℕ∞)) (t := s) (by
      simpa [Set.PairwiseDisjoint, Set.pairwise_univ] using hs))

open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module

section ZLattice_helpers

variable {E ι K : Type*} [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [NormedAddCommGroup E] [NormedSpace K E] (b : Module.Basis ι K E) [FloorRing K] [Fintype ι]

/-- A point is in the fundamental domain iff its `floor` vector is zero. -/
public theorem ZSpan.floor_eq_zero (v : E) : v ∈ fundamentalDomain b ↔ floor b v = 0 := by
  simp_rw [mem_fundamentalDomain, ← Int.floor_eq_zero_iff]
  constructor <;> intro h
  · simp [floor, h]
  · intro i
    exact_mod_cast (by simpa [h] using (repr_floor_apply b v i).symm)

end ZLattice_helpers

section BasisIndexEquiv

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

namespace ZLattice

/--
Reindex the chosen `ℤ`-basis of a full-rank lattice in `ℝ^d` by `Fin d`.

This is useful for building `Basis (Fin d) ℤ Λ` via `.reindex` without carrying around an
abstract basis-index type.
-/
public noncomputable def basis_index_equiv (Λ : Submodule ℤ E)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    (Module.Free.ChooseBasisIndex ℤ Λ) ≃ (Fin d) := by
  refine Fintype.equivFinOfCardEq ?_
  rw [← Module.finrank_eq_card_chooseBasisIndex (R := ℤ) (M := Λ),
    ZLattice.rank (K := ℝ) (L := Λ),
    finrank_euclideanSpace, Fintype.card_fin]

end ZLattice

end BasisIndexEquiv

section aux_lemmas

variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))

private theorem finite_of_bounded_iUnion_of_volume_lower_bound
    {ι τ : Type*} {s : Set ι} {f : ι → Set (EuclideanSpace ℝ τ)} {c : ℝ≥0∞} (hc : 0 < c)
    [Fintype τ] [NoAtoms (volume : Measure (EuclideanSpace ℝ τ))]
    (h_measurable : ∀ x ∈ s, MeasurableSet (f x))
    (h_bounded : IsBounded (⋃ x ∈ s, f x))
    (h_volume : ∀ x ∈ s, c ≤ volume (f x))
    (h_disjoint : s.PairwiseDisjoint f) :
    s.Finite := by
  classical
  let As : ι → Set (EuclideanSpace ℝ τ) := fun i ↦ if i ∈ s then f i else ∅
  have As_disj : Pairwise fun i j ↦ Disjoint (As i) (As j) := fun i j hij ↦ by
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
    · simpa [As, hi, hj] using h_disjoint hi hj hij
    all_goals simp [As, hi, hj]
  obtain ⟨L, hL⟩ := (h_bounded.subset (Set.iUnion_subset fun i x hi ↦ by
    by_cases hs : i ∈ s <;> [exact Set.mem_iUnion₂.2 ⟨i, hs, by simpa [As, hs] using hi⟩;
      simp [As, hs] at hi] : (⋃ i, As i) ⊆ _)).subset_ball 0
  exact (Measure.finite_const_le_meas_of_disjoint_iUnion (μ := volume) hc
    (fun i ↦ by by_cases hi : i ∈ s <;> [simpa [As, hi] using h_measurable i hi; simp [As, hi]])
    As_disj (ne_top_of_le_ne_top measure_ball_lt_top.ne (volume.mono hL))).subset fun i hi ↦ by
    simpa [As, hi] using h_volume i hi

/-- A periodic packing has only finitely many centers in a bounded set. -/
public lemma finite_centers_inter_of_isBounded (hD_isBounded : IsBounded D) (hd : 0 < d) :
    Finite ↑(S.centers ∩ D) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  obtain ⟨L, hL⟩ := isBounded_iff_forall_norm_le.1 hD_isBounded
  have hbounded : IsBounded (⋃ x ∈ S.centers ∩ D, ball x (S.separation / 2)) :=
    isBounded_iff_forall_norm_le.2 ⟨L + S.separation / 2, fun x hx ↦
      let ⟨y, hy, hx⟩ := Set.mem_iUnion₂.1 hx
      (norm_le_norm_add_norm_sub' x y).trans (add_le_add (hL y hy.2)
        (by simpa [mem_ball, dist_eq_norm] using hx.le))⟩
  refine Set.finite_coe_iff.2 <| finite_of_bounded_iUnion_of_volume_lower_bound
      (c := volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)))
      (by simpa using Metric.measure_ball_pos volume _ (by linarith [S.separation_pos]))
      (fun _ _ => measurableSet_ball) hbounded
      (fun _ _ => by simp [Measure.addHaar_ball_center])
      fun _ hx _ hy hxy ↦ ball_disjoint_ball <| by
        simpa [add_halves] using S.centers_dist' _ _ hx.1 hy.1 hxy

end aux_lemmas

section Pointwise

open scoped Pointwise

variable {d : ℕ}

/-- If `D` meets each lattice orbit at exactly one point, distinct translates of `D` are disjoint. -/
public lemma disjoint_vadd_of_unique_covers {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD_unique_covers : ∀ x, ∃! g : Λ, g +ᵥ x ∈ D)
    {g h : Λ} (hgh : g ≠ h) : Disjoint (g +ᵥ D) (h +ᵥ D) :=
  Set.disjoint_left.2 fun x hxg hxh ↦ hgh <| neg_injective <| (hD_unique_covers x).unique
    (by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hxg)
    (by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hxh)

variable (S : PeriodicSpherePacking d)

noncomputable def PeriodicSpherePacking.addActionOrbitRelEquiv
    (D : Set (EuclideanSpace ℝ (Fin d))) (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
    Quotient S.addAction.orbitRel ≃ ↑(S.centers ∩ D) where
  toFun := Quotient.lift (fun s ↦ ⟨(Classical.choose (hD_unique_covers s.val)).val + s.val,
      S.lattice_action (Classical.choose (hD_unique_covers s.val)).prop s.prop,
      (Classical.choose_spec (hD_unique_covers s.val)).1⟩) <| by
    rintro ⟨u, hu⟩ ⟨v, hv⟩ ⟨⟨y, hy⟩, hy'⟩
    obtain rfl : y + v = u := Subtype.ext_iff.mp hy'
    have hv' := (Classical.choose_spec (hD_unique_covers v)).2
    simp only [Subtype.forall] at hv'
    simp_rw [Subtype.forall, S.lattice.mk_vadd, vadd_eq_add, Subtype.mk.injEq, ← add_assoc]
    exact congrArg (· + _) <| Subtype.ext_iff.mp <| hv' _ (add_mem (SetLike.coe_mem _) hy) <| by
      simpa [Subtype.forall, S.lattice.mk_vadd, add_assoc] using
        (Classical.choose_spec (hD_unique_covers (y + v))).1
  invFun := fun ⟨x, hx⟩ ↦ ⟦⟨x, hx.1⟩⟧
  left_inv := Quotient.ind fun _ ↦ Quotient.eq.2 <| by
    simp [AddAction.orbitRel_apply, AddAction.orbit, Set.mem_range, addAction_vadd]
  right_inv := fun ⟨x, hx⟩ ↦ by
    simp_rw [Quotient.lift_mk, Subtype.mk.injEq, add_eq_right]
    obtain ⟨g, _, hg'⟩ := hD_unique_covers x
    exact_mod_cast (hg' _ (Classical.choose_spec (hD_unique_covers x)).1).trans
      (hg' 0 (by simpa using hx.2)).symm

public noncomputable def PeriodicSpherePacking.addActionOrbitRelEquiv'
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) :
    Quotient S.addAction.orbitRel ≃ ↑(S.centers ∩ (fundamentalDomain (b.ofZLatticeBasis ℝ _))) :=
  S.addActionOrbitRelEquiv _ fun x ↦
    let ⟨v, hv, hv'⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
    ⟨⟨v.val, (S.mem_basis_Z_span b _).1 v.prop⟩, by simpa using hv,
      fun s hs => by rw [← hv' ⟨s, (S.mem_basis_Z_span b _).2 s.prop⟩ hs]⟩

public noncomputable def PeriodicSpherePacking.addActionOrbitRelEquiv''
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) (v : EuclideanSpace ℝ (Fin d)) :
    Quotient S.addAction.orbitRel ≃
      ↑(S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))) := by
  letI : Fintype ι := Fintype.ofFinite ι
  set b' := b.ofZLatticeBasis ℝ _
  have hact (w u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ S.centers) :
      u - floor b' w ∈ S.centers := by
    rw [sub_eq_neg_add]; exact S.lattice_action (Submodule.neg_mem _ <|
      (mem_basis_Z_span ..).mp <| Submodule.coe_mem _) hu
  refine (S.addActionOrbitRelEquiv' b).trans {
    toFun := fun ⟨u, ⟨hu_centers, _⟩⟩ ↦
      ⟨u - floor b' (u - v), hact _ u hu_centers, Set.mem_vadd_set.2
        ⟨fract b' (u - v), fract_mem_fundamentalDomain _ _, by rw [fract, vadd_eq_add]; abel⟩⟩
    invFun := fun ⟨u, ⟨hu_centers, _⟩⟩ ↦
      ⟨fract b' u, by rw [fract]; exact hact _ u hu_centers, fract_mem_fundamentalDomain _ _⟩
    left_inv := fun ⟨u, ⟨_, hu_fd⟩⟩ ↦ by
      simpa [sub_eq_add_neg, fract_add_ZSpan _ _ (neg_mem (Submodule.coe_mem _))]
        using fract_eq_self.mpr hu_fd
    right_inv := fun ⟨u, ⟨_, hu_fd⟩⟩ ↦ by
      rw [Subtype.mk.injEq, ← EmbeddingLike.apply_eq_iff_eq b'.repr, map_sub]
      ext i
      calc _ = b'.repr (fract b' u) i - b'.repr (floor b' (u - floor b' u - v)) i := rfl
        _ = b'.repr u i - ⌊b'.repr u i⌋ - (⌊b'.repr (u - v) i⌋ - ⌊b'.repr u i⌋) := by
          rw [show u - floor b' u - v = u - v - floor b' u by abel]; simp
        _ = b'.repr u i := by
          rw [show b'.repr u i - ⌊b'.repr u i⌋ - (⌊b'.repr (u - v) i⌋ - ⌊b'.repr u i⌋) =
            b'.repr u i - ⌊b'.repr (u - v) i⌋ by abel_nf, sub_eq_self, ← repr_floor_apply,
            (ZSpan.floor_eq_zero ..).mp (by rwa [Set.mem_vadd_set_iff_neg_vadd_mem,
              vadd_eq_add, neg_add_eq_sub] at hu_fd)]
          simp }

public noncomputable instance PeriodicSpherePacking.finiteOrbitRelQuotient :
    Finite (Quotient S.addAction.orbitRel) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Quotient.finite _
  let b : Basis _ ℤ S.lattice := (ZLattice.module_free ℝ S.lattice).chooseBasis
  haveI := finite_centers_inter_of_isBounded S _ (ZSpan.fundamentalDomain_isBounded
    (b.ofZLatticeBasis ℝ _)) hd
  exact .of_equiv _ (S.addActionOrbitRelEquiv' b).symm

public noncomputable instance : Fintype (Quotient S.addAction.orbitRel) := Fintype.ofFinite _

open Finset Set
variable (D : Set (EuclideanSpace ℝ (Fin d)))

@[expose] public noncomputable def PeriodicSpherePacking.numReps : ℕ :=
  Fintype.card (Quotient S.addAction.orbitRel)

public theorem PeriodicSpherePacking.numReps_eq_one (hS : S.centers = S.lattice) :
    S.numReps = 1 :=
  haveI : Subsingleton (Quotient S.addAction.orbitRel) :=
    (AddAction.pretransitive_iff_subsingleton_quotient _ _).mp ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ ↦
      ⟨⟨y - x, by rw [hS] at hx hy; exact sub_mem hy hx⟩, by simp [addAction_vadd]⟩⟩
  Fintype.card_eq_one_iff.2 ⟨⟦(⟨0, by simp [hS]⟩ : S.centers)⟧, (Subsingleton.elim · _)⟩

public theorem PeriodicSpherePacking.card_centers_inter_isFundamentalDomain
    (hD_isBounded : IsBounded D) (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) :
    haveI := @Fintype.ofFinite _ <| finite_centers_inter_of_isBounded S D hD_isBounded hd
    (S.centers ∩ D).toFinset.card = S.numReps :=
  card_eq_of_equiv_fintype (by simpa [numReps] using
    (S.addActionOrbitRelEquiv D hD_unique_covers).symm)

public theorem PeriodicSpherePacking.encard_centers_inter_isFundamentalDomain
    (hD_isBounded : IsBounded D) (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) : (S.centers ∩ D).encard = S.numReps := by
  rw [← S.card_centers_inter_isFundamentalDomain D hD_isBounded hD_unique_covers hd]
  convert Set.encard_eq_coe_toFinset_card _

theorem PeriodicSpherePacking.card_centers_inter_vadd_fundamentalDomain (hd : 0 < d)
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) (v : EuclideanSpace ℝ (Fin d)) :
    haveI := @Fintype.ofFinite _ <| finite_centers_inter_of_isBounded S _
      ((ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ _)).vadd v) hd
    (S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))).toFinset.card = S.numReps :=
  card_eq_of_equiv_fintype (by simpa [numReps] using (S.addActionOrbitRelEquiv'' b v).symm)

theorem PeriodicSpherePacking.encard_centers_inter_vadd_fundamentalDomain (hd : 0 < d)
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) (v : EuclideanSpace ℝ (Fin d)) :
    (S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))).encard = S.numReps := by
  rw [← S.card_centers_inter_vadd_fundamentalDomain hd b]; convert Set.encard_eq_coe_toFinset_card _

public noncomputable instance PeriodicSpherePacking.instFintypeNumReps'
    (S : PeriodicSpherePacking d) (hd : 0 < d)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D) :
    Fintype ↑(S.centers ∩ D) := @Fintype.ofFinite _ <|
  finite_centers_inter_of_isBounded S D hD_isBounded hd

@[expose] public noncomputable def PeriodicSpherePacking.numReps'
    (S : PeriodicSpherePacking d) (hd : 0 < d)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D) : ℕ :=
  haveI := S.instFintypeNumReps' hd hD_isBounded; Fintype.card ↑(S.centers ∩ D)

public theorem PeriodicSpherePacking.numReps_eq_numReps' (S : PeriodicSpherePacking d) (hd : 0 < d)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
    S.numReps = S.numReps' hd hD_isBounded := by
  simpa [PeriodicSpherePacking.numReps', Set.toFinset_card] using
    (S.card_centers_inter_isFundamentalDomain (D := D) hD_isBounded hD_unique_covers hd).symm

private theorem disjoint_vadd_fundamentalDomain
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ S.lattice) (hy : y ∈ S.lattice) (hxy : x ≠ y) :
    Disjoint (x +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))
      (y +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  simpa using disjoint_vadd_of_unique_covers
    (Λ := Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ _)))
    (D := fundamentalDomain (b.ofZLatticeBasis ℝ _))
    (fun u ↦ by simpa using exist_unique_vadd_mem_fundamentalDomain _ u)
    fun h ↦ hxy <| congrArg Subtype.val
      (h : (⟨x, by simpa [S.basis_Z_span] using hx⟩ :
          Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ _))) =
        ⟨y, by simpa [S.basis_Z_span] using hy⟩)

private lemma pairwiseDisjoint_centers_inter_vadd
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {C : Set (EuclideanSpace ℝ (Fin d))} :
    Set.univ.PairwiseDisjoint fun i : (↑S.lattice ∩ C : Set _) ↦
      S.centers ∩ (i.val +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _)) := fun ⟨_, hx⟩ _ ⟨_, hy⟩ _
  hxy ↦ Set.disjoint_left.2 fun _ hux huy ↦ Set.disjoint_left.1
    (disjoint_vadd_fundamentalDomain S b hx.1 hy.1 fun h ↦ hxy (Subtype.ext h)) hux.right huy.right

/-- Theorem 2.3, lower bound. -/
public theorem PeriodicSpherePacking.aux_ge
    (hd : 0 < d) {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) :
    (↑S.centers ∩ ball 0 R).encard ≥
      S.numReps • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R - L)).encard := by
  have henc := Set.encard_mono <| Set.inter_subset_inter_right S.centers
    (show ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R - L),
        x +ᵥ (fundamentalDomain (b.ofZLatticeBasis ℝ _) : Set (EuclideanSpace ℝ (Fin d)))
          ⊆ ball 0 R from fun x hx => by
      obtain ⟨y, ⟨_, hy⟩, z, hz, rfl⟩ := by simpa using hx
      simp only [mem_ball, dist_zero_right, vadd_eq_add] at hy ⊢
      linarith [norm_add_le y z, hL z hz])
  simp_rw [Set.biUnion_eq_iUnion, Set.inter_iUnion,
    Set.encard_iUnion_of_pairwiseDisjoint (pairwiseDisjoint_centers_inter_vadd S b),
    S.encard_centers_inter_vadd_fundamentalDomain hd] at henc
  simpa [nsmul_eq_mul, ENat.tsum_set_const, mul_comm] using henc.ge

/-- Theorem 2.3, upper bound. -/
public theorem PeriodicSpherePacking.aux_le
    (hd : 0 < d) {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) :
    (↑S.centers ∩ ball 0 R).encard
      ≤ S.numReps • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + L)).encard := by
  letI : Fintype ι := Fintype.ofFinite ι
  have henc := Set.encard_mono <| Set.inter_subset_inter_right S.centers
    (fun x hx ↦ Set.mem_iUnion₂.2 ⟨floor (b.ofZLatticeBasis ℝ _) x,
      ⟨(S.mem_basis_Z_span b _).mp (Submodule.coe_mem _),
        mem_ball_zero_iff.2 <| ((show ‖floor (b.ofZLatticeBasis ℝ _) x‖ =
              ‖x - fract (b.ofZLatticeBasis ℝ _) x‖ by simp [fract]).le.trans
            (norm_sub_le _ _)).trans_lt (add_lt_add_of_lt_of_le (mem_ball_zero_iff.1 hx)
              (hL _ (fract_mem_fundamentalDomain _ _)))⟩,
      by simpa [Set.mem_vadd_set_iff_neg_vadd_mem, neg_add_eq_sub] using
        fract_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x⟩ :
      ball 0 R ⊆ ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + L),
        x +ᵥ (fundamentalDomain (b.ofZLatticeBasis ℝ _) : Set (EuclideanSpace ℝ (Fin d))))
  simp_rw [Set.biUnion_eq_iUnion, Set.inter_iUnion,
    Set.encard_iUnion_of_pairwiseDisjoint (pairwiseDisjoint_centers_inter_vadd S b),
    S.encard_centers_inter_vadd_fundamentalDomain hd] at henc
  simpa [nsmul_eq_mul, ENat.tsum_set_const, mul_comm] using henc

end Pointwise

/-! ## Theorem 2.2 (blueprint) and density formula -/

section DensityFormula

/-- Cancel a common numerator in a ratio of `ENNReal` divisions.
If `a` is nonzero and finite, and `c` is finite, then `(a / b) / (a / c) = c / b`. -/
private theorem ENNReal.div_div_div_cancel_left {a b c : ENNReal} (ha : a ≠ 0) (ha' : a ≠ ⊤)
    (hc : c ≠ ⊤) : (a / b) / (a / c) = c / b := by
  by_cases hb : b = 0
  · simp [ha, hb, div_zero, top_div, div_eq_top, hc, ha']
    split_ifs with hct <;> simp [hct, eq_comm, div_eq_top]
  · rw [← ENNReal.toReal_eq_toReal_iff', ENNReal.toReal_div, ENNReal.toReal_div,
      ENNReal.toReal_div, ENNReal.toReal_div]
    · rw [div_div_div_cancel_left']
      rw [ne_eq, ENNReal.toReal_eq_zero_iff, not_or]; tauto
    · simp [*, ne_eq, ENNReal.div_eq_top]
    · simp [*, ne_eq, ENNReal.div_eq_top]

section theorem_2_2

open scoped Pointwise
variable {d : ℕ} (S : PeriodicSpherePacking d) {ι : Type*} [Finite ι]
  (D : Set (EuclideanSpace ℝ (Fin d))) {L : ℝ} (R : ℝ)

theorem hD_isAddFundamentalDomain (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)
    (hD_measurable : MeasurableSet D) : IsAddFundamentalDomain S.lattice D :=
  .mk' (μ := volume) hD_measurable.nullMeasurableSet hD_unique_covers

/-- An add-left-invariant measure is invariant under translations by a submodule. -/
public instance (E : Type*) [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E] [Module ℤ E]
    [Module ℝ E] (μ : Measure E) [μ.IsAddLeftInvariant] [IsScalarTower ℤ ℝ E] (s : Submodule ℤ E) :
    VAddInvariantMeasure s E μ :=
  ⟨fun _ _ _ => by simp [Submodule.vadd_def, measure_preimage_add]⟩

private lemma measure_biUnion_lattice_inter_ball_vadd
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D) :
    volume (⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R, (x +ᵥ D)) =
      (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard * volume D := by
  have : Countable ↑(↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
    Set.Countable.mono Set.inter_subset_left (inferInstance : Countable ↑S.lattice)
  rw [Set.biUnion_eq_iUnion, measure_iUnion]
  · rw [tsum_congr fun i ↦ measure_vadd .., ENNReal.tsum_set_const]
  · exact fun i j hij => by
      simpa using disjoint_vadd_of_unique_covers (d := d) (Λ := S.lattice) (D := D)
        hD_unique_covers (fun h => hij <|
          Subtype.ext <| congrArg (fun u : S.lattice => (u : EuclideanSpace ℝ (Fin d))) h :
          (⟨i.1, i.2.1⟩ : S.lattice) ≠ ⟨j.1, j.2.1⟩)
  · exact fun i => hD_measurable.const_vadd i.1

variable (b : Basis ι ℤ S.lattice)

private lemma fundamentalDomain_unique_covers (x : EuclideanSpace ℝ (Fin d)) :
    ∃! g : S.lattice, g +ᵥ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _) :=
  let ⟨⟨v, hv⟩, hvD, hvuniq⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
  ⟨⟨v, by simpa [S.basis_Z_span] using hv⟩, hvD, fun ⟨y, hy⟩ hyD => Subtype.ext <| by
    simpa using congrArg Subtype.val (hvuniq ⟨y, by simpa [S.basis_Z_span] using hy⟩ hyD)⟩

/-- Theorem 2.2 lower bound, in terms of fundamental domain of Z-lattice. -/
public theorem PeriodicSpherePacking.aux2_ge'
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≥ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - L))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  set D : Set (EuclideanSpace ℝ (Fin d)) := fundamentalDomain (b.ofZLatticeBasis ℝ _)
  have hD_unique_covers := fundamentalDomain_unique_covers S b
  have hD_measurable : MeasurableSet D := fundamentalDomain_measurableSet _
  rw [ge_iff_le, ENNReal.div_le_iff
    ((hD_isAddFundamentalDomain S D ‹_› ‹_›).measure_ne_zero (NeZero.ne volume))
    (Bornology.IsBounded.measure_lt_top (isBounded_iff_forall_norm_le.mpr ⟨L, hL⟩)).ne,
    ← measure_biUnion_lattice_inter_ball_vadd S D R hD_unique_covers hD_measurable]
  refine volume.mono fun x hx => ?_
  obtain ⟨g, hg, -⟩ := hD_unique_covers x
  simp_rw [Set.mem_iUnion, exists_prop, Set.mem_inter_iff]
  refine ⟨-g.val, ⟨⟨by simp, ?_⟩, Set.mem_vadd_set_iff_neg_vadd_mem.2 (by simpa using hg)⟩⟩
  simpa [mem_ball_zero_iff, norm_neg] using lt_of_le_of_lt
    (by simpa [sub_eq_add_neg, add_assoc] using norm_sub_le (a := g.val + x) (b := x) :
      ‖g.val‖ ≤ ‖g.val + x‖ + ‖x‖) (by
    linarith [hL _ (by simpa using hg : g.val + x ∈ D), mem_ball_zero_iff.mp hx])

/-- Theorem 2.2 upper bound, in terms of fundamental domain of Z-lattice. -/
public theorem PeriodicSpherePacking.aux2_le'
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  set D : Set (EuclideanSpace ℝ (Fin d)) := fundamentalDomain (b.ofZLatticeBasis ℝ _)
  have hD_unique_covers := fundamentalDomain_unique_covers S b
  have hD_measurable : MeasurableSet D := fundamentalDomain_measurableSet _
  rw [ENNReal.le_div_iff_mul_le (.inl <| (hD_isAddFundamentalDomain S D ‹_› ‹_›).measure_ne_zero
    (NeZero.ne volume)) (.inl <| (Bornology.IsBounded.measure_lt_top
      (isBounded_iff_forall_norm_le.mpr ⟨L, hL⟩)).ne),
    ← measure_biUnion_lattice_inter_ball_vadd S D R hD_unique_covers hD_measurable]
  refine volume.mono fun x hx => ?_
  simp_rw [Set.mem_iUnion, exists_prop, Set.mem_inter_iff, mem_ball_zero_iff] at hx ⊢
  obtain ⟨i, ⟨-, hi_ball⟩, hi_mem⟩ := hx
  exact lt_of_le_of_lt ((show ‖x‖ = ‖i + (-i + x)‖ by congr; abel).le.trans (norm_add_le _ _))
    (add_lt_add_of_lt_of_le hi_ball (hL _ (Set.mem_vadd_set_iff_neg_vadd_mem.mp hi_mem)))

section finiteDensity_limit

variable {d : ℕ} {S : PeriodicSpherePacking d}
  {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)

/-- Upper bound for `S.finiteDensity R` in terms of a fundamental domain. -/
public theorem aux_big_le
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    S.finiteDensity R ≤
      S.numReps
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := calc
  _ ≤ (S.centers ∩ ball 0 (R + S.separation / 2)).encard
      * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
    S.finiteDensity_le hd R
  _ ≤ S.numReps
        • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L)).encard
          * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
            / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    gcongr; simpa using ENat.toENNReal_le.mpr (S.aux_le hd b hL _)
  _ ≤ S.numReps
        * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L + L))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)))
            * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    rw [nsmul_eq_mul]; gcongr; exact S.aux2_le' _ b hL hd
  _ = S.numReps
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := by
    rw [← mul_div_assoc, ← mul_div_assoc, mul_two, ← add_assoc, ← ENNReal.mul_div_right_comm,
      ← ENNReal.mul_div_right_comm, mul_assoc, mul_assoc, mul_comm (volume _) (volume _)]

/-- Lower bound for `S.finiteDensity R` in terms of a fundamental domain. -/
public theorem aux_big_ge
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    S.finiteDensity R ≥
      S.numReps
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - S.separation / 2 - L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := calc
  _ ≥ (S.centers ∩ ball 0 (R - S.separation / 2)).encard
      * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
    S.finiteDensity_ge hd R
  _ ≥ S.numReps
        • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R - S.separation / 2 - L)).encard
          * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
            / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    gcongr; simpa using ENat.toENNReal_le.mpr (S.aux_ge hd b hL _)
  _ ≥ S.numReps
        * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - S.separation / 2 - L - L))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)))
            * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    rw [nsmul_eq_mul]; gcongr; exact S.aux2_ge' _ b hL hd
  _ = S.numReps
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - S.separation / 2 - L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := by
    rw [← mul_div_assoc, ← mul_div_assoc, mul_two, ← sub_sub, ← ENNReal.mul_div_right_comm,
      ← ENNReal.mul_div_right_comm, mul_assoc, mul_assoc, mul_comm (volume _) (volume _)]

open Filter Topology

section VolumeBallRatio

open ENNReal

/-- As `R → ∞`, `volume (ball 0 R) / volume (ball 0 (R + C))` → `1` for `C ≥ 0`. -/
public theorem volume_ball_ratio_tendsto_nhds_one {C : ℝ} (hd : 0 < d) (hC : 0 ≤ C) :
    Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))) atTop (𝓝 1) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rcases le_iff_eq_or_lt.mp hC with (rfl | hC)
  · exact Tendsto.congr' (f₁ := 1) (eventually_atTop.mpr ⟨1, fun b hb => by
      simp [add_zero, ENNReal.div_self (Metric.measure_ball_pos volume _
        (by linarith)).ne.symm (MeasureTheory.measure_ball_lt_top (μ := volume)).ne]⟩)
      tendsto_const_nhds
  have hfmt (R : ℝ) (hR : 0 ≤ R) : volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
        = ENNReal.ofReal (R ^ d / (R + C) ^ d) := by
    rw [volume_ball, volume_ball, Fintype.card_fin, ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul,
      ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_div_of_pos,
      mul_div_mul_right] <;> positivity
  rw [ENNReal.tendsto_atTop (by decide)]
  intro ε hε
  obtain ⟨k, _, hk₂⟩ : ∃ k : ℝ, k ≥ 0 ∧ ∀ k' ≥ k,
      ENNReal.ofReal ((k' / (k' + 1)) ^ d) ∈ Set.Icc (1 - ε) (1 + ε) := by
    obtain ⟨k, hk⟩ := (ENNReal.tendsto_atTop (by simp)).mp
      (Tendsto.ennrpow_const (d : ℝ) <| tendsto_ofReal <| Tendsto.const_sub 1 <|
        tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_id) :
        Filter.Tendsto (fun k => (ENNReal.ofReal (1 - (k + 1)⁻¹) ^ (d : ℝ))) atTop
          (𝓝 (ENNReal.ofReal (1 - 0) ^ (d : ℝ)))) ε hε
    refine ⟨max 0 k, by simp, fun k' hk' => ?_⟩
    obtain ⟨_, hk₁⟩ := max_le_iff.mp hk'
    have := hk k' hk₁
    have hgoal :
        ENNReal.ofReal ((k' / (k' + 1)) ^ (d : ℝ)) ∈ Set.Icc (1 - ε) (1 + ε) := by
      rwa [sub_zero, ofReal_one, one_rpow, ← one_div, one_sub_div, add_sub_cancel_right,
        ENNReal.ofReal_rpow_of_nonneg] at this <;> positivity
    simpa using hgoal
  refine ⟨k * C, fun n hn => ?_⟩
  rw [hfmt _ ((by positivity : 0 ≤ k * C).trans hn)]
  convert hk₂ (n / C) ((le_div_iff₀ hC).mpr hn)
  rw [div_add_one, div_div_div_cancel_right₀, div_pow] <;> positivity

/-- As `R → ∞`, `volume (ball 0 (R + C)) / volume (ball 0 (R + C'))` → `1` for `C, C' ≥ 0`. -/
public theorem volume_ball_ratio_tendsto_nhds_one'
    {d : ℕ} {C C' : ℝ} (hd : 0 < d) (hC : 0 ≤ C) (hC' : 0 ≤ C') :
      Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) atTop (𝓝 1) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  refine Tendsto.congr' (f₁ := fun R ↦
    volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))
        / (volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
          / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))))
    (eventually_atTop.mpr ⟨1, fun R hR => ENNReal.div_div_div_cancel_left
      (Metric.measure_ball_pos volume _ (lt_of_lt_of_le zero_lt_one hR)).ne.symm
      measure_ball_lt_top.ne measure_ball_lt_top.ne⟩) ?_
  convert ENNReal.Tendsto.div (volume_ball_ratio_tendsto_nhds_one hd hC') ?_
    (volume_ball_ratio_tendsto_nhds_one hd hC) ?_ <;> simp

/-- Shifting the argument by a constant does not change convergence to `atTop`. -/
public theorem Filter.map_add_atTop_eq' {β : Type*} {f : ℝ → β} (C : ℝ) (α : Filter β) :
    Tendsto f atTop α ↔ Tendsto (fun x ↦ f (x + C)) atTop α :=
  have hmap : Filter.map (fun x : ℝ => x + C) atTop = atTop := by
    simpa using Filter.map_add_atTop_eq (α := ℝ) (k := C)
  ⟨fun hf => tendsto_map'_iff.mp (by simpa [hmap]),
    fun hf => by simpa [hmap] using tendsto_map'_iff.mpr hf⟩

/-- Same as `volume_ball_ratio_tendsto_nhds_one'`, without sign assumptions on `C, C'`. -/
public theorem volume_ball_ratio_tendsto_nhds_one'' {d : ℕ} {C C' : ℝ} (hd : 0 < d) :
    Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) atTop (𝓝 1) := by
  refine (Filter.map_add_atTop_eq' (f := fun R ↦
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C)) /
        volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) (max (-C) (-C')) _).mpr ?_
  simpa [add_assoc] using volume_ball_ratio_tendsto_nhds_one' (d := d)
    (C := max (-C) (-C') + C) (C' := max (-C) (-C') + C') hd
    (by linarith [le_max_left (-C) (-C')]) (by linarith [le_max_right (-C) (-C')])

end VolumeBallRatio
end finiteDensity_limit
end theorem_2_2

open scoped Pointwise Topology
open Filter

variable {d : ℕ}

section DensityEqFdDensity

variable
  {S : PeriodicSpherePacking d}
  {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)

/-- Compute the density of a periodic packing using a (bounded) fundamental domain. -/
public theorem PeriodicSpherePacking.density_eq
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    S.density
      = S.numReps * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  refine limsSup_eq_of_le_nhds ?_
  have hmul_one : ∀ a : ENNReal, 𝓝 a = 𝓝 (a * 1) := fun _ => by rw [mul_one]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ ?_
      (aux_big_ge b · hL hd) (aux_big_le b · hL hd) <;>
    rw [hmul_one] <;> refine ENNReal.Tendsto.const_mul ?_ (Or.inl one_ne_zero)
  · simp_rw [sub_sub, sub_eq_add_neg]
    convert volume_ball_ratio_tendsto_nhds_one'' hd (C := -(S.separation / 2 + L * 2))
    rw [add_zero]
  · simp_rw [add_assoc]
    convert volume_ball_ratio_tendsto_nhds_one'' hd (C := S.separation / 2 + L * 2)
    rw [add_zero]

end DensityEqFdDensity

/-- Normalize `PeriodicSpherePackingConstant d` as a sup over packings with `separation = 1`. -/
public theorem periodic_constant_eq_periodic_constant_normalized :
    PeriodicSpherePackingConstant d = ⨆ (S : PeriodicSpherePacking d) (_ : S.separation = 1),
    S.density := by
  rw [iSup_subtype', PeriodicSpherePackingConstant]
  refine le_antisymm (iSup_le fun S => ?_) (iSup_le fun ⟨S, _⟩ =>
    le_iSup (fun S : PeriodicSpherePacking d => S.density) S)
  rw [← scale_density _ (inv_pos.mpr S.separation_pos)]
  exact le_iSup (fun x : { x : PeriodicSpherePacking d // x.separation = 1 } ↦ x.val.density)
    ⟨S.scale (inv_pos.mpr S.separation_pos), inv_mul_cancel₀ S.separation_pos.ne.symm⟩

section Fundamental_Domains_in_terms_of_Basis

open Submodule

variable (S : PeriodicSpherePacking d) (b : Basis (Fin d) ℤ S.lattice)

/-- Every point has a unique translate in the fundamental domain associated to a lattice basis. -/
public theorem PeriodicSpherePacking.fundamental_domain_unique_covers :
    ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _) := fun x =>
  have hspan : S.lattice = span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) :=
    (Basis.ofZLatticeBasis_span ℝ S.lattice b).symm
  let ⟨g, hg, hguniq⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
  ⟨⟨(g : EuclideanSpace ℝ (Fin d)), by simp [hspan]⟩, hg, fun y hy => Subtype.ext <|
    congrArg (fun z : span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) => (z : EuclideanSpace ℝ (Fin d)))
      (hguniq ⟨(y : EuclideanSpace ℝ (Fin d)), by simpa [hspan] using y.property⟩ hy)⟩

end Fundamental_Domains_in_terms_of_Basis

/-- An index equivalence for the default basis of the lattice of a periodic packing. -/
@[expose] public noncomputable def PeriodicSpherePacking.basis_index_equiv
    (P : PeriodicSpherePacking d) : (Module.Free.ChooseBasisIndex ℤ ↥P.lattice) ≃ (Fin d) :=
  ZLattice.basis_index_equiv P.lattice

noncomputable def PeriodicSpherePacking.defaultBasis (S : PeriodicSpherePacking d) :
    Basis (Fin d) ℤ ↥S.lattice :=
  ((ZLattice.module_free ℝ S.lattice).chooseBasis).reindex S.basis_index_equiv

/-- A basis-free variant of `PeriodicSpherePacking.density_eq`, stated using `ZLattice.covolume`. -/
@[simp] public theorem PeriodicSpherePacking.density_eq'
    (S : PeriodicSpherePacking d) (hd : 0 < d) : S.density =
    (ENat.toENNReal (S.numReps : ENat)) *
    volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) /
    Real.toNNReal (ZLattice.covolume S.lattice) := by
  let b : Basis (Fin d) ℤ ↥S.lattice := S.defaultBasis
  obtain ⟨L, hL⟩ := isBounded_iff_forall_norm_le.1
    (fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ S.lattice b))
  rw [Real.toNNReal_of_nonneg (ZLattice.covolume_pos S.lattice volume).le,
    S.density_eq b hL hd, ENat.toENNReal_coe]
  refine congrArg _ ((ENNReal.toReal_eq_toReal_iff' (IsBounded.measure_lt_top
      (fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ S.lattice b))).ne
    ENNReal.coe_ne_top).mp ?_)
  rw [ENNReal.coe_toReal, NNReal.coe_mk]
  exact (ZLattice.covolume_eq_measure_fundamentalDomain S.lattice volume
    (ZLattice.isAddFundamentalDomain b volume)).symm

/-- If a periodic packing has no centers, then its density is zero. -/
public theorem PeriodicSpherePacking.density_of_centers_empty (S : PeriodicSpherePacking d)
    (hd : 0 < d) [instEmpty : IsEmpty S.centers] : S.density = 0 := by
  let b := S.defaultBasis
  let D := fundamentalDomain (Basis.ofZLatticeBasis ℝ S.lattice b)
  haveI : IsEmpty (↥(S.centers ∩ D)) := ⟨fun x => instEmpty.false ⟨x.1, x.2.1⟩⟩
  rw [S.density_eq' hd, ← S.card_centers_inter_isFundamentalDomain D
    (fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ S.lattice b))
    (S.fundamental_domain_unique_covers b) hd]
  simp

end DensityFormula
