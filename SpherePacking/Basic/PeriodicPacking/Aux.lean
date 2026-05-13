/-
Copyright (c) 2024 Gareth Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gareth Ma
-/
module
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Basis.SMul

public import SpherePacking.Basic.SpherePacking
public import SpherePacking.ForMathlib.Encard

/-!
# Periodic packings: auxiliary finiteness and disjointness lemmas (blueprint Theorem 2.2)
-/

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
