/-
Copyright (c) 2024 Gareth Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gareth Ma
-/
module
public import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Order.LiminfLimsup
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Data.ENNReal.Inv

public import SpherePacking.Basic.SpherePacking
public import SpherePacking.ForMathlib.ENNReal
public import SpherePacking.ForMathlib.Encard
public import SpherePacking.ForMathlib.ZLattice


/-!
# Periodic packings: auxiliary finiteness and disjointness lemmas

This file collects technical lemmas used to control periodic sphere packings in bounded regions
(blueprint Theorem 2.2).

The main ingredients are disjointness of the balls of radius `S.separation / 2` around distinct
centers and a uniform lower bound on their volume. From this we deduce finiteness of `S.centers ∩ D`
for bounded `D`, and disjointness of distinct lattice translates under a uniqueness-of-covers
hypothesis.
-/

open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module

section aux_lemmas

variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))

private lemma isBounded_iUnion_ball_centers_inter (hD_isBounded : IsBounded D) :
    IsBounded (⋃ x ∈ S.centers ∩ D, ball x (S.separation / 2)) := by
  rcases (isBounded_iff_forall_norm_le).1 hD_isBounded with ⟨L, hL⟩
  refine (isBounded_iff_forall_norm_le).2 ⟨L + S.separation / 2, ?_⟩
  intro x hx
  rcases Set.mem_iUnion₂.1 hx with ⟨y, hy, hx⟩
  have hyL : ‖y‖ ≤ L := hL y hy.2
  have hxy : ‖x - y‖ < S.separation / 2 := by simpa [mem_ball, dist_eq_norm] using hx
  exact (norm_le_norm_add_norm_sub' x y).trans (by gcongr)

private lemma pairwiseDisjoint_ball_centers_inter (D : Set (EuclideanSpace ℝ (Fin d))) :
    Set.PairwiseDisjoint (S.centers ∩ D) (fun x ↦ ball x (S.separation / 2)) := by
  intro x hx y hy hxy
  refine ball_disjoint_ball ?_
  simpa [add_halves] using S.centers_dist' _ _ hx.left hy.left hxy

private theorem finite_of_bounded_iUnion_of_volume_lower_bound
    {ι τ : Type*} {s : Set ι} {f : ι → Set (EuclideanSpace ℝ τ)} {c : ℝ≥0∞} (hc : 0 < c)
    [Fintype τ] [NoAtoms (volume : Measure (EuclideanSpace ℝ τ))]
    (h_measurable : ∀ x ∈ s, MeasurableSet (f x))
    (h_bounded : IsBounded (⋃ x ∈ s, f x))
    (h_volume : ∀ x ∈ s, c ≤ volume (f x))
    (h_disjoint : s.PairwiseDisjoint f) :
    s.Finite := by
  classical
  let As : ι → Set (EuclideanSpace ℝ τ) := fun i => if i ∈ s then f i else ∅
  have As_mble : ∀ i, MeasurableSet (As i) := by
    intro i
    by_cases hi : i ∈ s
    · simpa [As, hi] using h_measurable i hi
    · simp [As, hi]
  have As_disj : Pairwise fun i j => Disjoint (As i) (As j) := by
    intro i j hij
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
    · simpa [As, hi, hj] using h_disjoint hi hj hij
    · simp [As, hi, hj]
    · simp [As, hi, hj]
    · simp [As, hi, hj]
  have hUnion_subset : (⋃ i, As i) ⊆ ⋃ x ∈ s, f x := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
    by_cases hs : i ∈ s
    · exact Set.mem_iUnion₂.2 ⟨i, hs, by simpa [As, hs] using hi⟩
    · simp [As, hs] at hi
  obtain ⟨L, hL⟩ := (h_bounded.subset hUnion_subset).subset_ball 0
  have hUnion_fin : volume (⋃ i, As i) ≠ ∞ :=
    ne_top_of_le_ne_top (volume_ball_lt_top _).ne (volume.mono hL)
  have hfinite : Set.Finite { i : ι | c ≤ volume (As i) } :=
    Measure.finite_const_le_meas_of_disjoint_iUnion (μ := volume) hc As_mble As_disj hUnion_fin
  refine hfinite.subset ?_
  intro i hi
  simpa [As, hi] using h_volume i hi

/-- A periodic packing has only finitely many centers in a bounded set (in positive dimension). -/
public lemma finite_centers_inter_of_isBounded (hD_isBounded : IsBounded D) (hd : 0 < d) :
    Finite ↑(S.centers ∩ D) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  refine (Set.finite_coe_iff).2 <| finite_of_bounded_iUnion_of_volume_lower_bound
      (c := volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)))
      (hc := by
        simpa using
          volume_ball_pos (0 : EuclideanSpace ℝ (Fin d)) (by nlinarith [S.separation_pos]))
      (h_measurable := fun _ _ => measurableSet_ball)
      (h_bounded := isBounded_iUnion_ball_centers_inter S D hD_isBounded)
      (h_volume := fun _ _ => by simp [Measure.addHaar_ball_center])
      (h_disjoint := by simpa using pairwiseDisjoint_ball_centers_inter S D)

/-- A periodic packing has finitely many centers in a fundamental domain of its lattice. -/
public lemma finite_centers_inter_fundamentalDomain {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    (hd : 0 < d) :
    Finite ↑(S.centers ∩ fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
  finite_centers_inter_of_isBounded S _ (ZSpan.fundamentalDomain_isBounded _) hd

open scoped Pointwise in
lemma finite_centers_inter_vadd_fundamentalDomain
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) (hd : 0 < d) (v : EuclideanSpace ℝ (Fin d)) :
    Finite ↑(S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))) :=
  finite_centers_inter_of_isBounded S _
    (IsBounded.vadd (ZSpan.fundamentalDomain_isBounded _) _) hd

end aux_lemmas

section Pointwise

open scoped Pointwise

variable {d : ℕ}

/--
If a set `D` meets each orbit of the lattice action in exactly one point, then distinct lattice
translates of `D` are disjoint.
-/
public lemma disjoint_vadd_of_unique_covers {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_unique_covers : ∀ x, ∃! g : Λ, g +ᵥ x ∈ D) {g h : Λ} (hgh : g ≠ h) :
    Disjoint (g +ᵥ D) (h +ᵥ D) := by
  refine Set.disjoint_left.2 fun x hxg hxh => ?_
  rcases hD_unique_covers x with ⟨g0, -, hg0uniq⟩
  exact hgh <| neg_injective <|
    (hg0uniq _ (by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hxg)).trans
      (hg0uniq _ (by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hxh)).symm

end Pointwise

section instances
variable {d : ℕ} (S : PeriodicSpherePacking d)
open scoped Pointwise

noncomputable def PeriodicSpherePacking.addActionOrbitRelEquiv
    (D : Set (EuclideanSpace ℝ (Fin d))) (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
    Quotient S.addAction.orbitRel ≃ ↑(S.centers ∩ D) where
  toFun := by
    refine Quotient.lift ?_ ?_
    · intro s
      let g := Classical.choose (hD_unique_covers s.val)
      use g.val + s.val, S.lattice_action g.prop s.prop,
        (Classical.choose_spec (hD_unique_covers s.val)).left
    · intro ⟨u, hu⟩ ⟨v, hv⟩ h
      change (S.addAction.orbitRel).r ⟨u, hu⟩ ⟨v, hv⟩ at h
      rw [AddAction.orbitRel_apply, AddAction.orbit, Set.mem_range] at h
      obtain ⟨⟨y, hy⟩, hy'⟩ := h
      have : y + v = u := Subtype.ext_iff.mp hy'
      subst this
      have hv' := (Classical.choose_spec (hD_unique_covers v)).right
      simp only [Subtype.forall] at hv'
      simp_rw [Subtype.forall, S.lattice.mk_vadd, vadd_eq_add, Subtype.mk.injEq, ← add_assoc]
      congr 1
      convert Subtype.ext_iff.mp (hv' _ ?_ ?_)
      · exact add_mem (SetLike.coe_mem _) hy
      · simp only [S.lattice.mk_vadd, vadd_eq_add, add_assoc]
        have := (Classical.choose_spec (hD_unique_covers (y + v))).left
        change (Classical.choose _ : S.lattice).val + (y + v) ∈ D at this
        simp only [Subtype.forall] at this
        exact this
  invFun := fun ⟨x, hx⟩ ↦ ⟦⟨x, hx.left⟩⟧
  left_inv := by
    apply Quotient.ind
    intro ⟨a, ha⟩
    simp_rw [Quotient.lift_mk, Quotient.eq]
    change (S.addAction.orbitRel).r _ _
    simp_rw [AddAction.orbitRel_apply, AddAction.orbit, Set.mem_range]
    simp [addAction_vadd]
  right_inv := by
    intro ⟨x, hx⟩
    simp_rw [Quotient.lift_mk, Subtype.mk.injEq, add_eq_right]
    obtain ⟨g, ⟨hg, hg'⟩⟩ := hD_unique_covers x
    trans g.val <;> norm_cast
    · apply hg'
      exact (Classical.choose_spec (hD_unique_covers x)).left
    · apply (hg' 0 ?_).symm
      simpa using hx.right

public noncomputable def PeriodicSpherePacking.addActionOrbitRelEquiv'
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) :
    Quotient S.addAction.orbitRel ≃ ↑(S.centers ∩ (fundamentalDomain (b.ofZLatticeBasis ℝ _))) := by
  refine S.addActionOrbitRelEquiv _ ?_
  intro x
  obtain ⟨v, ⟨hv, hv'⟩⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
  use ⟨v.val, ?_⟩, ?_, ?_
  · apply Set.mem_of_subset_of_mem ?_ v.prop
    rw [← Submodule.coe_toAddSubgroup, Basis.ofZLatticeBasis_span]
    rfl
  · simp only at hv' ⊢
    convert hv using 1
  · intro s hs
    rw [← hv' ⟨s, ?_⟩ hs]
    apply Set.mem_of_subset_of_mem _ s.prop
    rw [← Submodule.coe_toAddSubgroup, Basis.ofZLatticeBasis_span]
    rfl

public noncomputable def PeriodicSpherePacking.addActionOrbitRelEquiv''
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) (v : EuclideanSpace ℝ (Fin d)) :
    Quotient S.addAction.orbitRel ≃
      ↑(S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))) := by
  letI : Fintype ι := Fintype.ofFinite ι
  apply (S.addActionOrbitRelEquiv' b).trans
  exact {
    toFun := fun ⟨u, ⟨hu_centers, _⟩⟩ ↦ by
      use u - floor (b.ofZLatticeBasis ℝ _) (u - v)
      constructor
      · rw [sub_eq_neg_add]
        apply S.lattice_action ?_ hu_centers
        apply Submodule.neg_mem
        exact (mem_basis_Z_span ..).mp <| Submodule.coe_mem _
      · rw [Set.mem_vadd_set]
        use fract (b.ofZLatticeBasis ℝ _) (u - v), fract_mem_fundamentalDomain _ _, ?_
        rw [fract, vadd_eq_add]
        abel
    invFun := fun ⟨u, ⟨hu_centers, _⟩⟩ ↦ by
      use fract (b.ofZLatticeBasis ℝ _) u
      constructor
      · rw [fract, sub_eq_neg_add]
        apply S.lattice_action ?_ hu_centers
        apply Submodule.neg_mem
        exact (mem_basis_Z_span ..).mp <| Submodule.coe_mem _
      · exact fract_mem_fundamentalDomain _ _
    left_inv := fun ⟨u, ⟨hu_centers, hu_fd⟩⟩ ↦ by
      simp_rw [Subtype.mk.injEq]
      rw [sub_eq_add_neg, fract_add_ZSpan]
      · exact fract_eq_self.mpr hu_fd
      · apply neg_mem
        exact Submodule.coe_mem _
    right_inv := fun ⟨u, ⟨hu_centers, hu_fd⟩⟩ ↦ by
      simp_rw [Subtype.mk.injEq]
      rw [← EmbeddingLike.apply_eq_iff_eq (b.ofZLatticeBasis ℝ _).repr, map_sub]
      have hu_fd' : u - v ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _) := by
        rwa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] at hu_fd
      ext i
      set b' := b.ofZLatticeBasis ℝ _
      calc
        _ = b'.repr (fract b' u) i - b'.repr (floor b' (u - floor b' u - v)) i := by rfl
        _ = b'.repr (fract b' u) i - b'.repr (floor b' (u - v - floor b' u)) i := by abel_nf
        _ = b'.repr u i - ⌊b'.repr u i⌋ - (⌊b'.repr (u - v) i⌋ - ⌊b'.repr u i⌋) := by simp
        _ = b'.repr u i - ⌊b'.repr (u - v) i⌋ := by abel_nf
        _ = b'.repr u i := by
          rw [sub_eq_self, ← repr_floor_apply, (ZSpan.floor_eq_zero ..).mp hu_fd']
          simp
  }

instance (S : PeriodicSpherePacking 0) : Subsingleton S.centers := inferInstance
instance (S : PeriodicSpherePacking 0) : Finite S.centers := inferInstance

public noncomputable instance PeriodicSpherePacking.finiteOrbitRelQuotient :
    Finite (Quotient S.addAction.orbitRel) := by
  -- We choose an arbitrary ℤ-basis of S.lattice
  let b : Basis _ ℤ S.lattice := (ZLattice.module_free ℝ S.lattice).chooseBasis
  by_cases hd : 0 < d
  · haveI : Finite ↑(S.centers ∩ fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
      finite_centers_inter_fundamentalDomain S b hd
    exact Finite.of_equiv _ (S.addActionOrbitRelEquiv' b).symm
  · have : d = 0 := Nat.eq_zero_of_not_pos hd
    subst this
    exact Quotient.finite (AddAction.orbitRel ..)

public noncomputable instance : Fintype (Quotient S.addAction.orbitRel) :=
  Fintype.ofFinite _

end instances

section numReps

-- Gareth's Code

open scoped Pointwise

open Finset Set


variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))

-- TODO: rename
@[expose] public noncomputable def PeriodicSpherePacking.numReps : ℕ :=
  Fintype.card (Quotient S.addAction.orbitRel)

public theorem PeriodicSpherePacking.numReps_eq_one (hS : S.centers = S.lattice) :
    S.numReps = 1 := by
  rw [numReps]
  haveI : Subsingleton (Quotient S.addAction.orbitRel) := by
    rw [← AddAction.pretransitive_iff_subsingleton_quotient]
    constructor
    intro ⟨x, hx⟩ ⟨y, hy⟩
    rw [hS] at hx hy
    refine ⟨⟨y - x, sub_mem hy hx⟩, ?_⟩
    simp [addAction_vadd]
  let z : S.centers := ⟨0, by simp [hS]⟩
  exact (Fintype.card_eq_one_iff).2 ⟨⟦z⟧, fun y => Subsingleton.elim y _⟩

public theorem PeriodicSpherePacking.card_centers_inter_isFundamentalDomain
    (hD_isBounded : IsBounded D)
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) :
    haveI := @Fintype.ofFinite _ <| finite_centers_inter_of_isBounded S D hD_isBounded hd
    (S.centers ∩ D).toFinset.card = S.numReps := by
  rw [numReps]
  convert Finset.card_eq_of_equiv_fintype ?_
  simpa [Set.mem_toFinset] using (S.addActionOrbitRelEquiv D hD_unique_covers).symm

public theorem PeriodicSpherePacking.encard_centers_inter_isFundamentalDomain
    (hD_isBounded : IsBounded D)
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) :
    (S.centers ∩ D).encard = S.numReps := by
  rw [← S.card_centers_inter_isFundamentalDomain D hD_isBounded hD_unique_covers hd]
  convert Set.encard_eq_coe_toFinset_card _

theorem PeriodicSpherePacking.card_centers_inter_vadd_fundamentalDomain (hd : 0 < d)
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) (v : EuclideanSpace ℝ (Fin d)) :
    haveI := @Fintype.ofFinite _ <| finite_centers_inter_vadd_fundamentalDomain S b hd v
    (S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))).toFinset.card = S.numReps := by
  rw [numReps]
  exact card_eq_of_equiv_fintype (by simpa using (S.addActionOrbitRelEquiv'' b v).symm)

theorem PeriodicSpherePacking.encard_centers_inter_vadd_fundamentalDomain (hd : 0 < d)
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) (v : EuclideanSpace ℝ (Fin d)) :
    (S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))).encard = S.numReps := by
  rw [← S.card_centers_inter_vadd_fundamentalDomain hd b]
  convert Set.encard_eq_coe_toFinset_card _


end numReps

-- TODO: Merge above and below; rename stuff as needed

section numReps_aux

-- Sid's code for Cohn-Elkies

variable {d : ℕ}

public noncomputable instance PeriodicSpherePacking.instFintypeNumReps'
  (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D) :
  Fintype ↑(S.centers ∩ D) :=
    @Fintype.ofFinite _ <| finite_centers_inter_of_isBounded S D hD_isBounded hd

@[expose] public noncomputable def PeriodicSpherePacking.numReps'
  (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D) : ℕ :=
  letI := S.instFintypeNumReps' hd hD_isBounded
  Fintype.card ↑(S.centers ∩ D)

public theorem PeriodicSpherePacking.numReps_eq_numReps' (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
  (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
  S.numReps = S.numReps' hd hD_isBounded := by
  simpa [PeriodicSpherePacking.numReps', Set.toFinset_card] using
    (S.card_centers_inter_isFundamentalDomain (D := D) hD_isBounded hD_unique_covers hd).symm

-- theorem PeriodicSpherePacking.numReps_ne_zero (S : PeriodicSpherePacking d)

end numReps_aux

section theorem_2_3

variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))

open scoped Pointwise

private theorem aux
    {ι : Type*} (b : Basis ι ℝ (EuclideanSpace ℝ (Fin d)))
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain b, ‖x‖ ≤ L) (R : ℝ) :
    ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R - L),
      x +ᵥ (fundamentalDomain b : Set (EuclideanSpace ℝ (Fin d)))
        ⊆ ball 0 R := by
  intro x hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨y, ⟨_, hy⟩, hy'⟩ := hx
  obtain ⟨z, hz, rfl⟩ := Set.mem_vadd_set.mp hy'
  simp only [mem_ball, dist_zero_right, vadd_eq_add] at hy ⊢
  have hzL : ‖z‖ ≤ L := hL z hz
  have hsum : ‖y‖ + ‖z‖ < R := by linarith [hy, hzL]
  exact lt_of_le_of_lt (norm_add_le _ _) hsum

private theorem disjoint_vadd_fundamentalDomain
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ S.lattice) (hy : y ∈ S.lattice) (hxy : x ≠ y) :
    Disjoint (x +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))
      (y +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  let Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
    Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ _))
  have hx' : x ∈ Λ := by
    simpa [Λ, S.basis_Z_span] using hx
  have hy' : y ∈ Λ := by
    simpa [Λ, S.basis_Z_span] using hy
  have hxy' : (⟨x, hx'⟩ : Λ) ≠ ⟨y, hy'⟩ :=
    fun h => hxy (by simpa using congrArg Subtype.val h)
  simpa [Λ] using
    (disjoint_vadd_of_unique_covers (d := d) (Λ := Λ)
      (D := fundamentalDomain (b.ofZLatticeBasis ℝ _))
      (by intro u; simpa using
        exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) u) hxy')

-- Theorem 2.3, lower bound
public theorem PeriodicSpherePacking.aux_ge
    (hd : 0 < d) {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) :
    (↑S.centers ∩ ball 0 R).encard ≥
      S.numReps • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R - L)).encard := by
  have := aux S (b.ofZLatticeBasis ℝ _) hL R
  have := Set.inter_subset_inter_right S.centers this
  rw [Set.biUnion_eq_iUnion, Set.inter_iUnion] at this
  have := Set.encard_mono this
  rw [Set.encard_iUnion_of_pairwiseDisjoint] at this
  · simp_rw [S.encard_centers_inter_vadd_fundamentalDomain hd] at this
    · convert this.ge
      rw [nsmul_eq_mul, ENat.tsum_set_const, mul_comm]
  · intro ⟨x, hx⟩ _ ⟨y, hy⟩ _ hxy
    have hxy' : x ≠ y := fun h => hxy (Subtype.ext h)
    refine Set.disjoint_left.2 fun u hux huy =>
      (Set.disjoint_left.1 (disjoint_vadd_fundamentalDomain (S := S) b hx.left hy.left hxy'))
        hux.right huy.right

private theorem aux'
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) :
    ball 0 R
      ⊆ ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + L),
        x +ᵥ (fundamentalDomain (b.ofZLatticeBasis ℝ _) : Set (EuclideanSpace ℝ (Fin d))) := by
  letI : Fintype ι := Fintype.ofFinite ι
  intro x hx
  simp only [Set.mem_iUnion, exists_prop]
  use floor (b.ofZLatticeBasis ℝ _) x
  constructor
  · constructor
    · rw [SetLike.mem_coe, ← S.mem_basis_Z_span b]
      exact Submodule.coe_mem _
    · rw [mem_ball_zero_iff] at hx ⊢
      have hfloor : ‖floor (b.ofZLatticeBasis ℝ _) x‖ = ‖x - fract (b.ofZLatticeBasis ℝ _) x‖ := by
        simp [fract]
      refine lt_of_le_of_lt (hfloor.le.trans (norm_sub_le _ _)) ?_
      exact add_lt_add_of_lt_of_le hx (hL _ (fract_mem_fundamentalDomain _ _))
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]
    exact fract_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x

-- Theorem 2.3, upper bound - the proof is similar to lower bound
public theorem PeriodicSpherePacking.aux_le
    (hd : 0 < d) {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) :
    (↑S.centers ∩ ball 0 R).encard
      ≤ S.numReps • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + L)).encard := by
  have := aux' S b hL R
  have := Set.inter_subset_inter_right S.centers this
  rw [Set.biUnion_eq_iUnion, Set.inter_iUnion] at this
  have := Set.encard_mono this
  rw [Set.encard_iUnion_of_pairwiseDisjoint] at this
  · simp_rw [S.encard_centers_inter_vadd_fundamentalDomain hd] at this
    · convert this
      rw [nsmul_eq_mul, ENat.tsum_set_const, mul_comm]
  · intro ⟨x, hx⟩ _ ⟨y, hy⟩ _ hxy
    have hxy' : x ≠ y := fun h => hxy (Subtype.ext h)
    refine Set.disjoint_left.2 fun u hux huy =>
      (Set.disjoint_left.1 (disjoint_vadd_fundamentalDomain (S := S) b hx.left hy.left hxy'))
        hux.right huy.right


end theorem_2_3

----------------------------------------------------
