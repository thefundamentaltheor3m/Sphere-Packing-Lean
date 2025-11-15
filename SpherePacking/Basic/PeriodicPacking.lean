/-
Copyright (c) 2024 Gareth Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gareth Ma
-/
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Dynamics.Ergodic.Action.Regular

import SpherePacking.Basic.SpherePacking
import SpherePacking.ForMathlib.ENNReal
import SpherePacking.ForMathlib.Encard
import SpherePacking.ForMathlib.ENat
import SpherePacking.ForMathlib.ZLattice

-- import Mathlib

/- In this file, we establish results about density of periodic packings. This roughly corresponds
to Section 2.2, "Bounds on Finite Density of Periodic Packing". -/

/-#
Key results:

* `PeriodicSpherePacking.density_eq`: The density of a periodic sphere packing equals the natural
density within a fundamental domain w.r.t. any basis.
-/

open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module ZLattice

section aux_lemmas

variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))

lemma aux1 (hD_isBounded : IsBounded D) :
    IsBounded (⋃ x ∈ S.centers ∩ D, ball x (S.separation / 2)) := by
  apply isBounded_iff_forall_norm_le.mpr
  obtain ⟨L, hL⟩ := isBounded_iff_forall_norm_le.mp <| hD_isBounded
  use L + S.separation / 2
  intro x hx
  obtain ⟨y, s, hy, hy'⟩ := Set.mem_iUnion.mp hx
  rw [Set.mem_range, exists_prop] at hy
  obtain ⟨hy, rfl⟩ := hy
  rw [mem_ball, dist_eq_norm] at hy'
  specialize hL y hy.right
  exact (norm_le_norm_add_norm_sub' x y).trans (by gcongr)

lemma aux2 (D : Set (EuclideanSpace ℝ (Fin d))) :
    Set.PairwiseDisjoint (S.centers ∩ D) (fun x ↦ ball x (S.separation / 2)) := by
  intro x hx y hy hxy
  apply ball_disjoint_ball
  rw [add_halves]
  exact S.centers_dist' _ _ hx.left hy.left hxy

theorem aux3 {ι τ : Type*} {s : Set ι} {f : ι → Set (EuclideanSpace ℝ τ)} {c : ℝ≥0∞} (hc : 0 < c)
    [Fintype τ] [NoAtoms (volume : Measure (EuclideanSpace ℝ τ))]
    (h_measurable : ∀ x ∈ s, MeasurableSet (f x))
    (h_bounded : IsBounded (⋃ x ∈ s, f x))
    (h_volume : ∀ x ∈ s, c ≤ volume (f x))
    (h_disjoint : s.PairwiseDisjoint f) :
    s.Finite := by
  wlog h_countable : s.Countable with h_wlog
  · by_contra! h_finite
    rw [Set.Countable, ← Cardinal.mk_le_aleph0_iff, not_le] at h_countable
    -- Brilliant(!!) idea by Etienne Marion on Zulip
    -- If s is uncountable, then we can argue on a countable subset!
    obtain ⟨t, ⟨ht_subset, ht_aleph0⟩⟩ := Cardinal.le_mk_iff_exists_subset.mp h_countable.le
    have ht_infinite : Infinite t := Cardinal.aleph0_le_mk_iff.mp ht_aleph0.symm.le
    have ht_countable := Cardinal.mk_le_aleph0_iff.mp ht_aleph0.le
    specialize @h_wlog _ _ t f c hc _ _ ?_ ?_ ?_ ?_ ht_countable
    · exact fun x hx ↦ h_measurable x (ht_subset hx)
    · exact h_bounded.subset <| Set.biUnion_mono ht_subset (by intros; rfl)
    · exact fun x hx ↦ h_volume x (ht_subset hx)
    · exact Set.Pairwise.mono ht_subset h_disjoint
    · exact ht_infinite.not_finite h_wlog
  · haveI : Countable s := h_countable
    obtain ⟨L, hL⟩ := h_bounded.subset_ball 0
    have h_volume' := volume.mono hL
    rw [OuterMeasure.measureOf_eq_coe, Measure.coe_toOuterMeasure, Set.biUnion_eq_iUnion,
      measure_iUnion] at h_volume'
    · have h_le : ∑' (n : ↑s), c ≤ ∑' (n : ↑s), volume (f ↑n) :=
          Summable.tsum_mono (f := fun _ ↦ c) (g := fun (x : s) ↦ volume (f x)) ?_ ?_ ?_
      · have h₁ := (ENNReal.tsum_set_const _ _ ▸ h_le).trans h_volume'
        rw [← Set.encard_lt_top_iff, ← ENat.toENNReal_lt, ENat.toENNReal_top]
        refine lt_of_le_of_lt ((ENNReal.le_div_iff_mul_le ?_ ?_).mpr h₁) <|
          ENNReal.div_lt_top ?_ hc.ne.symm
        · left; positivity
        · right; exact (volume_ball_lt_top _).ne
        · exact (volume_ball_lt_top _).ne
      · exact ENNReal.summable
      · exact ENNReal.summable
      · intro x
        exact h_volume x.val x.prop
    · intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      exact h_disjoint hx hy (by simpa using hxy)
    · exact fun ⟨x, hx⟩ ↦ h_measurable x hx

lemma aux4 (hD_isBounded : IsBounded D) (hd : 0 < d) : Finite ↑(S.centers ∩ D) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  apply aux3 (c := volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))) ?_ ?_
      (aux1 S D hD_isBounded)
  · intros
    simp [Measure.addHaar_ball_center]
  · intro x hx y hy hxy
    apply ball_disjoint_ball
    simpa [add_halves] using S.centers_dist' _ _ hx.left hy.left hxy
  · apply volume_ball_pos
    linarith [S.separation_pos]
  · intros
    exact measurableSet_ball

lemma aux4' {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) (hd : 0 < d) :
    Finite ↑(S.centers ∩ fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
  aux4 S _ (ZSpan.fundamentalDomain_isBounded _) hd

open scoped Pointwise in
lemma aux4''
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) (hd : 0 < d) (v : EuclideanSpace ℝ (Fin d)) :
    Finite ↑(S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))) :=
  aux4 S _ (IsBounded.vadd (ZSpan.fundamentalDomain_isBounded _) _) hd

end aux_lemmas

section instances
variable {d : ℕ} (S : PeriodicSpherePacking d)
open scoped Pointwise

-- TODO: rename + move
theorem PeriodicSpherePacking.fract_centers
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) (s : S.centers) :
    fract (b.ofZLatticeBasis ℝ _) s.val ∈ S.centers := by
  have := (floor (b.ofZLatticeBasis ℝ _) s).prop
  simp_rw [S.basis_Z_span] at this
  rw [fract_apply, sub_eq_add_neg, add_comm]
  apply S.lattice_action (neg_mem this) s.prop

-- TODO: rename + move
theorem PeriodicSpherePacking.orbitRel_fract
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) (a : S.centers) :
    (S.addAction.orbitRel).r ⟨fract (b.ofZLatticeBasis ℝ _) a, S.fract_centers _ _⟩ a := by
  rw [AddAction.orbitRel_apply, AddAction.orbit, Set.mem_range]
  refine ⟨⟨-↑(floor (b.ofZLatticeBasis ℝ _) ↑a), ?_⟩, ?_⟩
  · apply neg_mem
    have := (floor (b.ofZLatticeBasis ℝ _) a.val).prop
    simp_rw [S.basis_Z_span] at this
    exact this
  · simp_rw [fract_apply, sub_eq_neg_add]
    rfl

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
      simp at hv'
      simp_rw [Subtype.forall, S.lattice.mk_vadd, vadd_eq_add, Subtype.mk.injEq, ← add_assoc,]
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

noncomputable def PeriodicSpherePacking.addActionOrbitRelEquiv'
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) :
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

noncomputable def PeriodicSpherePacking.addActionOrbitRelEquiv''
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) (v : EuclideanSpace ℝ (Fin d)) :
    Quotient S.addAction.orbitRel ≃
      ↑(S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))) := by
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

noncomputable instance PeriodicSpherePacking.finiteOrbitRelQuotient :
    Finite (Quotient S.addAction.orbitRel) := by
  -- We choose an arbitrary ℤ-basis of S.lattice
  let b : Basis _ ℤ S.lattice := (ZLattice.module_free ℝ S.lattice).chooseBasis
  by_cases hd : 0 < d
  · have : Finite ↑(S.centers ∩ fundamentalDomain (b.ofZLatticeBasis ℝ _)) := aux4' S b hd
    exact (Finite.of_equiv _ (S.addActionOrbitRelEquiv' b).symm)
  · have : d = 0 := Nat.eq_zero_of_not_pos hd
    subst this
    exact Quotient.finite (AddAction.orbitRel ..)

noncomputable instance : Fintype (Quotient S.addAction.orbitRel) :=
  Fintype.ofFinite _

end instances

section numReps

-- Gareth's Code

open scoped Pointwise


variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))

noncomputable instance PeriodicSpherePacking.instCentersSetoid : Setoid S.centers :=
  S.addAction.orbitRel

-- TODO: rename
noncomputable def PeriodicSpherePacking.numReps : ℕ :=
  Fintype.card (Quotient S.addAction.orbitRel)

theorem PeriodicSpherePacking.numReps_eq_one (hS : S.centers = S.lattice) : S.numReps = 1 := by
  rw [numReps]
  apply le_antisymm
  · rw [Fintype.card_le_one_iff_subsingleton, ← AddAction.pretransitive_iff_subsingleton_quotient]
    constructor
    intro ⟨x, hx⟩ ⟨y, hy⟩
    rw [hS] at hx hy
    use ⟨y - x, sub_mem hy hx⟩
    simp [addAction_vadd]
  · rw [Fintype.card, Finset.one_le_card]
    let zero : S.centers := ⟨0, by rw [hS]; exact zero_mem _⟩
    use ⟦zero⟧, by simp [zero]

theorem PeriodicSpherePacking.card_centers_inter_isFundamentalDomain
    (hD_isBounded : IsBounded D)
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) :
    haveI := @Fintype.ofFinite _ <| aux4 S D hD_isBounded hd
    (S.centers ∩ D).toFinset.card = S.numReps := by
  rw [numReps]
  convert Finset.card_eq_of_equiv_fintype ?_
  simpa [Set.mem_toFinset] using (S.addActionOrbitRelEquiv D hD_unique_covers).symm

theorem PeriodicSpherePacking.encard_centers_inter_isFundamentalDomain
    (hD_isBounded : IsBounded D)
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) :
    (S.centers ∩ D).encard = S.numReps := by
  rw [← S.card_centers_inter_isFundamentalDomain D hD_isBounded hD_unique_covers hd]
  convert Set.encard_eq_coe_toFinset_card _

theorem PeriodicSpherePacking.card_centers_inter_fundamentalDomain (hd : 0 < d)
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) :
    haveI := @Fintype.ofFinite _ <| aux4' S b hd
    (S.centers ∩ (fundamentalDomain (b.ofZLatticeBasis ℝ _))).toFinset.card = S.numReps := by
  rw [numReps]
  convert Finset.card_eq_of_equiv_fintype ?_
  simpa [Set.mem_toFinset] using (S.addActionOrbitRelEquiv' b).symm

theorem PeriodicSpherePacking.encard_centers_inter_fundamentalDomain (hd : 0 < d)
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) :
    (S.centers ∩ (fundamentalDomain (b.ofZLatticeBasis ℝ _))).encard = S.numReps := by
  rw [← S.card_centers_inter_fundamentalDomain hd b]
  convert Set.encard_eq_coe_toFinset_card _

theorem PeriodicSpherePacking.card_centers_inter_vadd_fundamentalDomain (hd : 0 < d)
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) (v : EuclideanSpace ℝ (Fin d)) :
    haveI := @Fintype.ofFinite _ <| aux4'' S b hd v
    (S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))).toFinset.card = S.numReps := by
  rw [numReps]
  convert Finset.card_eq_of_equiv_fintype ?_
  simpa [Set.mem_toFinset] using (S.addActionOrbitRelEquiv'' b _).symm

theorem PeriodicSpherePacking.encard_centers_inter_vadd_fundamentalDomain (hd : 0 < d)
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) (v : EuclideanSpace ℝ (Fin d)) :
    (S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))).encard = S.numReps := by
  rw [← S.card_centers_inter_vadd_fundamentalDomain hd b]
  convert Set.encard_eq_coe_toFinset_card _


end numReps

-- TODO: Merge above and below; rename stuff as needed

section numReps_aux

  -- Sid's code for Cohn-Elkies

variable {d : ℕ}

noncomputable instance PeriodicSpherePacking.instFintypeNumReps'
  (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D) :
  Fintype ↑(S.centers ∩ D) := @Fintype.ofFinite _ <| aux4 S D hD_isBounded hd

noncomputable def PeriodicSpherePacking.numReps' (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D) : ℕ :=
  letI := S.instFintypeNumReps' hd hD_isBounded
  Fintype.card ↑(S.centers ∩ D)

theorem PeriodicSpherePacking.numReps'_nonneg (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D) :
  0 ≤ S.numReps' hd hD_isBounded := by
  letI := S.instFintypeNumReps' hd hD_isBounded
  rw [PeriodicSpherePacking.numReps']
  exact Nat.zero_le (Fintype.card ↑(S.centers ∩ D))

theorem PeriodicSpherePacking.numReps_eq_numReps' (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
  (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
  S.numReps = S.numReps' hd hD_isBounded := by
  letI := S.instFintypeNumReps' hd hD_isBounded
  rw [PeriodicSpherePacking.numReps']
  rw [← S.card_centers_inter_isFundamentalDomain D hD_isBounded hD_unique_covers hd]
  exact Set.toFinset_card (S.centers ∩ D)

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
  specialize hL z hz
  calc
    _ ≤ ‖y‖ + ‖z‖ := norm_add_le _ _
    _ < (R - L) + L := by linarith
    _ = R := by ring

-- Theorem 2.3, lower bound
theorem PeriodicSpherePacking.aux_ge
    (hd : 0 < d) {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice)
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
    simp only [Set.disjoint_iff, Set.subset_empty_iff]
    ext u
    rw [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro ⟨_, hux⟩ ⟨_, huy⟩
    obtain ⟨w, hw, hw_unique⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) u
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] at hux huy
    have hx := hw_unique ⟨-x, ?_⟩ ?_
    · have hy := hw_unique ⟨-y, ?_⟩ ?_
      · apply hxy
        rw [Subtype.ext_iff, ← neg_inj]
        exact Subtype.ext_iff.mp (hx.trans hy.symm)
      · apply neg_mem
        apply Set.mem_of_subset_of_mem (s₁ := S.lattice)
        · rw [S.basis_Z_span]
        · exact hy.left
      · simp_rw [Submodule.vadd_def, vadd_eq_add, neg_add_eq_sub]
        exact huy
    · apply neg_mem
      apply Set.mem_of_subset_of_mem (s₁ := S.lattice)
      · rw [S.basis_Z_span]
      · exact hx.left
    · simp_rw [Submodule.vadd_def, vadd_eq_add, neg_add_eq_sub]
      exact hux

private theorem aux'
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice)
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) :
    ball 0 R
      ⊆ ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + L),
        x +ᵥ (fundamentalDomain (b.ofZLatticeBasis ℝ _) : Set (EuclideanSpace ℝ (Fin d))) := by
  intro x hx
  simp only [Set.mem_iUnion, exists_prop]
  use floor (b.ofZLatticeBasis ℝ _) x
  constructor
  · constructor
    · rw [SetLike.mem_coe, ← S.mem_basis_Z_span b]
      exact Submodule.coe_mem _
    · have : floor (b.ofZLatticeBasis ℝ _) x = x - fract (b.ofZLatticeBasis ℝ _) x := by
        rw [fract]
        abel
      rw [mem_ball_zero_iff] at hx ⊢
      calc
        _ = ‖x - fract (b.ofZLatticeBasis ℝ _) x‖ := congrArg _ this
        _ ≤ ‖x‖ + ‖fract (b.ofZLatticeBasis ℝ _) x‖ := norm_sub_le _ _
        _ < R + L := add_lt_add_of_lt_of_le hx (hL _ (fract_mem_fundamentalDomain _ _))
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]
    exact fract_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x

-- Theorem 2.3, upper bound - the proof is similar to lower bound
theorem PeriodicSpherePacking.aux_le
    (hd : 0 < d) {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice)
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
    simp only [Set.disjoint_iff, Set.subset_empty_iff]
    ext u
    rw [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro ⟨_, hux⟩ ⟨_, huy⟩
    obtain ⟨w, hw, hw_unique⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) u
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] at hux huy
    have hx := hw_unique ⟨-x, ?hx₁⟩ ?hx₂
    case hx₁ =>
      apply neg_mem
      apply Set.mem_of_subset_of_mem (s₁ := S.lattice)
      · rw [S.basis_Z_span]
      · exact hx.left
    case hx₂ =>
      simp_rw [Submodule.vadd_def, vadd_eq_add, neg_add_eq_sub]
      exact hux
    have hy := hw_unique ⟨-y, ?hy₁⟩ ?hy₂
    case hy₁ =>
      apply neg_mem
      apply Set.mem_of_subset_of_mem (s₁ := S.lattice)
      · rw [S.basis_Z_span]
      · exact hy.left
    case hy₂ =>
      simp_rw [Submodule.vadd_def, vadd_eq_add, neg_add_eq_sub]
      exact huy
    apply hxy
    rw [Subtype.ext_iff, ← neg_inj]
    exact Subtype.ext_iff.mp (hx.trans hy.symm)


end theorem_2_3

----------------------------------------------------

section theorem_2_2

/- In this section we prove Theorem 2.2 of the blueprint. Below, instead of using a single
assumption `IsAddFundamentalDomain S.lattice D`, we chose to split it up into `hD_unique_covers` and
`hD_measure` (see below), which together (along with that D is null measurable) imply that `D` is an
additive fundamental domain. We do this because annoyingly, `IsAddFundamentalDomain` only requires D
to *almost* cover the entire space (ℝ ^ n), i.e. up to a null measurable set, and also for the
cosets to be *almost* disjoint. This makes the proofs below extremely annoying. For example, proving
that `volume (⋃ x ∈ s, x +ᵥ D) = s.encard • volume D` is tedious because `measure_iUnion` requires
things to be strictly disjoint. In short, results below *should* work if D is
`IsAddFundamentalDomain`, but we don't bother.

Note that this is consistent with how some parts of Mathlib are structured - they don't bother
either :)
-/

open scoped Pointwise
variable {d : ℕ} (S : PeriodicSpherePacking d)
  {ι : Type*} [Fintype ι]
  (D : Set (EuclideanSpace ℝ (Fin d))) {L : ℝ} (R : ℝ)

private theorem hD_isAddFundamentalDomain
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D) :
    IsAddFundamentalDomain S.lattice D where
  nullMeasurableSet := hD_measurable.nullMeasurableSet
  ae_covers := Filter.Eventually.of_forall fun x ↦ (hD_unique_covers x).exists
  aedisjoint := by
    apply Measure.pairwise_aedisjoint_of_aedisjoint_forall_ne_zero
    · intro g hg
      apply Disjoint.aedisjoint
      rw [Set.disjoint_iff]
      intro x ⟨hx₁, hx₂⟩
      have ⟨y, ⟨_, hy_unique⟩⟩ := hD_unique_covers x
      have hy₁ := hy_unique 0 (by simpa)
      have hy₂ := hy_unique (-g) (Set.mem_vadd_set_iff_neg_vadd_mem.mp hx₁)
      rw [neg_eq_iff_eq_neg.mp hy₂, ← hy₁] at hg
      norm_num at hg
    · exact fun _ ↦ quasiMeasurePreserving_add_left _ _

theorem aux7 (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hL : ∀ x ∈ D, ‖x‖ ≤ L) :
    ball 0 (R - L) ⊆ ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R, (x +ᵥ D) := by
  intro x hx
  rw [mem_ball_zero_iff] at hx
  obtain ⟨g, hg, _⟩ := hD_unique_covers x
  simp_rw [Set.mem_iUnion, exists_prop, Set.mem_inter_iff]
  refine ⟨-g.val, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · simp
  · rw [← norm_neg] at hx
    rw [mem_ball_zero_iff, norm_neg]
    calc
      _ = ‖(g + x) + (-x)‖ := by congr; abel
      _ ≤ ‖(g + x)‖ + ‖(-x)‖ := norm_add_le _ _
      _ < L + (R - L) := add_lt_add_of_le_of_lt (hL _ hg) hx
      _ = R := by abel
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg]
    exact hg

instance (E : Type*) [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E] [Module ℤ E]
    [Module ℝ E] (μ : Measure E) [μ.IsAddLeftInvariant] [IsScalarTower ℤ ℝ E] (s : Submodule ℤ E) :
    VAddInvariantMeasure s E μ where
  measure_preimage_vadd c t ht := by
    simp only [Submodule.vadd_def, vadd_eq_add, measure_preimage_add]

-- Theorem 2.2, lower bound
theorem PeriodicSpherePacking.aux2_ge
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)
    (hL : ∀ x ∈ D, ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≥ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - L)) / volume D := by
  rw [ge_iff_le, ENNReal.div_le_iff]
  · convert volume.mono <| aux7 S D R hD_unique_covers hL
    rw [OuterMeasure.measureOf_eq_coe, Measure.coe_toOuterMeasure]
    have : Countable ↑S.lattice := inferInstance
    have : Countable ↑(↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
      Set.Countable.mono (Set.inter_subset_left) this
    rw [Set.biUnion_eq_iUnion, measure_iUnion]
    · rw [tsum_congr fun i ↦ measure_vadd .., ENNReal.tsum_set_const]
    · intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      replace hxy : x ≠ y := Subtype.ext_iff.ne.mp hxy
      simp_rw [Set.disjoint_iff]
      intro v ⟨hxv, hyv⟩
      obtain ⟨⟨z, hz⟩, _, hz_unique⟩ := hD_unique_covers v
      have hx' := hz_unique ⟨-x, neg_mem hx.left⟩ (Set.mem_vadd_set_iff_neg_vadd_mem.mp hxv)
      have hy' := hz_unique ⟨-y, neg_mem hy.left⟩ (Set.mem_vadd_set_iff_neg_vadd_mem.mp hyv)
      replace hx' : x = -z := neg_eq_iff_eq_neg.mp <| Subtype.ext_iff.mp hx'
      replace hy' : y = -z := neg_eq_iff_eq_neg.mp <| Subtype.ext_iff.mp hy'
      exact hxy (hx'.trans hy'.symm)
    · intro i
      exact MeasurableSet.const_vadd hD_measurable i.val
  · exact (hD_isAddFundamentalDomain S D ‹_› ‹_›).measure_ne_zero (NeZero.ne volume)
  · have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
    rw [← lt_top_iff_ne_top]
    exact Bornology.IsBounded.measure_lt_top (isBounded_iff_forall_norm_le.mpr ⟨L, hL⟩)

theorem aux8 (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hL : ∀ x ∈ D, ‖x‖ ≤ L) :
    ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R, (x +ᵥ D) ⊆ ball 0 (R + L) := by
  intro x hx
  rw [mem_ball_zero_iff]
  obtain ⟨g, _, _⟩ := hD_unique_covers x
  simp_rw [Set.mem_iUnion, exists_prop, Set.mem_inter_iff] at hx
  obtain ⟨i, ⟨_, hi_ball⟩, hi_fd⟩ := hx
  rw [mem_ball_zero_iff] at hi_ball
  have := hL (-i + x) (Set.mem_vadd_set_iff_neg_vadd_mem.mp hi_fd)
  calc
    _ = ‖i + (-i + x)‖ := by congr; abel
    _ ≤ ‖i‖ + ‖-i + x‖ := norm_add_le _ _
    _ < R + L := add_lt_add_of_lt_of_le hi_ball this

-- Theorem 2.2, upper bound
theorem PeriodicSpherePacking.aux2_le
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)
    (hL : ∀ x ∈ D, ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L)) / volume D := by
  rw [ENNReal.le_div_iff_mul_le]
  · convert volume.mono <| aux8 S D R hD_unique_covers hL
    rw [OuterMeasure.measureOf_eq_coe, Measure.coe_toOuterMeasure]
    have : Countable ↑S.lattice := inferInstance
    have : Countable ↑(↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
      Set.Countable.mono (Set.inter_subset_left) this
    rw [Set.biUnion_eq_iUnion, measure_iUnion]
    · rw [tsum_congr fun i ↦ measure_vadd .., ENNReal.tsum_set_const]
    · intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      replace hxy : x ≠ y := Subtype.ext_iff.ne.mp hxy
      simp_rw [Set.disjoint_iff]
      intro v ⟨hxv, hyv⟩
      obtain ⟨⟨z, hz⟩, _, hz_unique⟩ := hD_unique_covers v
      have hx' := hz_unique ⟨-x, neg_mem hx.left⟩ (Set.mem_vadd_set_iff_neg_vadd_mem.mp hxv)
      have hy' := hz_unique ⟨-y, neg_mem hy.left⟩ (Set.mem_vadd_set_iff_neg_vadd_mem.mp hyv)
      replace hx' : x = -z := neg_eq_iff_eq_neg.mp <| Subtype.ext_iff.mp hx'
      replace hy' : y = -z := neg_eq_iff_eq_neg.mp <| Subtype.ext_iff.mp hy'
      exact hxy (hx'.trans hy'.symm)
    · intro i
      exact MeasurableSet.const_vadd hD_measurable i.val
  · left
    exact (hD_isAddFundamentalDomain S D ‹_› ‹_›).measure_ne_zero (NeZero.ne volume)
  · left
    have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
    rw [← lt_top_iff_ne_top]
    exact Bornology.IsBounded.measure_lt_top (isBounded_iff_forall_norm_le.mpr ⟨L, hL⟩)

open ZSpan

variable (b : Basis ι ℤ S.lattice)

-- Theorem 2.2 lower bound, in terms of fundamental domain of Z-lattice
theorem PeriodicSpherePacking.aux2_ge'
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≥ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - L))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  refine S.aux2_ge _ R ?_ (fundamentalDomain_measurableSet _) hL hd
  intro x
  obtain ⟨⟨v, hv⟩, hv'⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
  simp only [S.basis_Z_span] at hv hv' ⊢
  use ⟨v, hv⟩, hv'.left, ?_
  intro ⟨y, hy⟩ hy'
  have := hv'.right ⟨y, ?_⟩ hy'
  · rwa [Subtype.ext_iff] at this ⊢
  · rw [S.basis_Z_span]
    exact hy

-- Theorem 2.2 upper bound, in terms of fundamental domain of Z-lattice
theorem PeriodicSpherePacking.aux2_le'
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  refine S.aux2_le _ R ?_ (fundamentalDomain_measurableSet _) hL hd
  intro x
  obtain ⟨⟨v, hv⟩, hv'⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
  simp only [S.basis_Z_span] at hv hv' ⊢
  use ⟨v, hv⟩, hv'.left, ?_
  intro ⟨y, hy⟩ hy'
  have := hv'.right ⟨y, ?_⟩ hy'
  · rwa [Subtype.ext_iff] at this ⊢
  · rw [S.basis_Z_span]
    exact hy

section finiteDensity_limit

/- TODO: consider moving this section. -/

open MeasureTheory Measure Metric ZSpan

variable
  {d : ℕ} {S : PeriodicSpherePacking d}
  {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)

theorem aux_big_le
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
    gcongr
    convert ENat.toENNReal_le.mpr (S.aux_le hd b hL _)
    simp
  _ ≤ S.numReps
        * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L + L))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)))
            * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    rw [nsmul_eq_mul]
    gcongr
    exact S.aux2_le' _ b hL hd
  _ = S.numReps
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := by
    rw [← mul_div_assoc, ← mul_div_assoc, mul_two, ← add_assoc, ← ENNReal.mul_div_right_comm,
      ← ENNReal.mul_div_right_comm, mul_assoc, mul_assoc]
    congr 3
    rw [mul_comm]

theorem aux_big_ge
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
    gcongr
    convert ENat.toENNReal_le.mpr (S.aux_ge hd b hL _)
    simp
  _ ≥ S.numReps
        * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - S.separation / 2 - L - L))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)))
            * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    rw [nsmul_eq_mul]
    gcongr
    exact S.aux2_ge' _ b hL hd
  _ = S.numReps
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - S.separation / 2 - L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := by
    rw [← mul_div_assoc, ← mul_div_assoc, mul_two, ← sub_sub, ← ENNReal.mul_div_right_comm,
      ← ENNReal.mul_div_right_comm, mul_assoc, mul_assoc]
    congr 3
    rw [mul_comm]

open Filter Topology

section VolumeBallRatio

open scoped Topology NNReal
open Asymptotics Filter ENNReal EuclideanSpace

-- Credits to Bhavik Mehta for this <3 my original code is 92 lines long x)
private lemma aux_bhavik {d : ℝ} {ε : ℝ≥0∞} (hd : 0 ≤ d) (hε : 0 < ε) :
    ∃ k : ℝ, k ≥ 0 ∧ ∀ k' ≥ k, ENNReal.ofReal ((k' / (k' + 1)) ^ d) ∈ Set.Icc (1 - ε) (1 + ε) := by
  suffices Filter.Tendsto
      (fun k => (ENNReal.ofReal (1 - (k + 1)⁻¹) ^ d)) atTop (𝓝 (ENNReal.ofReal (1 - 0) ^ d)) by
    rw [ENNReal.tendsto_atTop ?ha] at this
    case ha => simp
    obtain ⟨k, hk⟩ := this ε hε
    refine ⟨max 0 k, by simp, ?_⟩
    simp only [ge_iff_le, max_le_iff, and_imp]
    intro k' hk₀ hk₁
    have := hk k' hk₁
    rwa [sub_zero, ofReal_one, one_rpow, ←one_div, one_sub_div, add_sub_cancel_right,
      ENNReal.ofReal_rpow_of_nonneg] at this
    · positivity
    · positivity
    · positivity
  refine Tendsto.ennrpow_const d (tendsto_ofReal (Tendsto.const_sub 1 ?_))
  exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)

private lemma aux_bhavik' {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ k : ℝ, k ≥ 0 ∧ ∀ k' ≥ k, ENNReal.ofReal ((k' / (k' + 1)) ^ d) ∈ Set.Icc (1 - ε) (1 + ε) := by
  simpa using aux_bhavik (d := d) (Nat.cast_nonneg _) hε

theorem volume_ball_ratio_tendsto_nhds_one {C : ℝ} (hd : 0 < d) (hC : 0 ≤ C) :
    Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))) atTop (𝓝 1) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rcases le_iff_eq_or_lt.mp hC with (rfl | hC)
  · simp_rw [add_zero]
    apply Tendsto.congr' (f₁ := 1) ?_ tendsto_const_nhds
    rw [EventuallyEq, eventually_atTop]
    use 1
    intro b hb
    rw [ENNReal.div_self, Pi.one_apply]
    · exact (volume_ball_pos _ (by linarith)).ne.symm
    · exact (volume_ball_lt_top _).ne
  · have (R : ℝ) (hR : 0 ≤ R) : volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
          = ENNReal.ofReal (R ^ d / (R + C) ^ d) := by
      rw [volume_ball, volume_ball, Fintype.card_fin, ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul,
        ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_div_of_pos, mul_div_mul_right]
      <;> positivity
    rw [ENNReal.tendsto_atTop (by decide)]
    intro ε hε
    obtain ⟨k, ⟨hk₁, hk₂⟩⟩ := aux_bhavik' (d := d) hε
    use k * C
    intro n hn
    rw [this _ ((by positivity : 0 ≤ k * C).trans hn)]
    convert hk₂ (n / C) ((le_div_iff₀ hC).mpr hn)
    rw [div_add_one, div_div_div_cancel_right₀, div_pow]
    · positivity
    · positivity

theorem volume_ball_ratio_tendsto_nhds_one'
    {d : ℕ} {C C' : ℝ} (hd : 0 < d) (hC : 0 ≤ C) (hC' : 0 ≤ C') :
      Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) atTop (𝓝 1) := by
  -- I love ENNReal (I don't)
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  apply Tendsto.congr' (f₁ := fun R ↦
    volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))
        / (volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
          / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))))
  · rw [EventuallyEq, eventually_atTop]
    use 1
    intro R hR
    have hR' : 0 < R := by linarith
    rw [ENNReal.div_div_div_cancel_left]
    · exact (volume_ball_pos _ hR').ne.symm
    · exact (volume_ball_lt_top _).ne
    · exact (volume_ball_lt_top _).ne
  · convert ENNReal.Tendsto.div (volume_ball_ratio_tendsto_nhds_one hd hC') ?_
      (volume_ball_ratio_tendsto_nhds_one hd hC) ?_ <;> simp

theorem Filter.map_add_atTop_eq' {β : Type*} {f : ℝ → β} (C : ℝ) (α : Filter β) :
    Tendsto f atTop α ↔ Tendsto (fun x ↦ f (x + C)) atTop α := by
  constructor <;> intro hf
  · apply tendsto_map'_iff.mp
    convert hf
    rw [map_atTop_eq_of_gc (fun x ↦ x - C) 0 ?_ ?_ ?_]
    · exact Monotone.add_const (fun _ _ a ↦ a) _
    · simp [le_sub_iff_add_le]
    · simp [sub_add_cancel]
  · convert tendsto_map'_iff.mpr hf using 1
    rw [map_atTop_eq_of_gc (fun x ↦ x - C) 0 ?_ ?_ ?_]
    · exact Monotone.add_const (fun _ _ a ↦ a) _
    · simp [le_sub_iff_add_le]
    · simp [sub_add_cancel]

theorem volume_ball_ratio_tendsto_nhds_one'' {d : ℕ} {C C' : ℝ} (hd : 0 < d) :
    Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) atTop (𝓝 1) := by
  apply (Filter.map_add_atTop_eq' (max (-C) (-C')) _).mpr
  simp_rw [add_assoc]
  convert volume_ball_ratio_tendsto_nhds_one' hd ?_ ?_
  · trans (-C) + C
    · linarith
    · gcongr; simp
  · trans (-C') + C'
    · linarith
    · gcongr; simp

end VolumeBallRatio

section DensityEqFdDensity

variable
  {d : ℕ} {S : PeriodicSpherePacking d}
  {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)

private lemma PeriodicSpherePacking.tendsto_finiteDensity
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    Tendsto S.finiteDensity atTop
      (𝓝 (S.numReps * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)))) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ ?_
      (aux_big_ge b · hL hd) (aux_big_le b · hL hd)
  · rw [show ∀ a : ENNReal, 𝓝 a = 𝓝 (a * 1) by intro; rw [mul_one]]
    apply ENNReal.Tendsto.const_mul
    · simp_rw [sub_sub, sub_eq_add_neg]
      convert volume_ball_ratio_tendsto_nhds_one'' hd (C := -(S.separation / 2 + L * 2))
      rw [add_zero]
    · left
      exact one_ne_zero
  · rw [show ∀ a : ENNReal, 𝓝 a = 𝓝 (a * 1) by intro; rw [mul_one]]
    apply ENNReal.Tendsto.const_mul
    · simp_rw [add_assoc]
      convert volume_ball_ratio_tendsto_nhds_one'' hd (C := S.separation / 2 + L * 2)
      rw [add_zero]
    · left
      exact one_ne_zero

theorem PeriodicSpherePacking.density_eq
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    S.density
      = S.numReps * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
  limsSup_eq_of_le_nhds (S.tendsto_finiteDensity b hL hd)

end DensityEqFdDensity

section ConstantEqNormalizedConstant

theorem periodic_constant_eq_periodic_constant_normalized (hd : 0 < d) :
    PeriodicSpherePackingConstant d = ⨆ (S : PeriodicSpherePacking d) (_ : S.separation = 1),
    S.density := by
  -- Argument almost identical to `constant_eq_constant_normalized`, courtesy Gareth
  rw [iSup_subtype', PeriodicSpherePackingConstant]
  apply le_antisymm
  · apply iSup_le
    intro S
    have h := inv_mul_cancel₀ S.separation_pos.ne.symm
    have := le_iSup (fun x : { x : PeriodicSpherePacking d // x.separation = 1 } ↦ x.val.density)
        ⟨S.scale (inv_pos.mpr S.separation_pos), h⟩
    rw [← scale_density hd]
    · exact this
    · rw [inv_pos]
      exact S.separation_pos
  · apply iSup_le
    intro ⟨S, _⟩
    simp only
    exact le_iSup_iff.mpr fun b a ↦ a S

end ConstantEqNormalizedConstant

section Disjoint_Covering_of_Centers

theorem PeriodicSpherePacking.unique_covers_of_centers (S : PeriodicSpherePacking d) -- (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} -- (hD_isBounded : IsBounded D)
  (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) -- (hD_measurable : MeasurableSet D)
  :
  ∀ x : S.centers, ∃! g : S.lattice, (g +ᵥ x : EuclideanSpace ℝ (Fin d)) ∈ S.centers ∩ D := by
  intro x
  obtain ⟨g, hg₁, hg₂⟩ := hD_unique_covers (x : EuclideanSpace ℝ (Fin d))
  use g
  simp only [Set.mem_inter_iff, Subtype.coe_prop, true_and, Subtype.forall] at hg₁ hg₂ ⊢
  constructor
  · exact hg₁
  · intro a ha hmem
    exact hg₂ a ha hmem

theorem PeriodicSpherePacking.centers_union_over_lattice (S : PeriodicSpherePacking d)
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
    S.centers = ⋃ (g : S.lattice), (g +ᵥ S.centers ∩ D) := by
  ext x
  simp only [Set.mem_iUnion, Subtype.exists]
  constructor
  · intro hx
    obtain ⟨g, hg₁, _⟩ := S.unique_covers_of_centers hD_unique_covers ⟨x, hx⟩
    use -g
    simp only [neg_mem_iff, SetLike.coe_mem]
    obtain ⟨hy₁, hy₂⟩ := hg₁
    have : ∃ y : D, ↑y = g +ᵥ x := by use ⟨g +ᵥ x, hy₂⟩
    obtain ⟨y, hy⟩ := this
    suffices x = -g +ᵥ (y : EuclideanSpace ℝ (Fin d)) by
      rw [this]
      have hy' := Subtype.coe_prop y
      use True.intro -- so weird
      refine Set.vadd_mem_vadd_set ?h.intro.intro.a
      simp only [Set.mem_inter_iff, hy', and_true]
      rw [hy]
      -- Idea: closure under additive action
      exact hy₁
    rw [hy, neg_vadd_vadd]
  · intro hexa
    obtain ⟨g, hg₁, hg₂⟩ := hexa
    rw [Set.vadd_set_inter, Set.mem_inter_iff] at hg₂
    obtain ⟨hg₂, _⟩ := hg₂
    -- Idea: x = g +ᵥ y for some y in the set of centers
    -- Then apply closure under action
    obtain ⟨y, hy₁, hy₂⟩ := hg₂
    rw [← hy₂]
    exact S.lattice_action hg₁ hy₁

-- This is true but unnecessary (for now). What's more important is expressing it as a disjoint
-- union over points in X / Λ = X ∩ D of translates of the lattice by points in X / Λ = X ∩ D or
-- something like that, because that's what's needed for `tsum_finset_bUnion_disjoint`.
-- theorem PeriodicSpherePacking.translates_disjoint (S : PeriodicSpherePacking d) -- (hd : 0 < d)
-- {D : Set (EuclideanSpace ℝ (Fin d))} -- (hD_isBounded : IsBounded D)
-- (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) -- (hD_measurable : MeasurableSet D)
-- : Set.Pairwise ⊤ (Disjoint on (fun (g : S.lattice) => g +ᵥ S.centers ∩ D)) -- why the error?
-- -- True
-- := by
-- intro x hx y hy hxy
-- obtain ⟨g, hg₁, hg₂⟩ := hD_unique_covers x
-- specialize hg₂ y
-- simp only at hg₂
-- simp only [Set.disjoint_iff_inter_eq_empty]
-- ext z
-- simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
-- intro hz₁ hz₂
-- sorry

-- Can we use some sort of orbit disjointedness result and factor through the equivalence between
-- the `Quotient` and `S.centers ∩ D`?

end Disjoint_Covering_of_Centers

section Fundamental_Domains_in_terms_of_Basis

open Submodule

variable (S : PeriodicSpherePacking d) (b : Basis (Fin d) ℤ S.lattice)

-- I include the following because some lemmas in `PeriodicPacking` have them as assumptions, and
-- I'd like to replace all instances of `D` with `fundamentalDomain (b.ofZLatticeBasis ℝ _)` and
-- the assumptions on `D` with the following lemmas.

-- Note that we have `ZSpan.fundamentalDomain_isBounded`. We can use this to prove the following,
-- which is necessary for `PeriodicSpherePacking.density_eq`.
theorem PeriodicSpherePacking.exists_bound_on_fundamental_domain :
  ∃ L : ℝ, ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L :=
  isBounded_iff_forall_norm_le.1 (fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ S.lattice b))

-- Note that we have `ZSpan.exist_unique_vadd_mem_fundamentalDomain`. We can use this to prove the
-- following.
theorem PeriodicSpherePacking.fundamental_domain_unique_covers :
   ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _) := by
  have : S.lattice = span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) :=
    Eq.symm (Basis.ofZLatticeBasis_span ℝ S.lattice b)
  intro x
  -- The `g` we need should be the negative of the floor of `x`, but we can obtain it from the
  -- existing library result.
  obtain ⟨g, hg₁, hg₂⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
  have hg_mem : ↑g ∈ S.lattice := by simp only [this, SetLike.coe_mem]
  use ⟨↑g, hg_mem⟩
  constructor
  · exact hg₁
  · intro y
    have hy_mem : ↑y ∈ (span ℤ (Set.range ⇑(Basis.ofZLatticeBasis ℝ S.lattice b))).toAddSubgroup :=
      by simp only [← this, SetLike.coe_mem]
    intro hy
    simp only at hg₂ ⊢
    specialize hg₂ ⟨y, hy_mem⟩ hy
    refine SetCoe.ext ?h.right.a
    have heq : ↑y = (g : EuclideanSpace ℝ (Fin d)) := by rw [← hg₂]
    exact heq

-- Note that we already have `ZSpan.fundamentalDomain_measurableSet`. Use
-- `fundamentalDomain_measurableSet (Basis.ofZLatticeBasis ℝ S.lattice b)` to say that our desired
-- fundamental domain is measurable.

end Fundamental_Domains_in_terms_of_Basis

section Periodic_Density_Formula

noncomputable instance HDivENNReal : HDiv NNReal ENNReal ENNReal where
  hDiv := fun x y => x / y
noncomputable instance HMulENNReal : HMul NNReal ENNReal ENNReal where
  hMul := fun x y => x * y

noncomputable def ZLattice.basis_index_equiv (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    (Module.Free.ChooseBasisIndex ℤ Λ) ≃ (Fin d) := by
  refine Fintype.equivFinOfCardEq ?h
  rw [← Module.finrank_eq_card_chooseBasisIndex,
      ZLattice.rank ℝ Λ,
      finrank_euclideanSpace, Fintype.card_fin]

noncomputable def PeriodicSpherePacking.basis_index_equiv (P : PeriodicSpherePacking d) :
  (Module.Free.ChooseBasisIndex ℤ ↥P.lattice) ≃ (Fin d) := ZLattice.basis_index_equiv P.lattice

/- Here's a version of `PeriodicSpherePacking.density_eq` that
1. does not require the `hL` hypothesis that the original one does
2. uses `ZLattice.covolume` instead of the `volume` of a basis-dependent `fundamentalDomain`
-/
@[simp]
theorem PeriodicSpherePacking.density_eq'
  (S : PeriodicSpherePacking d) (hd : 0 < d) : S.density =
  (ENat.toENNReal (S.numReps : ENat)) *
  volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) /
  Real.toNNReal (ZLattice.covolume S.lattice) := by
  let b : Basis (Fin d) ℤ ↥S.lattice := ((ZLattice.module_free ℝ S.lattice).chooseBasis).reindex
    (S.basis_index_equiv)
  obtain ⟨L, hL⟩ := S.exists_bound_on_fundamental_domain b
  rw [Real.toNNReal_of_nonneg (LT.lt.le (ZLattice.covolume_pos S.lattice volume))]
  rw [S.density_eq b hL hd]
  simp only [ENat.toENNReal_coe]
  apply congrArg _ _
  refine (ENNReal.toReal_eq_toReal_iff' ?hx ?hy).mp ?_
  · rw [← lt_top_iff_ne_top]
    letI := fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ S.lattice b)
    exact IsBounded.measure_lt_top this
  · exact ENNReal.coe_ne_top
  · rw [ENNReal.coe_toReal, NNReal.coe_mk]
    refine Eq.symm (ZLattice.covolume_eq_measure_fundamentalDomain S.lattice volume ?h)
    exact ZLattice.isAddFundamentalDomain b volume

theorem PeriodicSpherePacking'.density_eq'' (S : PeriodicSpherePacking' d) :
    S.density' = (S.fundDom).card * vol (B d 0 (S.separation / 2)) / covolume S.lattice := by
  sorry

end Periodic_Density_Formula

section Empty_Centers

theorem PeriodicSpherePacking.density_of_centers_empty (S : PeriodicSpherePacking d) (hd : 0 < d)
  [instEmpty : IsEmpty S.centers] : S.density = 0 := by
  -- Idea: Use formula
  -- (We are using `IsEmpty` in order to do cases on `isEmpty_or_nonempty` in proofs)
  rw [S.density_eq' hd]
  let b := ((ZLattice.module_free ℝ S.lattice).chooseBasis).reindex (S.basis_index_equiv)
  let D := fundamentalDomain (Basis.ofZLatticeBasis ℝ S.lattice b)
  have hD_isBounded : IsBounded D :=
    fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ S.lattice b)
  have hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D :=
    S.fundamental_domain_unique_covers b
  rw [← S.card_centers_inter_isFundamentalDomain D hD_isBounded hD_unique_covers hd]
  simp only [Set.toFinset_card, ENat.toENNReal_coe, ENNReal.div_eq_zero_iff, mul_eq_zero,
    Nat.cast_eq_zero, ENNReal.coe_ne_top, or_false]
  left
  letI instFintype := @Fintype.ofFinite _ <| aux4 S D hD_isBounded hd
  rw [Fintype.card_eq_zero_iff]
  refine Set.isEmpty_coe_sort.mpr ?h.a
  suffices S.centers = ∅ by
    rw [this]
    exact Set.empty_inter D
  exact Set.isEmpty_coe_sort.mp instEmpty

theorem SpherePacking.density_of_centers_empty (S : SpherePacking d) (hd : 0 < d)
  [instEmpty : IsEmpty S.centers] : S.density = 0 := by
  -- Idea: construct a periodic sphere packing with some lattice and the same set of centres
  -- Show that its toSpherePacking is the same as S
  -- Then use formula
  let b : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  let Λ := Submodule.span ℤ (Set.range b)
  let P : PeriodicSpherePacking d := {
    centers := S.centers
    separation := S.separation
    separation_pos := S.separation_pos
    centers_dist := S.centers_dist
    lattice := Λ
    lattice_action := by
      simp only
      intros x y _ hy
      rw [Set.isEmpty_coe_sort.mp instEmpty, Set.mem_empty_iff_false] at hy
      exfalso
      exact hy
    lattice_discrete := inferInstance
    lattice_isZLattice := inferInstance
  }
  have h₁ : P.toSpherePacking = S := rfl
  rw [← h₁]
  exact P.density_of_centers_empty hd

end Empty_Centers

section Periodic_Constant_Eq_Constant

theorem periodic_constant_eq_constant (hd : 0 < d) :
    PeriodicSpherePackingConstant d = SpherePackingConstant d := by
  sorry

end Periodic_Constant_Eq_Constant
end finiteDensity_limit

end theorem_2_2
