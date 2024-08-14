import Mathlib.Data.Set.Card
import SpherePacking.Basic.SpherePacking

import SpherePacking.ForMathlib.Cardinal
import SpherePacking.ForMathlib.Encard
import SpherePacking.ForMathlib.Zlattice
import SpherePacking.ForMathlib.Bornology

/- In this file, we establish results about density of periodic packings. This roughly corresponds
to Section 2.2, "Bounds on Finite Density of Periodic Packing". -/

/-#
TODO:

* Write the docstrings properly
* Rename lemmas

Vocabulary:

* `Quotient S.addAction.orbitRel`: the type of *representatives* of S.centers ⧸ S.lattice

-/

open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric Zspan Bornology

section aux_lemmas

variable {d : ℕ} (S : PeriodicSpherePacking d)
  (D : Set (EuclideanSpace ℝ (Fin d))) (hD_fd : IsAddFundamentalDomain S.lattice D)
  (hD_isBounded : IsBounded D)

lemma aux1 : IsBounded (⋃ x ∈ S.centers ∩ D, ball x (S.separation / 2)) := by
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
  clear D hD_fd hD_isBounded S
  wlog h_countable : s.Countable with h_wlog
  · by_contra! h_finite
    rw [Set.Countable, ← Cardinal.mk_le_aleph0_iff, not_le] at h_countable
    -- Brilliant(!!) idea by Etienne Marion on Zulip
    -- If s is uncountable, then we can argue on a countable subset!
    obtain ⟨t, ⟨ht_subset, ht_aleph0⟩⟩ := Cardinal.le_mk_iff_exists_subset.mp h_countable.le
    have ht_infinite : Infinite t := Cardinal.aleph0_le_mk_iff.mp ht_aleph0.symm.le
    have ht_countable := Cardinal.mk_le_aleph0_iff.mp ht_aleph0.le
    specialize @h_wlog d _ _ t f c hc _ _ ?_ ?_ ?_ ?_ ht_countable
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
    · have h_le := tsum_mono (f := fun _ ↦ c) (g := fun (x : s) ↦ volume (f x)) ?_ ?_ ?_
      · have h₁ := (ENNReal.tsum_const_eq' _ _ ▸ h_le).trans h_volume'
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

lemma aux4 (hd : 0 < d) : Finite ↑(S.centers ∩ D) := by
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
    Finite ↑(S.centers ∩ fundamentalDomain (b.ofZlatticeBasis ℝ _)) :=
  aux4 S _ (Zspan.fundamentalDomain_isBounded _) hd

open scoped Pointwise in
lemma aux4''
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) (hd : 0 < d) (v : EuclideanSpace ℝ (Fin d)) :
    Finite ↑(S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZlatticeBasis ℝ _))) :=
  aux4 S _ (Bornology.isBounded_vadd_set _ _ <| Zspan.fundamentalDomain_isBounded _) hd

end aux_lemmas

section instances
variable {d : ℕ} (S : PeriodicSpherePacking d)
open scoped Pointwise

-- TODO: rename + move
theorem PeriodicSpherePacking.fract_centers
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) (s : S.centers) :
    fract (b.ofZlatticeBasis ℝ _) s.val ∈ S.centers := by
  have := (floor (b.ofZlatticeBasis ℝ _) s).prop
  simp_rw [S.basis_Z_span] at this
  rw [fract_apply, sub_eq_add_neg, add_comm]
  apply S.lattice_action (neg_mem this) s.prop

-- TODO: rename + move
theorem PeriodicSpherePacking.orbitRel_fract
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) (a : S.centers) :
    (S.addAction.orbitRel).Rel ⟨fract (b.ofZlatticeBasis ℝ _) a, S.fract_centers _ _⟩ a := by
  rw [AddAction.orbitRel_apply, AddAction.orbit, Set.mem_range]
  refine ⟨⟨-↑(floor (b.ofZlatticeBasis ℝ _) ↑a), ?_⟩, ?_⟩
  · apply neg_mem
    have := (floor (b.ofZlatticeBasis ℝ _) a.val).prop
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
      change (S.addAction.orbitRel).Rel ⟨u, hu⟩ ⟨v, hv⟩ at h
      rw [AddAction.orbitRel_apply, AddAction.orbit, Set.mem_range] at h
      obtain ⟨⟨y, hy⟩, hy'⟩ := h
      have : y + v = u := Subtype.ext_iff.mp hy'
      subst this
      have hv' := (Classical.choose_spec (hD_unique_covers v)).right
      simp at hv'
      simp_rw [Subtype.forall, AddSubmonoid.mk_vadd, vadd_eq_add, Subtype.mk.injEq, ← add_assoc]
      congr 1
      convert Subtype.ext_iff.mp (hv' _ ?_ ?_)
      · exact add_mem (SetLike.coe_mem _) hy
      · rw [add_assoc]
        have := (Classical.choose_spec (hD_unique_covers (y + v))).left
        -- ew.
        change (Classical.choose _ : S.lattice).val + (y + v) ∈ D at this
        convert this using 5 with x
        simp [← add_assoc]
  invFun := fun ⟨x, hx⟩ ↦ ⟦⟨x, hx.left⟩⟧
  left_inv := by
    apply Quotient.ind
    intro ⟨a, ha⟩
    simp_rw [Quotient.lift_mk, Quotient.eq]
    change (S.addAction.orbitRel).Rel _ _
    simp_rw [AddAction.orbitRel_apply, AddAction.orbit, Set.mem_range]
    simp [addAction_vadd]
  right_inv := by
    intro ⟨x, hx⟩
    simp_rw [Quotient.lift_mk, Subtype.mk.injEq, add_left_eq_self]
    obtain ⟨g, ⟨hg, hg'⟩⟩ := hD_unique_covers x
    trans g.val <;> norm_cast
    · apply hg'
      exact (Classical.choose_spec (hD_unique_covers x)).left
    · apply (hg' 0 ?_).symm
      simpa using hx.right

noncomputable def PeriodicSpherePacking.addActionOrbitRelEquiv'
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) :
    Quotient S.addAction.orbitRel ≃ ↑(S.centers ∩ (fundamentalDomain (b.ofZlatticeBasis ℝ _))) := by
  refine S.addActionOrbitRelEquiv _ ?_
  intro x
  obtain ⟨v, ⟨hv, hv'⟩⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZlatticeBasis ℝ _) x
  use ⟨v.val, ?_⟩, ?_, ?_
  · apply Set.mem_of_subset_of_mem ?_ v.prop
    rw [← Submodule.coe_toAddSubgroup, Basis.ofZlatticeBasis_span]
  · simp only at hv' ⊢
    convert hv using 1
  · intro s hs
    rw [← hv' ⟨s, ?_⟩ hs]
    apply Set.mem_of_subset_of_mem _ s.prop
    rw [← Submodule.coe_toAddSubgroup, Basis.ofZlatticeBasis_span]

noncomputable def PeriodicSpherePacking.addActionOrbitRelEquiv''
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) (v : EuclideanSpace ℝ (Fin d)) :
    Quotient S.addAction.orbitRel ≃
      ↑(S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZlatticeBasis ℝ _))) := by
  apply (S.addActionOrbitRelEquiv' b).trans
  exact {
    toFun := fun ⟨u, ⟨hu_centers, _⟩⟩ ↦ by
      use u - floor (b.ofZlatticeBasis ℝ _) (u - v)
      constructor
      · rw [sub_eq_neg_add]
        apply S.lattice_action ?_ hu_centers
        apply AddSubgroup.neg_mem
        exact (mem_basis_Z_span ..).mp $ Submodule.coe_mem _
      · rw [Set.mem_vadd_set]
        use fract (b.ofZlatticeBasis ℝ _) (u - v), fract_mem_fundamentalDomain _ _, ?_
        rw [fract, vadd_eq_add]
        abel
    invFun := fun ⟨u, ⟨hu_centers, _⟩⟩ ↦ by
      use fract (b.ofZlatticeBasis ℝ _) u
      constructor
      · rw [fract, sub_eq_neg_add]
        apply S.lattice_action ?_ hu_centers
        apply AddSubgroup.neg_mem
        exact (mem_basis_Z_span ..).mp $ Submodule.coe_mem _
      · exact fract_mem_fundamentalDomain _ _
    left_inv := fun ⟨u, ⟨hu_centers, hu_fd⟩⟩ ↦ by
      simp_rw [Subtype.mk.injEq]
      rw [sub_eq_add_neg, fract_add_zspan]
      · exact fract_eq_self.mpr hu_fd
      · apply neg_mem
        exact Submodule.coe_mem _
    right_inv := fun ⟨u, ⟨hu_centers, hu_fd⟩⟩ ↦ by
      simp_rw [Subtype.mk.injEq]
      rw [← EmbeddingLike.apply_eq_iff_eq (b.ofZlatticeBasis ℝ _).repr, map_sub]
      have hu_fd' : u - v ∈ fundamentalDomain (b.ofZlatticeBasis ℝ _) := by
        rwa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] at hu_fd
      ext i
      set b' := b.ofZlatticeBasis ℝ _
      calc
        _ = b'.repr (fract b' u) i - b'.repr (floor b' (u - floor b' u - v)) i := by rfl
        _ = b'.repr (fract b' u) i - b'.repr (floor b' (u - v - floor b' u)) i := by abel_nf
        _ = b'.repr u i - ⌊b'.repr u i⌋ - (⌊b'.repr (u - v) i⌋ - ⌊b'.repr u i⌋) := by simp
        _ = b'.repr u i - ⌊b'.repr (u - v) i⌋ := by abel_nf
        _ = b'.repr u i := by
          rw [sub_eq_self, ← repr_floor_apply, (Zspan.floor_eq_zero ..).mp hu_fd']
          simp
  }

instance (S : PeriodicSpherePacking 0) : Subsingleton S.centers := inferInstance
instance (S : PeriodicSpherePacking 0) : Finite S.centers := inferInstance

noncomputable instance PeriodicSpherePacking.finiteOrbitRelQuotient :
    Finite (Quotient S.addAction.orbitRel) :=
  -- We choose an arbitrary ℤ-basis of S.lattice
  let b : Basis _ ℤ S.lattice := (Zlattice.module_free ℝ S.lattice).chooseBasis
  if hd : 0 < d then
    Finite.of_equiv (h := aux4' S b hd) (S.addActionOrbitRelEquiv' b).symm
  else
    have hd : d = 0 := Nat.eq_zero_of_not_pos hd
    have : Finite S.centers := by subst hd; infer_instance
    inferInstance

noncomputable instance : Fintype (Quotient S.addAction.orbitRel) :=
  Fintype.ofFinite _

end instances

section theorem_2_3
open scoped Pointwise
variable {d : ℕ} (S : PeriodicSpherePacking d)
  (D : Set (EuclideanSpace ℝ (Fin d)))
  (hD_isBounded : IsBounded D)
  (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)

-- TODO: rename
noncomputable def PeriodicSpherePacking.numReps : ℕ :=
  Fintype.card (Quotient S.addAction.orbitRel)

theorem PeriodicSpherePacking.card_centers_inter_isFundamentalDomain (hd : 0 < d)
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
    haveI := @Fintype.ofFinite _ <| aux4 S D hD_isBounded hd
    (S.centers ∩ D).toFinset.card = S.numReps := by
  rw [numReps]
  convert Finset.card_eq_of_equiv_fintype ?_
  simpa [Set.mem_toFinset] using (S.addActionOrbitRelEquiv D hD_unique_covers).symm

theorem PeriodicSpherePacking.encard_centers_inter_isFundamentalDomain (hd : 0 < d)
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
    (S.centers ∩ D).encard = S.numReps := by
  rw [← S.card_centers_inter_isFundamentalDomain D hD_isBounded hd hD_unique_covers]
  convert Set.encard_eq_coe_toFinset_card _

theorem PeriodicSpherePacking.card_centers_inter_fundamentalDomain (hd : 0 < d)
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) :
    haveI := @Fintype.ofFinite _ <| aux4' S b hd
    (S.centers ∩ (fundamentalDomain (b.ofZlatticeBasis ℝ _))).toFinset.card = S.numReps := by
  rw [numReps]
  convert Finset.card_eq_of_equiv_fintype ?_
  simpa [Set.mem_toFinset] using (S.addActionOrbitRelEquiv' b).symm

theorem PeriodicSpherePacking.encard_centers_inter_fundamentalDomain (hd : 0 < d)
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) :
    (S.centers ∩ (fundamentalDomain (b.ofZlatticeBasis ℝ _))).encard = S.numReps := by
  rw [← S.card_centers_inter_fundamentalDomain hd b]
  convert Set.encard_eq_coe_toFinset_card _

theorem PeriodicSpherePacking.card_centers_inter_vadd_fundamentalDomain (hd : 0 < d)
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) (v : EuclideanSpace ℝ (Fin d)) :
    haveI := @Fintype.ofFinite _ <| aux4'' S b hd v
    (S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZlatticeBasis ℝ _))).toFinset.card = S.numReps := by
  rw [numReps]
  convert Finset.card_eq_of_equiv_fintype ?_
  simpa [Set.mem_toFinset] using (S.addActionOrbitRelEquiv'' b _).symm

theorem PeriodicSpherePacking.encard_centers_inter_vadd_fundamentalDomain (hd : 0 < d)
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) (v : EuclideanSpace ℝ (Fin d)) :
    (S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZlatticeBasis ℝ _))).encard = S.numReps := by
  rw [← S.card_centers_inter_vadd_fundamentalDomain hd b]
  convert Set.encard_eq_coe_toFinset_card _

theorem aux
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
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZlatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) :
    (↑S.centers ∩ ball 0 R).encard ≥
      S.numReps • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R - L)).encard := by
  have := aux S (b.ofZlatticeBasis ℝ _) hL R
  have := Set.inter_subset_inter_right S.centers this
  rw [Set.biUnion_eq_iUnion, Set.inter_iUnion] at this
  have := Set.encard_mono this
  rw [Set.encard_iUnion_of_pairwiseDisjoint] at this
  simp_rw [S.encard_centers_inter_vadd_fundamentalDomain hd] at this
  · convert this.ge
    rw [nsmul_eq_mul, ENat.tsum_const_eq', mul_comm]
  · intro ⟨x, hx⟩ _ ⟨y, hy⟩ _ hxy
    simp only [Set.disjoint_iff, Set.subset_empty_iff]
    ext u
    rw [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro ⟨_, hux⟩ ⟨_, huy⟩
    obtain ⟨w, hw, hw_unique⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZlatticeBasis ℝ _) u
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] at hux huy
    have hx := hw_unique ⟨-x, ?_⟩ ?_
    have hy := hw_unique ⟨-y, ?_⟩ ?_
    · apply hxy
      rw [Subtype.ext_iff, ← neg_inj]
      exact Subtype.ext_iff.mp (hx.trans hy.symm)
    · apply neg_mem
      apply Set.mem_of_subset_of_mem (s₁ := S.lattice)
      · rw [S.basis_Z_span]
        rfl
      · exact hy.left
    · simp_rw [AddSubmonoid.mk_vadd, vadd_eq_add, neg_add_eq_sub]
      exact huy
    · apply neg_mem
      apply Set.mem_of_subset_of_mem (s₁ := S.lattice)
      · rw [S.basis_Z_span]
        rfl
      · exact hx.left
    · simp_rw [AddSubmonoid.mk_vadd, vadd_eq_add, neg_add_eq_sub]
      exact hux

theorem aux'
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice)
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZlatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) :
    ball 0 R
      ⊆ ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + L),
        x +ᵥ (fundamentalDomain (b.ofZlatticeBasis ℝ _) : Set (EuclideanSpace ℝ (Fin d))) := by
  intro x hx
  simp only [Set.mem_iUnion, exists_prop]
  use floor (b.ofZlatticeBasis ℝ _) x
  constructor
  · constructor
    · rw [SetLike.mem_coe, ← S.mem_basis_Z_span b]
      exact Submodule.coe_mem _
    · have : floor (b.ofZlatticeBasis ℝ _) x = x - fract (b.ofZlatticeBasis ℝ _) x := by
        rw [fract]
        abel
      rw [mem_ball_zero_iff] at hx ⊢
      calc
        _ = ‖x - fract (b.ofZlatticeBasis ℝ _) x‖ := congrArg _ this
        _ ≤ ‖x‖ + ‖fract (b.ofZlatticeBasis ℝ _) x‖ := norm_sub_le _ _
        _ < R + L := add_lt_add_of_lt_of_le hx (hL _ (fract_mem_fundamentalDomain _ _))
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]
    exact fract_mem_fundamentalDomain (b.ofZlatticeBasis ℝ _) x

-- Theorem 2.3, upper bound - the proof is similar to lower bound
theorem PeriodicSpherePacking.aux_le
    (hd : 0 < d) {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice)
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZlatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) :
    (↑S.centers ∩ ball 0 R).encard
      ≤ S.numReps • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + L)).encard := by
  have := aux' S b hL R
  have := Set.inter_subset_inter_right S.centers this
  rw [Set.biUnion_eq_iUnion, Set.inter_iUnion] at this
  have := Set.encard_mono this
  rw [Set.encard_iUnion_of_pairwiseDisjoint] at this
  simp_rw [S.encard_centers_inter_vadd_fundamentalDomain hd] at this
  · convert this
    rw [nsmul_eq_mul, ENat.tsum_const_eq', mul_comm]
  · intro ⟨x, hx⟩ _ ⟨y, hy⟩ _ hxy
    simp only [Set.disjoint_iff, Set.subset_empty_iff]
    ext u
    rw [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro ⟨_, hux⟩ ⟨_, huy⟩
    obtain ⟨w, hw, hw_unique⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZlatticeBasis ℝ _) u
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] at hux huy
    have hx := hw_unique ⟨-x, ?_⟩ ?_
    have hy := hw_unique ⟨-y, ?_⟩ ?_
    · apply hxy
      rw [Subtype.ext_iff, ← neg_inj]
      exact Subtype.ext_iff.mp (hx.trans hy.symm)
    · apply neg_mem
      apply Set.mem_of_subset_of_mem (s₁ := S.lattice)
      · rw [S.basis_Z_span]
        rfl
      · exact hy.left
    · simp_rw [AddSubmonoid.mk_vadd, vadd_eq_add, neg_add_eq_sub]
      exact huy
    · apply neg_mem
      apply Set.mem_of_subset_of_mem (s₁ := S.lattice)
      · rw [S.basis_Z_span]
        rfl
      · exact hx.left
    · simp_rw [AddSubmonoid.mk_vadd, vadd_eq_add, neg_add_eq_sub]
      exact hux

end theorem_2_3

----------------------------------------------------

section theorem_2_2
open scoped Pointwise
variable {d : ℕ} (S : PeriodicSpherePacking d)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (D : Set (EuclideanSpace ℝ (Fin d)))
  -- (hD_fd : IsAddFundamentalDomain S.lattice D)

  -- this strengthens hD_fd.ae_covers
  -- It's not actually necessary but it'll make the proof much much more annoying
  (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)
  -- this strengthens hD_fd.nullMeasurableSet
  -- i think this is not necessary because `volume` isdefined as the outer measure on non-measurable
  -- sets, so if D is only null measurable we can just take that approximation
  (hD_measurable : MeasurableSet D)

  {L : ℝ} (hL : ∀ x ∈ D, ‖x‖ ≤ L) (R : ℝ)

/- In this section we prove Theorem 2.2 -/

private theorem hD_isAddFundamentalDomain : IsAddFundamentalDomain S.lattice D where
  nullMeasurableSet := hD_measurable.nullMeasurableSet
  ae_covers := Filter.eventually_of_forall fun x ↦ (hD_unique_covers x).exists
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

theorem aux7 :
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

-- Theorem 2.2, lower bound
theorem PeriodicSpherePacking.aux2_ge (hd : 0 < d)  :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≥ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - L)) / volume D := by
  rw [ge_iff_le, ENNReal.div_le_iff]
  · convert volume.mono <| aux7 S D hD_unique_covers hL R
    rw [OuterMeasure.measureOf_eq_coe, Measure.coe_toOuterMeasure]
    have : Countable ↑S.lattice := inferInstance
    have : Countable ↑(↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
      Set.Countable.mono (Set.inter_subset_left) this
    rw [Set.biUnion_eq_iUnion, measure_iUnion]
    · rw [tsum_congr fun i ↦ measure_vadd .., ENNReal.tsum_const_eq']
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

theorem aux8 :
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
theorem PeriodicSpherePacking.aux2_le (hd : 0 < d)  :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L)) / volume D := by
  rw [ENNReal.le_div_iff_mul_le]
  · convert volume.mono <| aux8 S D hD_unique_covers hL R
    rw [OuterMeasure.measureOf_eq_coe, Measure.coe_toOuterMeasure]
    have : Countable ↑S.lattice := inferInstance
    have : Countable ↑(↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
      Set.Countable.mono (Set.inter_subset_left) this
    rw [Set.biUnion_eq_iUnion, measure_iUnion]
    · rw [tsum_congr fun i ↦ measure_vadd .., ENNReal.tsum_const_eq']
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

open Zspan

variable
  {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice)
  {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZlatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ)

-- Theorem 2.2 lower bound, in terms of fundamental domain of Z-lattice
theorem PeriodicSpherePacking.aux2_ge' (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≥ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - L))
        / volume (fundamentalDomain (b.ofZlatticeBasis ℝ _)) := by
  refine S.aux2_ge _ ?_ (fundamentalDomain_measurableSet _) hL R hd
  intro x
  obtain ⟨⟨v, hv⟩, hv'⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZlatticeBasis ℝ _) x
  simp only [S.basis_Z_span, AddSubmonoid.mk_vadd] at hv hv' ⊢
  use ⟨v, hv⟩, hv'.left, ?_
  intro ⟨y, hy⟩ hy'
  have := hv'.right ⟨y, ?_⟩ hy'
  rwa [Subtype.ext_iff] at this ⊢
  rw [S.basis_Z_span]
  exact hy

-- Theorem 2.2 upper bound, in terms of fundamental domain of Z-lattice
theorem PeriodicSpherePacking.aux2_le' (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L))
        / volume (fundamentalDomain (b.ofZlatticeBasis ℝ _)) := by
  refine S.aux2_le _ ?_ (fundamentalDomain_measurableSet _) hL R hd
  intro x
  obtain ⟨⟨v, hv⟩, hv'⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZlatticeBasis ℝ _) x
  simp only [S.basis_Z_span, AddSubmonoid.mk_vadd] at hv hv' ⊢
  use ⟨v, hv⟩, hv'.left, ?_
  intro ⟨y, hy⟩ hy'
  have := hv'.right ⟨y, ?_⟩ hy'
  rwa [Subtype.ext_iff] at this ⊢
  rw [S.basis_Z_span]
  exact hy

section finiteDensity_limit

/- TODO: consider moving this section. -/

open MeasureTheory Measure Metric Zspan

variable
  {d : ℕ} {S : PeriodicSpherePacking d} (hd : 0 < d)
  {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice)
  {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZlatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ)

theorem aux_big_le :
    S.finiteDensity R ≤
      S.numReps
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZlatticeBasis ℝ _))
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
          / volume (fundamentalDomain (b.ofZlatticeBasis ℝ _)))
            * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    rw [nsmul_eq_mul]
    gcongr
    exact S.aux2_le' b hL _ hd
  _ = S.numReps
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZlatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := by
    rw [← mul_div_assoc, ← mul_div_assoc, mul_two, ← add_assoc, ← ENNReal.mul_div_right_comm,
      ← ENNReal.mul_div_right_comm, mul_assoc, mul_assoc]
    congr 3
    rw [mul_comm]

theorem aux_big_ge :
    S.finiteDensity R ≥
      S.numReps
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZlatticeBasis ℝ _))
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
          / volume (fundamentalDomain (b.ofZlatticeBasis ℝ _)))
            * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    rw [nsmul_eq_mul]
    gcongr
    exact S.aux2_ge' b hL _ hd
  _ = S.numReps
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZlatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - S.separation / 2 - L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := by
    rw [← mul_div_assoc, ← mul_div_assoc, mul_two, ← sub_sub, ← ENNReal.mul_div_right_comm,
      ← ENNReal.mul_div_right_comm, mul_assoc, mul_assoc]
    congr 3
    rw [mul_comm]

open Filter Topology

private lemma PeriodicSpherePacking.tendsto_finiteDensity : Tendsto S.finiteDensity atTop
    (𝓝 (S.numReps * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
      / volume (fundamentalDomain (b.ofZlatticeBasis ℝ _)))) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ ?_ (aux_big_ge hd b hL) (aux_big_le hd b hL)
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

theorem PeriodicSpherePacking.density_eq :
    S.density
      = (S.numReps * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (fundamentalDomain (b.ofZlatticeBasis ℝ _))) :=
  limsSup_eq_of_le_nhds (S.tendsto_finiteDensity hd b hL)

#print axioms PeriodicSpherePacking.density_eq
