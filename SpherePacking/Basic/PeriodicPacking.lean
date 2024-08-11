import Mathlib.Data.Set.Card
import SpherePacking.Basic.E8
import SpherePacking.Basic.SpherePacking
import SpherePacking.ForMathlib.Zlattice

/- In this file, we establish results about density of periodic packings. This roughly corresponds
to Section 2.2, "Bounds on Finite Density of Periodic Packing". -/

/-#
TODO: Write the docstring properly lol

Vocabulary:

* `Quotient S.addAction.orbitRel`: the type of *representatives* of S.centers ⧸ S.lattice

TODO:


-/

open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric Zspan Bornology

section aux_lemmas

variable {d : ℕ} (S : PeriodicSpherePacking d)
  (D : Set (EuclideanSpace ℝ (Fin d))) (hD_fd : IsAddFundamentalDomain S.lattice D)
  (hD_isBounded : IsBounded D)

#check parallelepiped
#check Zspan.fundamentalDomain
#check Zspan.fundamentalDomain_ae_parallelepiped
#check Zspan.volume_fundamentalDomain
#check measure_congr

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

section main_theorem
variable {d : ℕ} (S : PeriodicSpherePacking d)
  (D : Set (EuclideanSpace ℝ (Fin d)))
  (hD_isBounded : IsBounded D)
  (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)

-- TODO: rename
noncomputable def PeriodicSpherePacking.numReps : ℕ :=
  Fintype.card (Quotient S.addAction.orbitRel)

#check fract_zspan_add
theorem PeriodicSpherePacking.card_centers_inter_fundamentalDomain (hd : 0 < d)
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
    haveI := @Fintype.ofFinite _ <| aux4 S D hD_isBounded hd
    (S.centers ∩ D).toFinset.card = S.numReps := by
  rw [numReps]
  convert Finset.card_eq_of_equiv_fintype ?_
  simpa [Set.mem_toFinset] using (S.addActionOrbitRelEquiv D hD_unique_covers).symm

open Pointwise Filter

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

example
    {ι : Type*} (b : Basis ι ℝ (EuclideanSpace ℝ (Fin d)))
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain b, ‖x‖ ≤ L) (R : ℝ) : false := by
  have := aux S b hL R
  have := Set.inter_subset_inter_right S.centers this
  rw [Set.biUnion_eq_iUnion, Set.inter_iUnion] at this
  have := Set.encard_mono this
  rw [S.card_centers_inter_fundamentalDomain] at this

-- Theorem 2.3, LB
example
    {ι : Type*} (b : Basis ι ℤ S.lattice)
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZlatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) (hR : L < R) :
    S.numReps • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R - L)).encard
      ≤ (↑S.centers ∩ ball 0 R).encard := by
  sorry

-- Theorem 2.3, UB
example
    {ι : Type*} (b : Basis ι ℤ S.lattice)
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZlatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) (hR : L < R) :
    (↑S.centers ∩ ball 0 R).encard
      ≤ S.numReps • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + L)).encard := by
  sorry
