import SpherePacking.Basic.SpherePacking
import SpherePacking.Basic.E8
import Mathlib.Data.Set.Card

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

variable {d : ℕ} (S : PeriodicSpherePacking d)

#check parallelepiped
#check Zspan.fundamentalDomain
#check Zspan.fundamentalDomain_ae_parallelepiped
#check Zspan.volume_fundamentalDomain
#check measure_congr

lemma aux1 {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) :
    IsBounded (⋃ x ∈ S.centers ∩ fundamentalDomain (b.ofZlatticeBasis ℝ _),
      ball x (S.separation / 2)) := by
  apply isBounded_iff_forall_norm_le.mpr
  obtain ⟨L, hL⟩ := isBounded_iff_forall_norm_le.mp
    <| fundamentalDomain_isBounded (b.ofZlatticeBasis ℝ _)
  use L + S.separation / 2
  intro x hx
  obtain ⟨y, s, hy, hy'⟩ := Set.mem_iUnion.mp hx
  rw [Set.mem_range, exists_prop] at hy
  obtain ⟨hy, rfl⟩ := hy
  rw [mem_ball, dist_eq_norm] at hy'
  specialize hL y hy.right
  exact (norm_le_norm_add_norm_sub' x y).trans (by gcongr)

lemma aux2 {ι : Type*} (b : Basis ι ℝ (EuclideanSpace ℝ (Fin d))) :
    Set.PairwiseDisjoint (S.centers ∩ fundamentalDomain b)
      (fun x ↦ ball x (S.separation / 2)) := by
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
  clear S
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

lemma aux4 {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) (hd : 0 < d) :
    Finite ↑(S.centers ∩ fundamentalDomain (b.ofZlatticeBasis ℝ _)) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  apply aux3 (c := volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))) ?_ ?_ (aux1 S b)
  · intros
    simp [Measure.addHaar_ball_center]
  · intro x hx y hy hxy
    apply ball_disjoint_ball
    simpa [add_halves] using S.centers_dist' _ _ hx.left hy.left hxy
  · apply volume_ball_pos
    linarith [S.separation_pos]
  · intros
    exact measurableSet_ball

-- TODO: rename + move
theorem PeriodicSpherePacking.fract_centers
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) (s : S.centers) :
    fract (b.ofZlatticeBasis ℝ _) s.val ∈ S.centers := by
  have := (floor (b.ofZlatticeBasis ℝ _) s).prop
  simp_rw [S.basis_Z_span] at this
  rw [fract_apply, sub_eq_add_neg, add_comm]
  apply S.lattice_action (Submodule.neg_mem _ this) s.prop

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
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) :
    Quotient S.addAction.orbitRel ≃ ↑(S.centers ∩ fundamentalDomain (b.ofZlatticeBasis ℝ _)) where
  toFun := by
    refine Quotient.lift ?_ ?_
    · intro s
      use fract (Basis.ofZlatticeBasis ℝ _ b) s, ?_
      · simp only [fractRestrict_apply, mem_fundamentalDomain, repr_fract_apply, Set.mem_Ico,
          Int.fract_nonneg, true_and]
        intro
        exact Int.fract_lt_one _
      · exact fract_centers _ _ _
    · intro ⟨u, hu⟩ ⟨v, hv⟩ h
      simp only [Subtype.mk.injEq]
      change (S.addAction.orbitRel).Rel ⟨u, hu⟩ ⟨v, hv⟩ at h
      rw [AddAction.orbitRel_apply, AddAction.orbit, Set.mem_range] at h
      obtain ⟨⟨y, hy⟩, hy'⟩ := h
      have : y + v = u := Subtype.ext_iff.mp hy'
      subst this
      refine fract_zspan_add _ _ ?_
      rw [← Submodule.toIntSubmodule_eq_iff_eq_toAddSubgroup.mpr (b.ofZlatticeBasis_span ℝ _).symm]
      exact hy
  invFun := fun ⟨x, hx⟩ ↦ ⟦⟨x, hx.left⟩⟧
  left_inv := by
    apply Quotient.ind
    intro ⟨a, ha⟩
    simp_rw [Quotient.lift_mk, Quotient.eq]
    exact S.orbitRel_fract _ _
  right_inv := by
    intro ⟨x, hx⟩
    simp_rw [Quotient.lift_mk, Subtype.mk.injEq, fract_eq_self]
    exact hx.right

instance (S : PeriodicSpherePacking 0) : Subsingleton S.centers := inferInstance
instance (S : PeriodicSpherePacking 0) : Finite S.centers := inferInstance

noncomputable instance PeriodicSpherePacking.finiteOrbitRelQuotient :
    Finite (Quotient S.addAction.orbitRel) :=
  -- We choose an arbitrary ℤ-basis of S.lattice
  let b : Basis _ ℤ S.lattice := (Zlattice.module_free ℝ S.lattice).chooseBasis
  if hd : 0 < d then
    Finite.of_equiv (h := aux4 S b hd) (S.addActionOrbitRelEquiv b).symm
  else
    have hd : d = 0 := Nat.eq_zero_of_not_pos hd
    have : Finite S.centers := by subst hd; infer_instance
    inferInstance

noncomputable instance : Fintype (Quotient S.addAction.orbitRel) :=
  Fintype.ofFinite _

-- TODO: rename
noncomputable def PeriodicSpherePacking.numReps : ℕ :=
  Fintype.card (Quotient S.addAction.orbitRel)

theorem PeriodicSpherePacking.numReps_eq_card_centers_inter_fundamentalDomain
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ S.lattice) (hd : 0 < d) :
    haveI := @Fintype.ofFinite _ <| aux4 S b hd
    S.numReps = (S.centers ∩ fundamentalDomain (b.ofZlatticeBasis ℝ _)).toFinset.card := by
  rw [numReps]
  have := S.addActionOrbitRelEquiv b
  convert (Finset.card_eq_of_equiv_fintype ?_).symm
  simp_rw [Set.mem_toFinset]
  exact this.symm

open Pointwise Filter

example
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
