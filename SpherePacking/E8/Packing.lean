/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Gareth Ma
-/
module
public import SpherePacking.E8.Basic

/-!
# The E8 packing

This file defines the periodic packing coming from the `E8` lattice, and computes its density.

## Main definitions
* `E8Lattice`
* `E8Packing`

## Main statements
* `E8Packing_density`
-/

variable {R : Type*}

open Module
open InnerProductSpace RCLike

public lemma E8_norm_eq_sqrt_even
    (v : Fin 8 → ℝ) (hv : v ∈ Submodule.E8 ℝ) :
    ∃ n : ℤ, Even n ∧ n = ‖WithLp.toLp 2 v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial]
  exact E8_integral_self _ hv

lemma E8_norm_lower_bound (v : Fin 8 → ℝ) (hv : v ∈ Submodule.E8 ℝ) :
    v = 0 ∨ √2 ≤ ‖WithLp.toLp 2 v‖ := by
  rw [or_iff_not_imp_left, ← ne_eq]
  intro hv'
  obtain ⟨n, hn, hn'⟩ := E8_norm_eq_sqrt_even v hv
  have hn0 : 0 ≤ n := by exact_mod_cast (by simp [hn'] : (0 : ℝ) ≤ (n : ℝ))
  have hn_ne : n ≠ 0 := by contrapose! hv'; simpa [hv'] using hn'.symm
  have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := hn; omega
  apply le_of_sq_le_sq _ (by simp)
  simpa [hn', Real.sq_sqrt zero_le_two] using (show (2 : ℝ) ≤ n from mod_cast hn2)

/-- The `E8` lattice as a `ℤ`-submodule of `EuclideanSpace ℝ (Fin 8)`. -/
public noncomputable def E8Lattice : Submodule ℤ (EuclideanSpace ℝ (Fin 8)) :=
  (Submodule.E8 ℝ).map (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm.toLinearMap

/-- The `E8` lattice is a discrete subgroup of `EuclideanSpace ℝ (Fin 8)`. -/
public instance instDiscreteE8Lattice : DiscreteTopology E8Lattice := by
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
  refine ⟨1, by norm_num, ?_⟩
  rintro ⟨x, hx⟩ hx'
  simp only [Submodule.mk_eq_zero]
  obtain ⟨v, hv, rfl⟩ := hx
  suffices v = 0 by simpa using congrArg (WithLp.toLp 2) this
  refine (E8_norm_lower_bound v hv).resolve_right ?_
  have hx1 : ‖WithLp.toLp 2 v‖ < (1 : ℝ) := by
    simpa [dist_zero_right, AddSubgroupClass.coe_norm] using hx'
  exact not_le_of_gt (hx1.trans Real.one_lt_sqrt_two)

lemma span_E8_eq_top : Submodule.span ℝ (Submodule.E8 ℝ : Set (Fin 8 → ℝ)) = ⊤ := by
  refine (eq_top_iff).2 ?_
  simpa [span_E8Matrix_eq_top ℝ] using
    (Submodule.span_mono (R := ℝ) (range_E8Matrix_row_subset ℝ))

lemma span_E8_eq_top' :
    Submodule.span ℝ (E8Lattice : Set (EuclideanSpace ℝ (Fin 8))) = ⊤ := by
  set e := (WithLp.linearEquiv 2 ℝ (Fin 8 → ℝ)).symm.toLinearMap
  change Submodule.span ℝ (e '' (Submodule.E8 ℝ : Set _)) = ⊤
  rw [Submodule.span_image, span_E8_eq_top]
  simp [e]

lemma span_E8Matrix_eq_E8Lattice :
    Submodule.span ℤ
      (Set.range fun i ↦ (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i)) =
      E8Lattice := by
  rw [show Set.range (fun i ↦ (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i)) =
        ((WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm :
            (Fin 8 → ℝ) →ₗ[ℤ] EuclideanSpace ℝ (Fin 8)) '' Set.range (E8Matrix ℝ).row by
      simpa [Function.comp] using
        Set.range_comp (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm (E8Matrix ℝ).row,
    ← Submodule.map_span, span_E8Matrix ℝ]
  simp [E8Lattice]

/-- `E8Lattice` spans the ambient space over `ℝ`. -/
public instance instIsZLatticeE8Lattice : IsZLattice ℝ E8Lattice where
  span_top := by rw [span_E8_eq_top']

noncomputable def E8_ℤBasis : Basis (Fin 8) ℤ E8Lattice := by
  refine Basis.mk
      (v := fun i ↦ ⟨(WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i), ?_⟩) ?_ ?_
  · exact Submodule.mem_map_of_mem (E8Matrix_row_mem_E8 i)
  · refine LinearIndependent.of_comp (Submodule.subtype _) ?_
    refine LinearIndependent.of_comp (M' := (Fin 8 → ℝ)) (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)) ?_
    exact (linearIndependent_E8Matrix ℝ).restrict_scalars' ℤ
  · rw [← Submodule.map_le_map_iff_of_injective (f := E8Lattice.subtype) (by simp)]
    simp only [Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_span, ← Set.range_comp]
    exact span_E8Matrix_eq_E8Lattice.ge

lemma coe_E8_ℤBasis_apply (i : Fin 8) :
    E8_ℤBasis i = (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i) := by
  rw [E8_ℤBasis, Basis.coe_mk]

section Packing

open scoped Real

/-- The periodic sphere packing in `ℝ^8` coming from the `E8` lattice. -/
@[expose] public noncomputable def E8Packing : PeriodicSpherePacking 8 where
  separation := √2
  lattice := E8Lattice
  centers := E8Lattice
  centers_dist := by
    simp only [Pairwise, E8Lattice, ne_eq, Subtype.forall, Subtype.mk.injEq]
    intro a ha b hb hab
    rw [SetLike.mem_coe, Submodule.mem_map] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have hsub : a' - b' ∈ Submodule.E8 ℝ := Submodule.sub_mem _ ha' hb'
    have hne : a' ≠ b' := by
      contrapose! hab
      simp [hab]
    simp only [dist_eq_norm, AddSubgroupClass.coe_norm, AddSubgroupClass.coe_sub]
    have hne' : a' - b' ≠ 0 := sub_ne_zero.mpr hne
    convert (E8_norm_lower_bound _ hsub).resolve_left hne' using 2
  lattice_action x y := add_mem

lemma E8Packing_numReps : E8Packing.numReps = 1 :=
  PeriodicSpherePacking.numReps_eq_one _ rfl

lemma E8Basis_apply_norm : ∀ i : Fin 8, ‖WithLp.toLp 2 (E8Basis ℝ i)‖ ≤ 2 := by
  simp [E8Basis, E8Matrix, EuclideanSpace.norm_eq, Fin.forall_fin_succ, Fin.sum_univ_eight]
  norm_num [show (√2 : ℝ) ≤ 2 by
    rw [Real.sqrt_le_iff]
    norm_num]

lemma E8_ℤBasis_apply_norm : ∀ i : Fin 8, ‖E8_ℤBasis i‖ ≤ 2 := by
  simpa [coe_E8_ℤBasis_apply, E8Basis_apply] using fun i => E8Basis_apply_norm i

section Determinant

private abbrev Matrix.myDet {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]
    (M : Matrix n n R) : R := M.det

lemma E8Matrix_myDet_eq_one (R : Type*) [Field R] [NeZero (2 : R)] : (E8Matrix R).myDet = 1 :=
  E8Matrix_unimodular R

open MeasureTheory ZSpan

lemma ZSpan.volume_fundamentalDomain' {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ (ι → ℝ)) :
    volume (fundamentalDomain b) = ENNReal.ofReal |(Matrix.of b).myDet| :=
  volume_fundamentalDomain b

public lemma E8Basis_volume : volume (fundamentalDomain (E8Basis ℝ)) = 1 := by
  simp [ZSpan.volume_fundamentalDomain' (b := E8Basis ℝ), of_basis_eq_matrix, E8Matrix_myDet_eq_one]

end Determinant

open MeasureTheory ZSpan in
lemma same_domain :
    (WithLp.linearEquiv 2 ℝ _).symm ⁻¹' fundamentalDomain (E8_ℤBasis.ofZLatticeBasis ℝ E8Lattice) =
      fundamentalDomain (E8Basis ℝ) := by
  rw [← LinearEquiv.image_eq_preimage_symm, ZSpan.map_fundamentalDomain]
  congr! 1
  ext i : 1
  simp [E8_ℤBasis, E8Basis_apply]

open MeasureTheory ZSpan in
lemma E8_Basis_volume :
    volume (fundamentalDomain (E8_ℤBasis.ofZLatticeBasis ℝ E8Lattice)) = 1 := by
  rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).symm.measure_preimage_equiv]
  erw [same_domain]
  rw [E8Basis_volume]

open MeasureTheory ZSpan in
/-- The density of the `E8` packing. -/
public theorem E8Packing_density : E8Packing.density = ENNReal.ofReal π ^ 4 / 384 := by
  rw [PeriodicSpherePacking.density_eq E8_ℤBasis ?_ (by omega) (L := 16)]
  · rw [E8Packing_numReps, Nat.cast_one, one_mul, volume_ball, finrank_euclideanSpace,
      Fintype.card_fin, Nat.cast_ofNat]
    simp only [E8Packing]
    have {x : ℝ} (hx : 0 ≤ x := by positivity) : √x ^ 8 = x ^ 4 := calc
      √x ^ 8 = (√x ^ 2) ^ 4 := by rw [← pow_mul]
      _ = x ^ 4 := by rw [Real.sq_sqrt hx]
    rw [← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, div_pow, this, this, ← mul_div_assoc,
      div_mul_eq_mul_div, mul_comm, mul_div_assoc, mul_div_assoc]
    · norm_num [Nat.factorial, mul_one_div]
      convert div_one _
      · rw [E8_Basis_volume]
      · rw [← ENNReal.ofReal_pow, ENNReal.ofReal_div_of_pos, ENNReal.ofReal_ofNat] <;> positivity
    · positivity
    · positivity
  · intro x hx
    trans ∑ i, ‖E8_ℤBasis i‖
    · rw [← fract_eq_self.mpr hx]
      convert norm_fract_le (K := ℝ) _ _
      simp; rfl
    · refine (Finset.sum_le_sum (fun i hi ↦ E8_ℤBasis_apply_norm i)).trans ?_
      norm_num

end Packing
