/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Gareth Ma
-/
module
public import SpherePacking.E8.Basic

/-! # The E8 packing — density `π^4 / 384`. Main: `E8Lattice`, `E8Packing`, `E8Packing_density`. -/

variable {R : Type*}

open Module InnerProductSpace RCLike

public lemma E8_norm_eq_sqrt_even (v : Fin 8 → ℝ) (hv : v ∈ Submodule.E8 ℝ) :
    ∃ n : ℤ, Even n ∧ n = ‖WithLp.toLp 2 v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial]
  exact E8_integral_self _ hv

lemma E8_norm_lower_bound (v : Fin 8 → ℝ) (hv : v ∈ Submodule.E8 ℝ) :
    v = 0 ∨ √2 ≤ ‖WithLp.toLp 2 v‖ := by
  rw [or_iff_not_imp_left, ← ne_eq]
  intro hv'
  obtain ⟨n, hn, hn'⟩ := E8_norm_eq_sqrt_even v hv
  have hn_ne : n ≠ 0 := by contrapose! hv'; simpa [hv'] using hn'.symm
  have hn2 : 2 ≤ n := by
    have : 0 ≤ n := by exact_mod_cast (by simp [hn'] : (0 : ℝ) ≤ (n : ℝ))
    obtain ⟨k, rfl⟩ := hn; omega
  exact le_of_sq_le_sq
    (by simpa [hn', Real.sq_sqrt zero_le_two] using (show (2 : ℝ) ≤ n from mod_cast hn2)) (by simp)

/-- The `E8` lattice as a `ℤ`-submodule of `EuclideanSpace ℝ (Fin 8)`. -/
public noncomputable def E8Lattice : Submodule ℤ (EuclideanSpace ℝ (Fin 8)) :=
  (Submodule.E8 ℝ).map (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm.toLinearMap

/-- The `E8` lattice is a discrete subgroup of `EuclideanSpace ℝ (Fin 8)`. -/
public instance instDiscreteE8Lattice : DiscreteTopology E8Lattice := by
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
  refine ⟨1, by norm_num, ?_⟩
  rintro ⟨_, ⟨v, hv, rfl⟩⟩ hx'
  suffices v = 0 by simpa using congrArg (WithLp.toLp 2) this
  exact (E8_norm_lower_bound v hv).resolve_right (not_le_of_gt (lt_trans
    (by simpa [dist_zero_right, AddSubgroupClass.coe_norm] using hx') Real.one_lt_sqrt_two))

/-- `E8Lattice` spans the ambient space over `ℝ`. -/
public instance instIsZLatticeE8Lattice : IsZLattice ℝ E8Lattice where
  span_top := by
    have hE8 : Submodule.span ℝ (Submodule.E8 ℝ : Set (Fin 8 → ℝ)) = ⊤ :=
      eq_top_iff.2 (by simpa [span_E8Matrix_eq_top ℝ] using
        Submodule.span_mono (R := ℝ) (range_E8Matrix_row_subset ℝ))
    change Submodule.span ℝ
      ((WithLp.linearEquiv 2 ℝ (Fin 8 → ℝ)).symm.toLinearMap '' (Submodule.E8 ℝ : Set _)) = ⊤
    rw [Submodule.span_image, hE8]; simp

private lemma span_E8Matrix_eq_E8Lattice :
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

noncomputable def E8_ℤBasis : Basis (Fin 8) ℤ E8Lattice := by
  refine Basis.mk
      (v := fun i ↦ ⟨(WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i), ?_⟩) ?_ ?_
  · exact Submodule.mem_map_of_mem (E8Matrix_row_mem_E8 i)
  · exact LinearIndependent.of_comp (Submodule.subtype _) <|
      LinearIndependent.of_comp (M' := (Fin 8 → ℝ)) (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ))
        ((linearIndependent_E8Matrix ℝ).restrict_scalars' ℤ)
  · rw [← Submodule.map_le_map_iff_of_injective (f := E8Lattice.subtype) (by simp),
      Submodule.map_top, Submodule.range_subtype, Submodule.map_span, ← Set.range_comp]
    exact span_E8Matrix_eq_E8Lattice.ge

open scoped Real

/-- The periodic sphere packing in `ℝ^8` coming from the `E8` lattice. -/
@[expose] public noncomputable def E8Packing : PeriodicSpherePacking 8 where
  separation := √2
  lattice := E8Lattice
  centers := E8Lattice
  centers_dist := by
    simp only [Pairwise, E8Lattice, ne_eq, Subtype.forall, Subtype.mk.injEq]
    rintro _ ⟨a', ha', rfl⟩ _ ⟨b', hb', rfl⟩ hab
    simp only [dist_eq_norm, AddSubgroupClass.coe_norm, AddSubgroupClass.coe_sub]
    convert (E8_norm_lower_bound _ (Submodule.sub_mem _ ha' hb')).resolve_left
      (sub_ne_zero.mpr (by contrapose! hab; simp [hab])) using 2
  lattice_action x y := add_mem

lemma E8Packing_numReps : E8Packing.numReps = 1 :=
  PeriodicSpherePacking.numReps_eq_one _ rfl

private lemma E8_ℤBasis_apply_norm : ∀ i : Fin 8, ‖E8_ℤBasis i‖ ≤ 2 := by
  have hbase : ∀ i : Fin 8, ‖WithLp.toLp 2 (E8Basis ℝ i)‖ ≤ 2 := by
    simp [E8Basis, E8Matrix, EuclideanSpace.norm_eq, Fin.forall_fin_succ, Fin.sum_univ_eight]
    norm_num [show (√2 : ℝ) ≤ 2 by rw [Real.sqrt_le_iff]; norm_num]
  simpa [E8_ℤBasis, Basis.coe_mk, E8Basis_apply] using hbase

open MeasureTheory ZSpan in
public lemma E8Basis_volume : volume (fundamentalDomain (E8Basis ℝ)) = 1 := by
  simp [volume_fundamentalDomain (b := E8Basis ℝ), of_basis_eq_matrix,
    E8Matrix_unimodular (R := ℝ)]

open MeasureTheory ZSpan in
private lemma E8_Basis_volume :
    volume (fundamentalDomain (E8_ℤBasis.ofZLatticeBasis ℝ E8Lattice)) = 1 := by
  have hpreim : (WithLp.linearEquiv 2 ℝ _).symm ⁻¹' fundamentalDomain
      (E8_ℤBasis.ofZLatticeBasis ℝ E8Lattice) = fundamentalDomain (E8Basis ℝ) := by
    rw [← LinearEquiv.image_eq_preimage_symm, ZSpan.map_fundamentalDomain]
    congr! 1; ext i : 1; simp [E8_ℤBasis, E8Basis_apply]
  rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).symm.measure_preimage_equiv]
  erw [hpreim, E8Basis_volume]

open MeasureTheory ZSpan in
/-- The density of the `E8` packing. -/
public theorem E8Packing_density : E8Packing.density = ENNReal.ofReal π ^ 4 / 384 := by
  rw [PeriodicSpherePacking.density_eq E8_ℤBasis ?_ (by omega) (L := 16)]
  · rw [E8Packing_numReps, Nat.cast_one, one_mul, volume_ball, finrank_euclideanSpace,
      Fintype.card_fin, Nat.cast_ofNat]
    simp only [E8Packing]
    have {x : ℝ} (hx : 0 ≤ x := by positivity) : √x ^ 8 = x ^ 4 := by
      rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, Real.sq_sqrt hx]
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
    · rw [← fract_eq_self.mpr hx]; convert norm_fract_le (K := ℝ) _ _; simp; rfl
    · exact (Finset.sum_le_sum (fun i _ ↦ E8_ℤBasis_apply_norm i)).trans (by norm_num)
