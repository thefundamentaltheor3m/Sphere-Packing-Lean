module
public import Mathlib.Order.Filter.Defs
public import SpherePacking.Basic.PeriodicPacking.Theorem22

/-!
# Density formula for periodic sphere packings

For a periodic sphere packing `S` with lattice `S.lattice`, the density can be computed from a
fundamental domain `D`: it is the number of centers in `D` times the volume of a ball of radius
`S.separation / 2`, divided by `volume D`.

This file proves the limit statement for `S.finiteDensity` and packages it as
`PeriodicSpherePacking.density_eq`, together with a few auxiliary consequences used later in the
linear programming bound.
-/

open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open Filter
open scoped Pointwise
open scoped Topology

variable {d : ℕ}

section DensityEqFdDensity

variable
  {d : ℕ} {S : PeriodicSpherePacking d}
  {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)

lemma PeriodicSpherePacking.tendsto_finiteDensity
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

/-- Compute the density of a periodic packing using a (bounded) fundamental domain. -/
public theorem PeriodicSpherePacking.density_eq
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    S.density
      = S.numReps * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
  limsSup_eq_of_le_nhds (S.tendsto_finiteDensity b hL hd)

end DensityEqFdDensity

section ConstantEqNormalizedConstant

/--
Normalize `PeriodicSpherePackingConstant d` to a supremum over packings with `separation = 1`.
-/
public theorem periodic_constant_eq_periodic_constant_normalized :
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
    rw [← scale_density]
    · exact this
    · rw [inv_pos]
      exact S.separation_pos
  · refine iSup_le ?_
    rintro ⟨S, _⟩
    exact le_iSup (fun S : PeriodicSpherePacking d => S.density) S

end ConstantEqNormalizedConstant

section Disjoint_Covering_of_Centers

/--
If `D` meets each lattice orbit in exactly one point, then the same is true for each center of a
periodic packing.
-/
public theorem PeriodicSpherePacking.unique_covers_of_centers (S : PeriodicSpherePacking d)
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
    ∀ x : S.centers, ∃! g : S.lattice,
      (g +ᵥ x : EuclideanSpace ℝ (Fin d)) ∈ S.centers ∩ D := by
  intro x
  rcases hD_unique_covers (x : EuclideanSpace ℝ (Fin d)) with ⟨g, hg, hguniq⟩
  exact ⟨g, ⟨S.lattice_action g.property x.property, hg⟩, fun g' hg' => hguniq g' hg'.2⟩

end Disjoint_Covering_of_Centers

section Fundamental_Domains_in_terms_of_Basis

open Submodule

variable (S : PeriodicSpherePacking d) (b : Basis (Fin d) ℤ S.lattice)

theorem PeriodicSpherePacking.exists_bound_on_fundamental_domain :
  ∃ L : ℝ, ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L :=
  isBounded_iff_forall_norm_le.1 (fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ S.lattice b))

/-- Every point has a unique translate in the fundamental domain associated to a lattice basis. -/
public theorem PeriodicSpherePacking.fundamental_domain_unique_covers :
   ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _) := by
  have hspan : S.lattice = span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) :=
    (Basis.ofZLatticeBasis_span ℝ S.lattice b).symm
  intro x
  rcases exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x with ⟨g, hg, hguniq⟩
  have hg_mem : (g : EuclideanSpace ℝ (Fin d)) ∈ S.lattice := by
    simp [hspan]
  refine ⟨⟨(g : EuclideanSpace ℝ (Fin d)), hg_mem⟩, hg, ?_⟩
  intro y hy
  have hy_mem : (y : EuclideanSpace ℝ (Fin d)) ∈ span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) := by
    simpa [hspan] using y.property
  exact Subtype.ext <| congrArg
    (fun z : span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) => (z : EuclideanSpace ℝ (Fin d)))
    (hguniq ⟨(y : EuclideanSpace ℝ (Fin d)), hy_mem⟩ hy)

end Fundamental_Domains_in_terms_of_Basis

section Periodic_Density_Formula

/-!
## Convenience definitions
-/

/-- An index equivalence for the default basis of the lattice of a periodic packing. -/
@[expose] public noncomputable def PeriodicSpherePacking.basis_index_equiv
    (P : PeriodicSpherePacking d) : (Module.Free.ChooseBasisIndex ℤ ↥P.lattice) ≃ (Fin d) :=
  ZLattice.basis_index_equiv P.lattice

noncomputable def PeriodicSpherePacking.defaultBasis (S : PeriodicSpherePacking d) :
    Basis (Fin d) ℤ ↥S.lattice :=
  ((ZLattice.module_free ℝ S.lattice).chooseBasis).reindex S.basis_index_equiv

/- Here's a version of `PeriodicSpherePacking.density_eq` that
1. does not require the `hL` hypothesis that the original one does
2. uses `ZLattice.covolume` instead of the `volume` of a basis-dependent `fundamentalDomain`
-/
/-- A basis-free variant of `PeriodicSpherePacking.density_eq`, stated using `ZLattice.covolume`. -/
@[simp] public theorem PeriodicSpherePacking.density_eq'
  (S : PeriodicSpherePacking d) (hd : 0 < d) : S.density =
  (ENat.toENNReal (S.numReps : ENat)) *
  volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) /
  Real.toNNReal (ZLattice.covolume S.lattice) := by
  let b : Basis (Fin d) ℤ ↥S.lattice := S.defaultBasis
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

end Periodic_Density_Formula

section Empty_Centers

/-- If a periodic packing has no centers, then its density is zero. -/
public theorem PeriodicSpherePacking.density_of_centers_empty (S : PeriodicSpherePacking d)
    (hd : 0 < d) [instEmpty : IsEmpty S.centers] : S.density = 0 := by
  -- Idea: Use formula
  -- (We are using `IsEmpty` in order to do cases on `isEmpty_or_nonempty` in proofs)
  rw [S.density_eq' hd]
  let b := S.defaultBasis
  let D := fundamentalDomain (Basis.ofZLatticeBasis ℝ S.lattice b)
  have hD_isBounded : IsBounded D :=
    fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ S.lattice b)
  have hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D :=
    S.fundamental_domain_unique_covers b
  rw [← S.card_centers_inter_isFundamentalDomain D hD_isBounded hD_unique_covers hd]
  simp only [Set.toFinset_card, ENat.toENNReal_coe, ENNReal.div_eq_zero_iff, mul_eq_zero,
    Nat.cast_eq_zero, ENNReal.coe_ne_top, or_false]
  left
  letI := @Fintype.ofFinite _ <| finite_centers_inter_of_isBounded S D hD_isBounded hd
  haveI : IsEmpty (↥(S.centers ∩ D)) := ⟨fun x => instEmpty.false ⟨x.1, x.2.1⟩⟩
  simp

end Empty_Centers
