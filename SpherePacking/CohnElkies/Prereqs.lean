/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
/-
## THIS FILE SHOULD EVENTUALLY BE REMOVED AND THE REFERENCES IN COHN-ELKIES MUST BE REPLACED WITH
## THE RIGHT ONES (NOT THE ONES FROM HERE). THIS FILE IS JUST A TEMPORARY SOLUTION TO MAKE THE
## COHN-ELKIES FILE WORK.
-/
import Mathlib.Algebra.Module.Zlattice.Basic
import Mathlib.Algebra.Module.Zlattice.Covolume
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import SpherePacking.Basic.SpherePacking
import SpherePacking.Basic.PeriodicPacking

open BigOperators Bornology

variable {d : ℕ} [Fact (0 < d)]
variable (Λ : AddSubgroup (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZlattice ℝ Λ]

noncomputable section Dual_Lattice

/-
This section defines the Dual Lattice of a Lattice. Taken from `SpherePacking/ForMathlib/Dual.lean`.
-/

def DualLattice : AddSubgroup (EuclideanSpace ℝ (Fin d)) where
  carrier := { x | ∀ l : Λ, ∃ n : ℤ, ⟪x, l⟫_ℝ = ↑n }
  zero_mem' := by
    simp only [Subtype.forall, Set.mem_setOf_eq, inner_zero_left]
    intro a _
    use 0
    rw [Int.cast_zero]
  add_mem' := by
    intros x y hx hy l
    obtain ⟨n, hn⟩ := hx l
    obtain ⟨m, hm⟩ := hy l
    use n + m
    simp only [inner_add_left, hn, hm, Int.cast_add]
  neg_mem' := by
    intros x hx l
    obtain ⟨n, hn⟩ := hx l
    use -n
    simp only [inner_neg_left, hn, Int.cast_neg]

end Dual_Lattice

open scoped FourierTransform

open Complex Real

section Schwartz_Functions

namespace SchwartzMap

@[simp]
def Inv_Pow_Summable_Over (X : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  Summable (fun x : X => 1 / ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ (d + 1))

-- TODO: Remove after proving that d + 1 does, indeed, work.
-- Else, use as hack for `Summable_of_Inv_Pow_Summable'`.
def Exists_Inv_Pow_Summable_Over (X : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ k > 0, Summable (fun x : X => 1 / ‖(x : EuclideanSpace ℝ (Fin d))‖^k)

variable (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ)
-- Need to relax to decaying! Reason: want its composition with `Subtype.val` to be valid.
-- This would _not_ be true of Schwartz functions because the restriction cannot be Schwartz!
-- (Its domain and codomain are almost never going to be vector spaces!!!!!!!!)

theorem Summable_of_Inv_Pow_Summable' -- (P : PeriodicSpherePacking d)
  {X : Set (EuclideanSpace ℝ (Fin d))} (hX : SchwartzMap.Inv_Pow_Summable_Over X)
  (hne_zero : 0 ∉ X) :
  Summable (fun x : X => f x) := by
  rw [summable_iff_vanishing_norm]
  intro ε hε
  let k := d + 1
  have hk' : 0 < k := by positivity
  rw [Inv_Pow_Summable_Over] at hX
  simp only [one_div, summable_iff_vanishing_norm, gt_iff_lt, Real.norm_eq_abs] at hX
  obtain ⟨C, hC⟩ := f.decay' k 0
  have hC_nonneg : 0 ≤ C := by
    specialize hC (0 : EuclideanSpace ℝ (Fin d))
    rw [norm_zero, zero_pow (Nat.not_eq_zero_of_lt hk'), zero_mul] at hC
    exact hC
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hC
  have haux₁ : 0 < C + 1 := by linarith
  specialize hX (ε / (C + 1)) (div_pos hε haux₁)
  obtain ⟨s, hs⟩ := hX
  use s
  intro t ht
  specialize hs t ht
  suffices htriangle : ∑ x ∈ t, |f ↑x| < ε
  · refine lt_of_le_of_lt ?_ htriangle
    rw [Real.norm_eq_abs]
    exact Finset.abs_sum_le_sum_abs (fun i : X ↦ f ↑i) t
  have haux₂ : |∑ x ∈ t, (C + 1) * (‖(x : EuclideanSpace ℝ (Fin d))‖ ^ k)⁻¹| < ε := by
    rw [← Finset.mul_sum, IsAbsoluteValue.abv_mul (fun (x : ℝ) ↦ |x|) _ _, abs_of_pos haux₁]
    exact (lt_div_iff' haux₁).mp hs
  refine lt_of_le_of_lt ?_ haux₂
  have haux₃ : ∀ x ∈ t, (0 : ℝ) ≤ (C + 1) * (‖(x : EuclideanSpace ℝ (Fin d))‖ ^ k)⁻¹ := by
    intro x _
    apply mul_nonneg
    · linarith
    · simp only [inv_nonneg, norm_nonneg, pow_nonneg]
  rw [Finset.abs_sum_of_nonneg haux₃]
  cases t.eq_empty_or_nonempty
  · case inl hempty =>
    rw [hempty, Finset.sum_empty, Finset.sum_empty]
  · case inr hnonempty =>
    apply Finset.sum_le_sum
    intro x _
    have haux₄ : (x : EuclideanSpace ℝ (Fin d)) ≠ 0 := by
      intro h
      apply hne_zero
      rw [← h]
      exact Subtype.coe_prop x
    have haux₅ : 0 < (‖(x : EuclideanSpace ℝ (Fin d))‖ ^ k) := by
      apply pow_pos
      exact norm_pos_iff'.mpr haux₄
    refine le_of_mul_le_mul_of_pos_right ?_ haux₅
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ (ne_of_gt haux₅), mul_one]
    specialize hC x
    refine LE.le.trans hC ?_
    rw [le_add_iff_nonneg_right]
    exact zero_le_one

theorem Summable_of_Inv_Pow_Summable -- (P : PeriodicSpherePacking d)
  (X : Set (EuclideanSpace ℝ (Fin d))) (hX : SchwartzMap.Inv_Pow_Summable_Over X) :
  Summable (fun x : X => f x) := by
  if hzero : 0 ∈ X then
    let s : Finset (X) := {⟨0, hzero⟩}
    rw [Inv_Pow_Summable_Over] at hX
    rw [← (Finset.summable_compl_iff s)] at hX ⊢
    -- rw [← Inv_Pow_Summable_Over] at hX
    -- refine Summable_of_Inv_Pow_Summable' (f ∘ Subtype.val) ?_ ?_

    sorry
  else
    exact Summable_of_Inv_Pow_Summable' f hX hzero

end SchwartzMap

namespace PeriodicSpherePacking

lemma Summable_Inverse_Powers (P : PeriodicSpherePacking d) :
  SchwartzMap.Inv_Pow_Summable_Over P.centers := by
  rw [SchwartzMap.Inv_Pow_Summable_Over]
  simp only [one_div, summable_iff_vanishing_norm, gt_iff_lt, Real.norm_eq_abs]
  · intro ε hε
    -- Translating and scaling fundamental domains could be a good idea - discussion with Bhavik
    sorry

end PeriodicSpherePacking

end Schwartz_Functions

noncomputable section PSF_L

/-
This section defines the Poisson Summation Formual, Lattice Version (`PSF_L`). This is a direct
dependency of the Cohn-Elkies proof.
-/

-- Could this maybe become a `structure` with each field being a different condition?
def PSF_Conditions (f : EuclideanSpace ℝ (Fin d) → ℂ) : Prop :=
  /-
    Mention here all the conditions we decide to impose functions on which to define the PSF-L.
    For example, this could be that they must be Schwartz (cf. blueprint) or admissible (cf. Cohn-
    Elkies). This is a placeholder for now, as is almost everything in this file.

    I think Schwartz is a good choice, because we can use the results in
    `Mathlib.Analysis.Distribution.FourierSchwartz` to conclude various things about the function.
  -/
  Summable f ∧
  sorry

theorem PSF_L {f : EuclideanSpace ℝ (Fin d) → ℂ} (hf : PSF_Conditions f)
  (v : EuclideanSpace ℝ (Fin d)) :
  ∑' ℓ : Λ, f (v + ℓ) = (1 / Zlattice.covolume Λ) * ∑' m : DualLattice Λ, (𝓕 f m) *
  exp (2 * π * I * ⟪v, m⟫_ℝ) :=
  sorry

-- The version below is on the blueprint. I'm pretty sure it can be removed.
theorem PSF_L' {f : EuclideanSpace ℝ (Fin d) → ℂ} (hf : PSF_Conditions f) :
  ∑' ℓ : Λ, f ℓ = (1 / Zlattice.covolume Λ) * ∑' m : DualLattice Λ, (𝓕 f m) := by
  have := PSF_L Λ hf (0 : EuclideanSpace ℝ (Fin d))
  simp only [zero_add, inner_zero_left, ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at this
  exact this

end PSF_L

open scoped ENNReal
open SpherePacking Metric BigOperators Pointwise Filter MeasureTheory Zspan

section Periodic_Packings

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

end Periodic_Packings

section numReps_Related

noncomputable instance PeriodicSpherePacking.instFintypeNumReps'
  (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D) :
  Fintype ↑(S.centers ∩ D) := @Fintype.ofFinite _ <| aux4 S D hD_isBounded hd

noncomputable def PeriodicSpherePacking.numReps' (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
  -- (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)
  : ℕ :=
  haveI := S.instFintypeNumReps' hd hD_isBounded
  Fintype.card ↑(S.centers ∩ D)

lemma PeriodicSpherePacking.numReps'_nonneg (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D) :
  0 ≤ S.numReps' hd hD_isBounded := by
  letI := S.instFintypeNumReps' hd hD_isBounded
  rw [PeriodicSpherePacking.numReps']
  exact Nat.zero_le (Fintype.card ↑(S.centers ∩ D))

end numReps_Related

section Disjoint_Covering_of_Centers

lemma PeriodicSpherePacking.unique_covers_of_centers (S : PeriodicSpherePacking d) -- (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))}  -- (hD_isBounded : IsBounded D)
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

lemma PeriodicSpherePacking.centers_union_over_lattice (S : PeriodicSpherePacking d) -- (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))}  -- (hD_isBounded : IsBounded D)
  (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) -- (hD_measurable : MeasurableSet D)
  : S.centers = ⋃ (g : S.lattice), (g +ᵥ S.centers ∩ D) := by
  ext x
  simp only [Set.mem_iUnion, Subtype.exists, AddSubmonoid.mk_vadd, exists_prop]
  constructor
  · intro hx
    obtain ⟨g, hg₁, _⟩ := S.unique_covers_of_centers hD_unique_covers ⟨x, hx⟩
    use -g
    simp only [neg_mem_iff, SetLike.coe_mem, true_and]
    obtain ⟨hy₁, hy₂⟩ := hg₁
    have : ∃ y : D, ↑y = g +ᵥ x := by use ⟨g +ᵥ x, hy₂⟩
    obtain ⟨y, hy⟩ := this
    suffices : x = -g +ᵥ (y : EuclideanSpace ℝ (Fin d))
    · rw [this]
      have hy' := Subtype.coe_prop y
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
    simp only [vadd_eq_add] at hy₂
    rw [← hy₂]
    exact S.lattice_action hg₁ hy₁

-- This is true but unnecessary (for now). What's more important is expressing it as a disjoint
-- union over points in X / Λ = X ∩ D of translates of the lattice by points in X / Λ = X ∩ D or
-- something like that, because that's what's needed for `tsum_finset_bUnion_disjoint`.
lemma PeriodicSpherePacking.translates_disjoint (S : PeriodicSpherePacking d) -- (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))}  -- (hD_isBounded : IsBounded D)
  (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) -- (hD_measurable : MeasurableSet D)
  : Set.Pairwise ⊤ (Disjoint on (fun (g : S.lattice) => g +ᵥ S.centers ∩ D)) -- why the error?
  -- True
  := by
  intro x hx y hy hxy
  obtain ⟨g, hg₁, hg₂⟩ := hD_unique_covers x
  specialize hg₂ y
  simp only  at hg₂
  simp only [Set.disjoint_iff_inter_eq_empty]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hz₁ hz₂
  sorry

-- Can we use some sort of orbit disjointedness result and factor through the equivalence between
-- the `Quotient` and `S.centers ∩ D`?

end Disjoint_Covering_of_Centers

section Fundamental_Domains_in_terms_of_Basis

open Submodule

variable (S : PeriodicSpherePacking d) (b : Basis (Fin d) ℤ S.lattice)

-- I include the following because some lemmas in `PeriodicPacking` have them as assumptions, and
-- I'd like to replace all instances of `D` with `fundamentalDomain (b.ofZlatticeBasis ℝ _)` and
-- the assumptions on `D` with the following lemmas.

-- Note that we have `Zspan.fundamentalDomain_isBounded`. We can use this to prove the following,
-- which is necessary for `PeriodicSpherePacking.density_eq`.
lemma PeriodicSpherePacking.exists_bound_on_fundamental_domain :
  ∃ L : ℝ, ∀ x ∈ fundamentalDomain (b.ofZlatticeBasis ℝ _), ‖x‖ ≤ L :=
  isBounded_iff_forall_norm_le.1 (fundamentalDomain_isBounded (Basis.ofZlatticeBasis ℝ S.lattice b))

-- Note that we have `Zspan.exist_unique_vadd_mem_fundamentalDomain`. We can use this to prove the
-- following.
lemma PeriodicSpherePacking.fundamental_domain_unique_covers :
   ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ fundamentalDomain (b.ofZlatticeBasis ℝ _) := by
  have : S.lattice = (span ℤ (Set.range (b.ofZlatticeBasis ℝ _))).toAddSubgroup :=
    Eq.symm (Basis.ofZlatticeBasis_span ℝ S.lattice b)
  intro x
  -- The `g` we need should be the negative of the floor of `x`, but we can obtain it from the
  -- existing library result.
  obtain ⟨g, hg₁, hg₂⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZlatticeBasis ℝ _) x
  have hg_mem : ↑g ∈ S.lattice := by simp only [this, mem_toAddSubgroup, SetLike.coe_mem]
  use ⟨↑g, hg_mem⟩
  constructor
  · exact hg₁
  · intro y
    have hy_mem : ↑y ∈ (span ℤ (Set.range ⇑(Basis.ofZlatticeBasis ℝ S.lattice b))).toAddSubgroup :=
      by simp only [← this, SetLike.coe_mem]
    intro hy
    simp only at hg₂ ⊢
    specialize hg₂ ⟨y, hy_mem⟩ hy
    refine SetCoe.ext ?h.right.a
    have heq : ↑y = (g : EuclideanSpace ℝ (Fin d)) := by rw [← hg₂]
    exact heq

-- Note that we already have `Zspan.fundamentalDomain_measurableSet`. Use
-- `fundamentalDomain_measurableSet (Basis.ofZlatticeBasis ℝ S.lattice b)` to say that our desired
-- fundamental domain is measurable.

end Fundamental_Domains_in_terms_of_Basis

section Periodic_Density_Formula

noncomputable instance HDivENNReal : HDiv NNReal ENNReal ENNReal where
  hDiv := fun x y => x / y
noncomputable instance HMulENNReal : HMul NNReal ENNReal ENNReal where
  hMul := fun x y => x * y

noncomputable def PeriodicSpherePacking.basis_index_equiv (P : PeriodicSpherePacking d) :
  (Module.Free.ChooseBasisIndex ℤ ↥P.lattice) ≃ (Fin d) := by
  refine Fintype.equivFinOfCardEq ?h
  rw [← FiniteDimensional.finrank_eq_card_chooseBasisIndex, Zlattice.rank ℝ P.lattice,
      finrank_euclideanSpace, Fintype.card_fin]

/- Here's a version of `PeriodicSpherePacking.density_eq` that
1. Does not require the `hL` hypothesis that the original one does
2. Uses `Zlattice.covolume` instead of the `volume` of a basis-dependent `fundamentalDomain`
-/
@[simp]
theorem PeriodicSpherePacking.density_eq'
  (S : PeriodicSpherePacking d) (hd : 0 < d) : S.density =
  (ENat.toENNReal (S.numReps : ENat)) *
  volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) /
  Real.toNNReal (Zlattice.covolume S.lattice) := by
  let b : Basis (Fin d) ℤ ↥S.lattice := ((Zlattice.module_free ℝ S.lattice).chooseBasis).reindex
    (S.basis_index_equiv)
  obtain ⟨L, hL⟩ := S.exists_bound_on_fundamental_domain b
  rw [Real.toNNReal_of_nonneg (LT.lt.le (Zlattice.covolume_pos S.lattice volume))]
  rw [S.density_eq b hL hd]
  simp only [ENat.toENNReal_coe]
  apply congrArg _ _
  refine (ENNReal.toReal_eq_toReal_iff' ?hx ?hy).mp ?_
  · rw [← lt_top_iff_ne_top]
    letI := fundamentalDomain_isBounded (Basis.ofZlatticeBasis ℝ S.lattice b)
    exact IsBounded.measure_lt_top this
  · exact ENNReal.coe_ne_top
  · rw [ENNReal.coe_toReal, NNReal.coe_mk]
    refine Eq.symm (Zlattice.covolume_eq_measure_fundamentalDomain S.lattice volume ?h)
    exact Zlattice.isAddFundamentalDomain b volume

theorem periodic_constant_eq_constant (hd : 0 < d) :
    PeriodicSpherePackingConstant d = SpherePackingConstant d := by
  sorry

end Periodic_Density_Formula

open scoped FourierTransform

section Fourier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

-- Super surprised not to find this in Mathlib!
-- @[simp]
-- def fourierIntegral (f : V → E) : 𝓕⁻ (𝓕 f) = f := by
--   ext x
--   refine Integrable.fourier_inversion ?h.hf ?h.h'f ?h.hv
--   sorry

end Fourier

noncomputable section Misc

-- For some reason the following two instances seem to need restating...
instance (v : EuclideanSpace ℝ (Fin d)) : Decidable (v = 0) := Classical.propDecidable (v = 0)

instance : DecidableEq (EuclideanSpace ℝ (Fin d)) :=
  Classical.typeDecidableEq (EuclideanSpace ℝ (Fin d))

-- Now a small lemma from Complex analysis:
local notation "conj" => starRingEnd ℂ
lemma Complex.exp_neg_real_I_eq_conj (x m : EuclideanSpace ℝ (Fin d)) :
  cexp (-(2 * ↑π * I * ↑⟪x, m⟫_ℝ)) = conj (cexp (2 * ↑π * I * ↑⟪x, m⟫_ℝ)) :=
  calc cexp (-(2 * ↑π * I * ↑⟪x, m⟫_ℝ))
  _ = Circle.exp (-2 * π * ⟪x, m⟫_ℝ)
      := by
          rw [Circle.coe_exp]
          push_cast
          ring_nf
  _ = conj (Circle.exp (2 * π * ⟪x, m⟫_ℝ))
      := by rw [mul_assoc, neg_mul, ← mul_assoc, ← Circle.coe_inv_eq_conj, Circle.exp_neg]
  _= conj (cexp (2 * ↑π * I * ↑⟪x, m⟫_ℝ))
      := by
          rw [Circle.coe_exp]
          apply congrArg conj
          push_cast
          ring_nf

end Misc
