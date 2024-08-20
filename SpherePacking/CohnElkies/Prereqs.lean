/-
## THIS FILE SHOULD EVENTUALLY BE REMOVED AND THE REFERENCES IN COHN-ELKIES MUST BE REPLACED WITH
## THE RIGHT ONES (NOT THE ONES FROM HERE). THIS FILE IS JUST A TEMPORARY SOLUTION TO MAKE THE
## COHN-ELKIES FILE WORK.
-/
import Mathlib.Algebra.Module.Zlattice.Basic
import Mathlib.Algebra.Module.Zlattice.Covolume
import Mathlib.Analysis.Fourier.FourierTransform
import SpherePacking.Basic.SpherePacking
import SpherePacking.Basic.PeriodicPacking

open BigOperators Bornology

variable {d : ℕ}
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

    I think Schwartz is a good choice, because it also guarantees that
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

-- Removable?
instance (S : PeriodicSpherePacking d) (b : Basis (Fin d) ℤ S.lattice) :
  Fintype ↑(S.centers ∩ fundamentalDomain (b.ofZlatticeBasis ℝ _)) := sorry

-- Removable?
noncomputable def PeriodicSpherePacking.numReps''
  (S : PeriodicSpherePacking d) (b : Basis (Fin d) ℤ S.lattice) : ℕ :=
  Fintype.card ↑(S.centers ∩ fundamentalDomain (b.ofZlatticeBasis ℝ _))

noncomputable instance PeriodicSpherePacking.instFintypeNumReps'
  (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D) :
  Fintype ↑(S.centers ∩ D) := @Fintype.ofFinite _ <| aux4 S D hD_isBounded hd

noncomputable def PeriodicSpherePacking.numReps' (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
  -- (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)
  : ℕ :=
  haveI := S.instFintypeNumReps' hd hD_isBounded
  (S.centers ∩ D).toFinset.card

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
  :
  S.centers = ⋃ (g : S.lattice), (g +ᵥ S.centers ∩ D) := by
  ext x
  simp only [Set.mem_iUnion, Subtype.exists, AddSubmonoid.mk_vadd, exists_prop]
  constructor
  · intro hx
    obtain ⟨g, hg₁, hg₂⟩ := S.unique_covers_of_centers hD_unique_covers ⟨x, hx⟩
    use -g
    simp only [neg_mem_iff, SetLike.coe_mem, true_and]
    obtain ⟨hy₁, hy₂⟩ := hg₁
    have : ∃ y : D, ↑y = g +ᵥ x := by use ⟨g +ᵥ x, hy₂⟩
    obtain ⟨y, hy⟩ := this
    suffices : x = -g +ᵥ (y : EuclideanSpace ℝ (Fin d))
    · rw [this] --, Subtype.coe_prop y]
      have hy' := Subtype.coe_prop y
      have hg' := Subtype.coe_prop g
      refine Set.vadd_mem_vadd_set ?h.intro.intro.a
      simp only [Set.mem_inter_iff, hy', and_true]
      rw [hy]
      -- Idea: closure under additive action
      sorry
    rw [hy, neg_vadd_vadd]
  · intro hexa
    obtain ⟨y, hy₁, hy₂⟩ := hexa
    rw [Set.vadd_set_inter, Set.mem_inter_iff] at hy₂
    obtain ⟨hy₂, hy₃⟩ := hy₂
    -- Idea: x = y +ᵥ g for some g in the lattice
    -- Then x = -g +ᵥ (y +ᵥ g) where -g is also in the lattice
    -- We can apply closure under action to this and the fact that (y +ᵥ g) is in the centers
    sorry

-- I hope these aren't outright wrong
instance HDivENNReal : HDiv ENNReal ℝ ENNReal := sorry
instance HMulENNReal : HMul ℝ ENNReal ENNReal := sorry

@[simp]
theorem PeriodicSpherePacking.periodic_density_formula (S : PeriodicSpherePacking d) :
  S.density = (S.numReps : ENNReal) /
    (Zlattice.covolume S.lattice) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) := by
  -- Is this necessary? Might be nice to have a basis- and bound-independent version of
  -- `PeriodicSpherePacking.density_eq`...
  sorry

@[simp]
theorem PeriodicSpherePacking.periodic_density_formula'
  (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
  (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D) :
  S.density = ((S.numReps' hd hD_isBounded) : ENNReal) /
    (Zlattice.covolume S.lattice) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) := by
  -- TODO: Reframe this in terms of `PeriodicSpherePacking.density_eq` and prove it
  sorry

theorem periodic_constant_eq_constant (hd : 0 < d) :
    PeriodicSpherePackingConstant d = SpherePackingConstant d := by
  sorry

variable {d : ℕ} (P : PeriodicSpherePacking d)

noncomputable def PeriodicSpherePacking.basis_index_equiv :
  (Module.Free.ChooseBasisIndex ℤ ↥P.lattice) ≃ (Fin d) := by
  refine Fintype.equivFinOfCardEq ?h
  rw [← FiniteDimensional.finrank_eq_card_chooseBasisIndex, Zlattice.rank ℝ P.lattice,
      finrank_euclideanSpace, Fintype.card_fin]

end Periodic_Packings

noncomputable section Misc

-- For some reason the following two instances seem to need restating...
instance (v : EuclideanSpace ℝ (Fin d)) : Decidable (v = 0) := Classical.propDecidable (v = 0)

instance : DecidableEq (EuclideanSpace ℝ (Fin d)) :=
  Classical.typeDecidableEq (EuclideanSpace ℝ (Fin d))

-- Now a small lemma from Fourier analysis:


-- Now a small lemma from Complex analysis:
local notation "conj" => starRingEnd ℂ
lemma Complex.exp_neg_real_I_eq_conj (x m : EuclideanSpace ℝ (Fin d)) :
  cexp (-(2 * ↑π * I * ↑⟪x, m⟫_ℝ)) = conj (cexp (2 * ↑π * I * ↑⟪x, m⟫_ℝ)) :=
  calc cexp (-(2 * ↑π * I * ↑⟪x, m⟫_ℝ))
  _ = Circle.exp (-2 * π * ⟪x, m⟫_ℝ)
      := by
          rw [Circle.exp_apply]
          push_cast
          ring_nf
  _ = conj (Circle.exp (2 * π * ⟪x, m⟫_ℝ))
      := by rw [mul_assoc, neg_mul, ← mul_assoc, ← Circle.coe_inv_eq_conj, Circle.exp_neg]
  _= conj (cexp (2 * ↑π * I * ↑⟪x, m⟫_ℝ))
      := by
          rw [Circle.exp_apply]
          apply congrArg conj
          push_cast
          ring_nf

end Misc
