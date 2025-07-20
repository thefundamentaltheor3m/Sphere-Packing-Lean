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
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.RCLike.Inner
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Compactness.PseudometrizableLindelof
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular

import SpherePacking.Basic.SpherePacking
import SpherePacking.Basic.PeriodicPacking
import SpherePacking.ForMathlib.InvPowSummability

open BigOperators Bornology

variable {d : ℕ} [Fact (0 < d)]
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]


-- noncomputable section Dual_Lattice

-- /-
-- This section defines the Dual Lattice of a Lattice. Taken from
-- `SpherePacking/ForMathlib/Dual.lean`.
-- -/

-- def bilinFormOfRealInner.dualSubmodule : AddSubgroup (EuclideanSpace ℝ (Fin d)) where
-- carrier := { x | ∀ l : Λ, ∃ n : ℤ, ⟪x, l⟫_[ℝ] = ↑n }
-- zero_mem' := by
-- simp only [Subtype.forall, Set.mem_setOf_eq, inner_zero_left]
-- intro a _
-- use 0
-- rw [Int.cast_zero]
-- add_mem' := by
-- intros x y hx hy l
-- obtain ⟨n, hn⟩ := hx l
-- obtain ⟨m, hm⟩ := hy l
-- use n + m
-- simp only [inner_add_left, hn, hm, Int.cast_add]
-- neg_mem' := by
-- intros x hx l
-- obtain ⟨n, hn⟩ := hx l
-- use -n
-- simp only [inner_neg_left, hn, Int.cast_neg]

-- end Dual_Lattice

section Euclidean_Space

instance instNonemptyFin : Nonempty (Fin d) := ⟨0, Fact.out⟩
  -- rw [← Fintype.card_pos_iff, Fintype.card_fin]
  -- exact Fact.out

-- noncomputable instance : DivisionCommMonoid ENNReal where
-- inv_inv := inv_inv
-- mul_inv_rev := sorry
-- inv_eq_of_mul := sorry
-- mul_comm := sorry


end Euclidean_Space

open scoped FourierTransform

open Complex Real
open LinearMap (BilinForm)

noncomputable section PSF_L

-- instance inst₁ : IsScalarTower ℤ ℝ (EuclideanSpace ℝ (Fin d)) := AddCommGroup.intIsScalarTower

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
  ∑' ℓ : Λ, f (v + ℓ) = (1 / ZLattice.covolume Λ) *
    ∑' m : bilinFormOfRealInner.dualSubmodule Λ,
  (𝓕 f m) * exp (2 * π * I * ⟪v, m⟫_[ℝ]) :=
  sorry

-- The version below is on the blueprint. I'm pretty sure it can be removed.
theorem PSF_L' {f : EuclideanSpace ℝ (Fin d) → ℂ} (hf : PSF_Conditions f) :
  ∑' ℓ : Λ, f ℓ = (1 / ZLattice.covolume Λ) * ∑' m : bilinFormOfRealInner.dualSubmodule Λ, (𝓕 f m)
    := by
  simpa using PSF_L Λ hf 0

namespace SchwartzMap

theorem PoissonSummation_Lattices (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)
  (v : EuclideanSpace ℝ (Fin d)) : ∑' ℓ : Λ, f (v + ℓ) = (1 / ZLattice.covolume Λ) *
  ∑' m : bilinFormOfRealInner.dualSubmodule Λ, (𝓕 f m) * exp (2 * π * I * ⟪v, m⟫_[ℝ]) := by
  sorry

-- theorem PoissonSummation_Lattices' (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) :
-- ∑' ℓ : Λ, f ℓ = (1 / ZLattice.covolume Λ) * ∑' m : bilinFormOfRealInner.dualSubmodule Λ, (𝓕 f m)
--   := by
-- sorry

end SchwartzMap

end PSF_L

open scoped FourierTransform

section FourierSchwartz

namespace SchwartzMap

variable (𝕜 : Type*) [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
    [CompleteSpace E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  (f : 𝓢(V, E))

include 𝕜 in
@[simp]
theorem fourierInversion : 𝓕⁻ (𝓕 f) = f := by
  rw [← fourierTransformCLE_apply 𝕜 f,
      ← fourierTransformCLE_symm_apply 𝕜 _,
      ContinuousLinearEquiv.symm_apply_apply]

end SchwartzMap

end FourierSchwartz

section Positivity_on_Nhd

-- TODO: PR this to Mathlib (very useful!)
-- Or was I just not able to find it...

variable {E : Type*} [TopologicalSpace E]

theorem Continuous.pos_iff_exists_nhd_pos {f : E → ℝ} (hf₁ : Continuous f) (x : E) :
  0 < f x ↔ ∃ U ∈ (nhds x), ∀ y ∈ U, 0 < f y := by
  constructor
  · intro hx
    suffices ∀ᶠ y in nhds x, 0 < f y by
      rw [Filter.eventually_iff] at this
      refine ⟨_, this, by simp⟩
    exact hf₁.tendsto x (eventually_gt_nhds hx)
  · intro hexistsnhd
    obtain ⟨U, hU₁, hU₂⟩ := hexistsnhd
    specialize hU₂ x (mem_of_mem_nhds hU₁)
    exact hU₂

open MeasureTheory

variable [MeasureSpace E] [BorelSpace E]

theorem Continuous.pos_iff_exists_measurable_nhd_pos {f : E → ℝ} (hf₁ : Continuous f) (x : E) :
  0 < f x ↔ ∃ U ∈ (nhds x), MeasurableSet U ∧ ∀ y ∈ U, 0 < f y := by
  constructor
  · intro hposatx
    have h₁ : ContinuousAt f x := continuousAt hf₁
    rw [continuousAt_def] at h₁
    have h₁' : Set.Ioo (f x / 2) (3 * f x / 2) ∈ nhds (f x) := by
      apply Ioo_mem_nhds (div_two_lt_of_pos hposatx) ?_
      linarith
    specialize h₁ (Set.Ioo (f x / 2) (3 * f x / 2)) h₁'
    use (f ⁻¹' Set.Ioo (f x / 2) (3 * f x / 2))
    constructor
    · exact h₁
    · constructor
      · exact hf₁.measurable measurableSet_Ioo
      · intro y hy
        have h₂ : f y ∈ Set.Ioo (f x / 2) (3 * f x / 2) := hy
        rw [Set.mem_Ioo] at h₂
        linarith
  · intro hnhx
    obtain ⟨U, hU₁, _, hU₃⟩ := hnhx
    exact (hf₁.pos_iff_exists_nhd_pos x).mpr ⟨U, hU₁, hU₃⟩

end Positivity_on_Nhd

section Integration

open MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [MeasureSpace E] [BorelSpace E]
variable [(volume : Measure E).IsAddLeftInvariant] [(volume : Measure E).Regular]
  [NeZero (volume : Measure E)] -- More Generality Possible?

instance : (volume : Measure E).IsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_regular

theorem Continuous.integral_zero_iff_zero_of_nonneg {f : E → ℝ} (hf₁ : Continuous f)
  (hf₂ : Integrable f) (hnn : ∀ x, 0 ≤ f x) : ∫ (v : E), f v = 0 ↔ f = 0 := by
  /- Informal proof:
  ← is obvious. Now, assume the integral is zero. Suppose, for contradiction, that f ≠ 0.
  Then, there is a point x at which 0 < f x. So, there is a neighbourhood of x at which
  0 < f. The integral over this neighbourhood has to be positive, but less than that over
  the entire space. This is a contradiction.
  -/
  constructor
  · intro hintf
    by_contra hne
    -- Get an x at which f x ≠ 0
    obtain ⟨x, hneatx⟩ := Function.ne_iff.mp fun a ↦ hne (id (Eq.symm a))
    have hposatx : 0 < f x := lt_of_le_of_ne (hnn x) hneatx
    -- Get a neighbourhood of x at which f is positive
    obtain ⟨U, hU₁, hU₃⟩ := (hf₁.pos_iff_exists_nhd_pos x).mp hposatx
    -- Compare the integral over this neighbourhood to the integral over the entire space
    have hintgleintf : ∫ (v : E) in U, f v ≤ ∫ (v : E), f v := by
      refine integral_mono_measure Measure.restrict_le_self ?_ hf₂
      simp only [EventuallyLE, Pi.zero_apply, hnn, eventually_true]
    have hintgpos : 0 < ∫ (v : E) in U, f v := by
      refine (integral_pos_iff_support_of_nonneg hnn (Integrable.restrict hf₂)).mpr ?_
      suffices hUpos : 0 < (volume.restrict U) U
      · dsimp [Function.support]
        suffices hInclusion : U ⊆ {x | f x ≠ 0}
        · have : (volume.restrict U) U ≤ (volume.restrict U) {x | f x ≠ 0} := by
            rw [Measure.restrict_apply_self, Measure.restrict_apply_superset hInclusion]
          exact lt_of_lt_of_le hUpos this
        intro y hy
        rw [Set.mem_setOf_eq]
        specialize hU₃ y hy
        exact Ne.symm (ne_of_lt hU₃)
      rw [Measure.restrict_apply_self]
      exact MeasureTheory.Measure.measure_pos_of_mem_nhds volume hU₁
    linarith
  · intro hf
    simp only [hf, Pi.zero_apply]
    exact integral_zero E ℝ

example {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf₁ : Continuous f) (hf₂ : Integrable f)
  (hnn : ∀ x, 0 ≤ f x) : ∫ (v : EuclideanSpace ℝ (Fin d)), f v = 0 ↔ f = 0 :=
  hf₁.integral_zero_iff_zero_of_nonneg hf₂ hnn

namespace SchwartzMap

theorem toFun_eq_zero_iff_zero {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (f : 𝓢(E, F)) : (f : E → F) = 0 ↔ f = 0 := by
  constructor
  · exact fun a ↦ SchwartzMap.ext (congrFun a)
  · intro hf
    rw [hf]
    exact coeFn_zero

omit [Fact (0 < d)] in
theorem integral_zero_iff_zero_of_nonneg {f : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)}
  (hnn : ∀ x, 0 ≤ f x) : ∫ (v : EuclideanSpace ℝ (Fin d)), f v = 0 ↔ f = 0 := by
  simp [← f.toFun_eq_zero_iff_zero]
  exact f.continuous.integral_zero_iff_zero_of_nonneg f.integrable hnn

end SchwartzMap

end Integration

noncomputable section Misc

-- For some reason the following two instances seem to need restating...
instance (v : EuclideanSpace ℝ (Fin d)) : Decidable (v = 0) := Classical.propDecidable (v = 0)

instance : DecidableEq (EuclideanSpace ℝ (Fin d)) :=
  Classical.typeDecidableEq (EuclideanSpace ℝ (Fin d))

omit [Fact (0 < d)]
-- Now a small theorem from Complex analysis:
local notation "conj" => starRingEnd ℂ
theorem Complex.exp_neg_real_I_eq_conj (x m : EuclideanSpace ℝ (Fin d)) :
  cexp (-(2 * ↑π * I * ↑⟪x, m⟫_[ℝ])) = conj (cexp (2 * ↑π * I * ↑⟪x, m⟫_[ℝ])) :=
  calc cexp (-(2 * ↑π * I * ↑⟪x, m⟫_[ℝ]))
  _ = Circle.exp (-2 * π * ⟪x, m⟫_[ℝ])
      := by
          rw [Circle.coe_exp]
          push_cast
          ring_nf
  _ = conj (Circle.exp (2 * π * ⟪x, m⟫_[ℝ]))
      := by rw [mul_assoc, neg_mul, ← mul_assoc, ← Circle.coe_inv_eq_conj, Circle.exp_neg]
  _= conj (cexp (2 * ↑π * I * ↑⟪x, m⟫_[ℝ]))
      := by
          rw [Circle.coe_exp]
          apply congrArg conj
          push_cast
          ring_nf

end Misc
