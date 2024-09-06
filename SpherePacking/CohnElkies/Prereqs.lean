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
import SpherePacking.ForMathlib.InvPowSummability

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

section Euclidean_Space

instance instNonemptyFin : Nonempty (Fin d) := by
  rw [← Fintype.card_pos_iff, Fintype.card_fin]
  exact Fact.out

-- noncomputable instance : DivisionCommMonoid ENNReal where
--   inv_inv := inv_inv
--   mul_inv_rev := sorry
--   inv_eq_of_mul := sorry
--   mul_comm := sorry


end Euclidean_Space

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

namespace SchwartzMap

theorem PoissonSummation_Lattices (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)
  (v : EuclideanSpace ℝ (Fin d)) : ∑' ℓ : Λ, f (v + ℓ) = (1 / Zlattice.covolume Λ) *
  ∑' m : DualLattice Λ, (𝓕 f m) * exp (2 * π * I * ⟪v, m⟫_ℝ) := by
  sorry

-- theorem PoissonSummation_Lattices' (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) :
--   ∑' ℓ : Λ, f ℓ = (1 / Zlattice.covolume Λ) * ∑' m : DualLattice Λ, (𝓕 f m) := by
--   sorry

end SchwartzMap

end PSF_L

open scoped FourierTransform

section FourierSchwartz

namespace SchwartzMap

variable (𝕜 : Type*) [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E] [CompleteSpace E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  (f : 𝓢(V, E))

include 𝕜 in
theorem fourierInversion : 𝓕⁻ (𝓕 f) = f := by
  rw [← fourierTransformCLE_apply 𝕜 f,
      ← fourierTransformCLE_symm_apply 𝕜 _,
      ContinuousLinearEquiv.symm_apply_apply]

end SchwartzMap

end FourierSchwartz

noncomputable section Misc

-- For some reason the following two instances seem to need restating...
instance (v : EuclideanSpace ℝ (Fin d)) : Decidable (v = 0) := Classical.propDecidable (v = 0)

instance : DecidableEq (EuclideanSpace ℝ (Fin d)) :=
  Classical.typeDecidableEq (EuclideanSpace ℝ (Fin d))

-- Now a small theorem from Complex analysis:
local notation "conj" => starRingEnd ℂ
theorem Complex.exp_neg_real_I_eq_conj (x m : EuclideanSpace ℝ (Fin d)) :
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
