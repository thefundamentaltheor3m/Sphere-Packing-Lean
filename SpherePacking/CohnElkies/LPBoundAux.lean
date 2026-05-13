module
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.Order.Filter.Cofinite

/-!
# Auxiliary summability for the LP bound

If `f` is Schwartz and `a + Λ` is a translate of a discrete `ℤ`-lattice, then the family of norms
`‖f (a + ℓ)‖` is summable over `ℓ : Λ`. Used to justify rearranging `tsum` expressions in the
Cohn-Elkies linear programming bound.
-/

open scoped SchwartzMap FourierTransform
open BigOperators

namespace SpherePacking.CohnElkies
variable {d : ℕ}

namespace LPBoundAux

variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]

/-- A Schwartz function has summable norms on any translate of a `ℤ`-lattice. -/
public lemma summable_norm_comp_add_zlattice (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (a : EuclideanSpace ℝ (Fin d)) :
    Summable (fun ℓ : Λ => ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖) := by
  let k : ℕ := Module.finrank ℤ Λ + 2
  obtain ⟨C, _hCpos, hC⟩ := f.decay k 0
  have hC' : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ k * ‖f x‖ ≤ C := fun x => by
    simpa [norm_iteratedFDeriv_zero] using hC x
  set b : EuclideanSpace ℝ (Fin d) := -a
  refine Summable.of_norm_bounded_eventually
    (f := fun ℓ : Λ => ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖)
    (g := fun ℓ : Λ => (C + 1) * ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖⁻¹ ^ k) ?_ ?_
  · simpa [mul_assoc] using
      (ZLattice.summable_norm_sub_inv_pow (L := Λ) (n := k) (by simp [k]) b).mul_left (C + 1)
  · have hClosed : IsClosed (X := EuclideanSpace ℝ (Fin d))
        (Λ : Set (EuclideanSpace ℝ (Fin d))) := by
      letI : DiscreteTopology Λ.toAddSubgroup := inferInstanceAs (DiscreteTopology Λ)
      simpa [Submodule.coe_toAddSubgroup] using
        AddSubgroup.isClosed_of_discrete (H := Λ.toAddSubgroup)
    have hFiniteBad :
        ({ℓ : Λ | ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ ≤ (1 : ℝ)} : Set Λ).Finite := by
      have hpre :
          ((fun ℓ : Λ => (ℓ : EuclideanSpace ℝ (Fin d))) ⁻¹'
              (Metric.closedBall b (1 : ℝ) ∩ (Λ : Set (EuclideanSpace ℝ (Fin d))))).Finite := by
        simpa using (Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
          Metric.isBounded_closedBall hClosed).preimage_embedding
          (f := (⟨Subtype.val, Subtype.coe_injective⟩ : Λ ↪ EuclideanSpace ℝ (Fin d)))
      simpa [Set.preimage, Metric.mem_closedBall, dist_eq_norm, and_true] using hpre
    refine hFiniteBad.subset ?_
    intro ℓ hfail
    by_contra hlarge
    have hlarge' : (1 : ℝ) < ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ := lt_of_not_ge hlarge
    have hpos : 0 < ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ ^ k :=
      pow_pos (lt_of_lt_of_le one_pos hlarge'.le) _
    have hdec :
        ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ ^ k *
          ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖ ≤ C := by
      have hnorm : ‖a + (ℓ : EuclideanSpace ℝ (Fin d))‖ = ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ := by
        simp [b, sub_eq_add_neg, add_comm]
      simpa [hnorm] using hC' (a + (ℓ : EuclideanSpace ℝ (Fin d)))
    have hmono :
        C / ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ ^ k ≤
          (C + 1) / ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ ^ k := by
      simpa [div_eq_mul_inv, mul_assoc] using
        mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1)
          (by positivity : 0 ≤ (‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ ^ k)⁻¹)
    refine hfail (by simpa [div_eq_mul_inv, inv_pow] using
      ((le_div_iff₀' hpos).2 hdec).trans (by simpa using hmono))

end LPBoundAux

namespace LPBoundSummability

open SpherePacking.CohnElkies.LPBoundAux

section ZLattice

variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]
variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (a : EuclideanSpace ℝ (Fin d))

/-- A Schwartz function is summable on any translate of a discrete `ℤ`-lattice. -/
public theorem summable_lattice_translate :
    Summable (fun ℓ : Λ => f (a + (ℓ : EuclideanSpace ℝ (Fin d)))) :=
  Summable.of_norm (summable_norm_comp_add_zlattice (Λ := Λ) f a)

/-- The real part of a Schwartz function is summable on any translate of a discrete `ℤ`-lattice. -/
public theorem summable_lattice_translate_re :
    Summable (fun ℓ : Λ => (f (a + (ℓ : EuclideanSpace ℝ (Fin d)))).re) :=
  Complex.reCLM.summable (summable_lattice_translate (Λ := Λ) f a)

end ZLattice

end LPBoundSummability

end SpherePacking.CohnElkies
