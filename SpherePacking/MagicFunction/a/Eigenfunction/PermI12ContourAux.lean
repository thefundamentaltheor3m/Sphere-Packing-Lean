module
public import SpherePacking.MagicFunction.a.Eigenfunction.PermI12WedgeDomain
public import SpherePacking.MagicFunction.a.Eigenfunction.PermI12Prelude
public import SpherePacking.Contour.MobiusInv.WedgeSet
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
public import SpherePacking.Contour.MobiusInv.LineMap
import SpherePacking.ForMathlib.ScalarOneFormDiffContOnCl
import SpherePacking.ForMathlib.ScalarOneFormFDeriv


/-!
# Auxiliary lemmas for `perm_I12_contour`

We verify regularity and symmetry conditions needed to apply the Poincare lemma for curve
integrals of closed `1`-forms on the wedge domain `wedgeSet`.

## Main statements
* `diffContOnCl_ω_wedgeSet`
* `fderivWithin_ω_wedgeSet_symm`
-/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open Filter SpherePacking

section Integral_Permutations

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

private lemma diffContOnCl_Φ₃'_wedgeSet (r : ℝ) :
    DiffContOnCl ℝ (MagicFunction.a.ComplexIntegrands.Φ₃' r) wedgeSet := by
  refine ⟨?_, ?_⟩
  · have h :=
      (MagicFunction.a.ComplexIntegrands.Φ₃'_contDiffOn (r := r)).differentiableOn (by simp)
    exact h.mono wedgeSet_subset_upperHalfPlaneSet
  · intro z hz
    by_cases h1 : z = (1 : ℂ)
    · subst h1
      have hval : MagicFunction.a.ComplexIntegrands.Φ₃' r (1 : ℂ) = 0 := by
        simp [MagicFunction.a.ComplexIntegrands.Φ₃']
      have htend := tendsto_Φ₃'_one_within_closure_wedgeSet (r := r)
      -- `ContinuousWithinAt` is `Tendsto` to the value at the point.
      simpa [ContinuousWithinAt, hval] using htend
    · have hzU : z ∈ UpperHalfPlane.upperHalfPlaneSet :=
        mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one hz h1
      have hcontU :
          ContinuousAt (MagicFunction.a.ComplexIntegrands.Φ₃' r) z :=
        (MagicFunction.a.ComplexIntegrands.Φ₃'_contDiffOn (r := r)).continuousOn.continuousAt
          (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hzU)
      exact hcontU.continuousWithinAt

/-- The `1`-form built from `Φ₃'` is differentiable on `wedgeSet` with continuous extension. -/
public lemma diffContOnCl_ω_wedgeSet (r : ℝ) :
    DiffContOnCl ℝ (scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r)) wedgeSet :=
  ForMathlib.diffContOnCl_scalarOneForm (s := wedgeSet) (diffContOnCl_Φ₃'_wedgeSet (r := r))

/-- Symmetry of the derivative of `scalarOneForm (Φ₃' r)` on `wedgeSet`.

This is the key hypothesis needed to apply the Poincare lemma. -/
public lemma fderivWithin_ω_wedgeSet_symm (r : ℝ) :
    ∀ x ∈ wedgeSet, ∀ u ∈ tangentConeAt ℝ wedgeSet x, ∀ v ∈ tangentConeAt ℝ wedgeSet x,
      fderivWithin ℝ (scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r)) wedgeSet x u v =
        fderivWithin ℝ (scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r))
          wedgeSet x v u := by
  intro x hx u _ v _
  let f : ℂ → ℂ := MagicFunction.a.ComplexIntegrands.Φ₃' r
  have hxU : x ∈ UpperHalfPlane.upperHalfPlaneSet := wedgeSet_subset_upperHalfPlaneSet hx
  have hfdiff :
      DifferentiableAt ℂ f x :=
    (MagicFunction.a.ComplexIntegrands.Φ₃'_holo (r := r)).differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hxU)
  simpa [f] using
    (SpherePacking.ForMathlib.fderivWithin_scalarOneForm_symm_of_isOpen
      (f := f) (s := wedgeSet) isOpen_wedgeSet hx (hfdiff := hfdiff))


end Integral_Permutations

end
end MagicFunction.a.Fourier
