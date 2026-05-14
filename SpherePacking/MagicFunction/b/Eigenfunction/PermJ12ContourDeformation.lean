module
public import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12Defs
public import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12Regularity
public import SpherePacking.Contour.PermJ12Contour
public import SpherePacking.ForMathlib.ScalarOneForm
import SpherePacking.Contour.MobiusInv.ContourChange
import SpherePacking.Contour.MobiusInv.Segments
import SpherePacking.Contour.MobiusInv.WedgeSet
import SpherePacking.Contour.Segments
import SpherePacking.Contour.MobiusInv.WedgeSetContour


/-!
# Perm J12 Contour Deformation

This file proves results such as `perm_J12_contour_h2`, `perm_J12_contour`.
-/

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology ModularForm MatrixGroups

open MagicFunction.b.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap

open SpherePacking SpherePacking.ForMathlib

section Integral_Permutations

open scoped Real

open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral


section PermJ12

open MeasureTheory Set Complex Real
open Filter
open scoped Interval ModularForm

/-- `Ψ₁' r` is `DiffContOnCl` on `wedgeSet`. -/
public lemma diffContOnCl_Ψ₁'_wedgeSet (r : ℝ) :
    DiffContOnCl ℝ (Ψ₁' r) wedgeSet := by
  refine ⟨((differentiableOn_Ψ₁'_upper (r := r)).restrictScalars ℝ).mono
    wedgeSet_subset_upperHalfPlaneSet, fun z hzcl => ?_⟩
  by_cases h1 : z = (1 : ℂ)
  · subst h1
    have hval : Ψ₁' r 1 = 0 := by simp [Ψ₁', ψT']
    simpa [ContinuousWithinAt, hval] using (tendsto_Ψ₁'_one_within_closure_wedgeSet (r := r))
  · exact ((differentiableOn_Ψ₁'_upper (r := r)).continuousOn.continuousAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
        (mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one hzcl h1))).continuousWithinAt

/-- The scalar one-form `scalarOneForm (Ψ₁' r)` is `DiffContOnCl` on `wedgeSet`. -/
public lemma diffContOnCl_ω_wedgeSet (r : ℝ) :
    DiffContOnCl ℝ (scalarOneForm (Ψ₁' r)) wedgeSet :=
  diffContOnCl_scalarOneForm (s := wedgeSet) (diffContOnCl_Ψ₁'_wedgeSet (r := r))

/-- Symmetry of the within-derivative of the scalar one-form on `wedgeSet`, i.e. `dω = 0`. -/
public lemma fderivWithin_ω_wedgeSet_symm (r : ℝ) :
    ∀ x ∈ wedgeSet, ∀ u ∈ tangentConeAt ℝ wedgeSet x, ∀ v ∈ tangentConeAt ℝ wedgeSet x,
      fderivWithin ℝ (scalarOneForm (Ψ₁' r)) wedgeSet x u v =
        fderivWithin ℝ (scalarOneForm (Ψ₁' r)) wedgeSet x v u := by
  intro x hx u _ v _
  simpa using
    (SpherePacking.ForMathlib.fderivWithin_scalarOneForm_symm_of_isOpen (f := Ψ₁' r)
      (s := wedgeSet) isOpen_wedgeSet hx (u := u) (v := v)
      ((differentiableOn_Ψ₁'_upper (r := r)).differentiableAt
        (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
          (wedgeSet_subset_upperHalfPlaneSet hx))))

/-- Sum of the two `Ψ₁_fourier` curve integrals on the left boundary equals minus the corresponding
sum of `Ψ₁'` curve integrals on the right boundary. -/
public lemma perm_J12_contour (r : ℝ) :
    (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + I),
          scalarOneForm (Ψ₁_fourier r) z) +
        ∫ᶜ z in Path.segment ((-1 : ℂ) + I) I,
          scalarOneForm (Ψ₁_fourier r) z =
      -((∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
            scalarOneForm (Ψ₁' r) z) +
          ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (Ψ₁' r) z) := by
  simpa using
    (SpherePacking.perm_J12_contour_mobiusInv_wedgeSet
      (Ψ₁_fourier := Ψ₁_fourier)
      (Ψ₁' := Ψ₁')
      (Ψ₁_fourier_eq_neg_deriv_mul := Ψ₁_fourier_eq_neg_deriv_mul)
      (closed_ω_wedgeSet := fun r =>
        ⟨diffContOnCl_ω_wedgeSet (r := r), fderivWithin_ω_wedgeSet_symm (r := r)⟩)
      (r := r))

end Integral_Permutations.PermJ12
end

end MagicFunction.b.Fourier
