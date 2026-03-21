module
public import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12Defs
public import SpherePacking.Contour.PermJ12Contour
public import SpherePacking.ForMathlib.ScalarOneForm
import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12DiffContOnCl
import SpherePacking.Contour.MobiusInv.ContourChange
import SpherePacking.Contour.MobiusInv.LineMap
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

open SpherePacking

section Integral_Permutations

open scoped Real

open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral


section PermJ12

open MeasureTheory Set Complex Real
open Filter
open scoped Interval ModularForm

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
