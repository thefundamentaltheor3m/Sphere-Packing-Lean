module
public import SpherePacking.MagicFunction.a.Eigenfunction.PermI12Prelude
public import SpherePacking.MagicFunction.a.Basic
import SpherePacking.MagicFunction.a.Eigenfunction.PermI12ContourAux
import SpherePacking.Contour.MobiusInv.WedgeSetContour


/-!
# Contour permutation for `I₁` and `I₂`

We apply the general wedge-domain contour permutation lemma to the integrands defining `I₁` and
`I₂`, reducing the identity to the hypotheses verified in `PermI12ContourAux`.

## Main statements
* `perm_I12_contour`
-/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open Filter SpherePacking

section Integral_Permutations

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open MeasureTheory Set Complex Real
open scoped Interval

/-- The contour permutation identity underlying the Fourier invariance of the `I₁`/`I₂` part. -/
public lemma perm_I12_contour (r : ℝ) :
    (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + I),
          scalarOneForm (Φ₁_fourier r) z) +
        ∫ᶜ z in Path.segment ((-1 : ℂ) + I) I,
          scalarOneForm (Φ₁_fourier r) z =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
            scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r) z) +
          ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r) z := by
  simpa using
    (SpherePacking.perm_I12_contour_mobiusInv_wedgeSet
      (Ψ₁_fourier := Φ₁_fourier)
      (Ψ₁' := MagicFunction.a.ComplexIntegrands.Φ₃')
      (Ψ₁_fourier_eq_deriv_mul := Φ₁_fourier_eq_deriv_mobiusInv_mul_Φ₃')
      (closed_ω_wedgeSet := fun r =>
        ⟨diffContOnCl_ω_wedgeSet (r := r), fderivWithin_ω_wedgeSet_symm (r := r)⟩)
      (r := r))


end Integral_Permutations

end
end MagicFunction.a.Fourier
