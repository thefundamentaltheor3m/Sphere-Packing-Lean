module
public import SpherePacking.MagicFunction.a.Schwartz.Basic
public import SpherePacking.MagicFunction.a.Eigenfunction.PermI12WedgeDomain
public import SpherePacking.MagicFunction.a.Eigenfunction.PermI12Prelude
public import SpherePacking.Contour.MobiusInv.WedgeSet
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import SpherePacking.MagicFunction.a.Eigenfunction.PermI5Kernel
import SpherePacking.MagicFunction.a.Eigenfunction.PermI12FourierMain
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
import SpherePacking.ForMathlib.ScalarOneForm
import SpherePacking.Contour.MobiusInv.WedgeSetContour

/-!
# Fourier Permutations

We show that the Fourier transform permutes the integral pieces defining `a`, and deduce that `a`
is a Fourier eigenfunction.

## Main statements
* `eig_a`
-/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter
open Filter SpherePacking SpherePacking.ForMathlib

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section Integral_Permutations

/-- The `1`-form built from `Φ₃'` is differentiable on `wedgeSet` with continuous extension. -/
public lemma diffContOnCl_ω_wedgeSet (r : ℝ) :
    DiffContOnCl ℝ (scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r)) wedgeSet :=
  ForMathlib.diffContOnCl_scalarOneForm (s := wedgeSet) <| by
    refine ⟨((MagicFunction.a.ComplexIntegrands.Φ₃'_contDiffOn (r := r)).differentiableOn
        (by simp)).mono wedgeSet_subset_upperHalfPlaneSet, fun z hz => ?_⟩
    by_cases h1 : z = (1 : ℂ)
    · subst h1
      have hval : MagicFunction.a.ComplexIntegrands.Φ₃' r (1 : ℂ) = 0 := by
        simp [MagicFunction.a.ComplexIntegrands.Φ₃']
      simpa [ContinuousWithinAt, hval] using tendsto_Φ₃'_one_within_closure_wedgeSet (r := r)
    · have hzU : z ∈ UpperHalfPlane.upperHalfPlaneSet :=
        mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one hz h1
      exact ((MagicFunction.a.ComplexIntegrands.Φ₃'_contDiffOn (r := r)).continuousOn.continuousAt
        (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hzU)).continuousWithinAt

/-- Symmetry of the derivative of `scalarOneForm (Φ₃' r)` on `wedgeSet`.

This is the key hypothesis needed to apply the Poincare lemma. -/
public lemma fderivWithin_ω_wedgeSet_symm (r : ℝ) :
    ∀ x ∈ wedgeSet, ∀ u ∈ tangentConeAt ℝ wedgeSet x, ∀ v ∈ tangentConeAt ℝ wedgeSet x,
      fderivWithin ℝ (scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r)) wedgeSet x u v =
        fderivWithin ℝ (scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r))
          wedgeSet x v u := by
  intro x hx _ _ _ _
  have hxU : x ∈ UpperHalfPlane.upperHalfPlaneSet := wedgeSet_subset_upperHalfPlaneSet hx
  have hfdiff : DifferentiableAt ℂ (MagicFunction.a.ComplexIntegrands.Φ₃' r) x :=
    (MagicFunction.a.ComplexIntegrands.Φ₃'_holo (r := r)).differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hxU)
  exact SpherePacking.ForMathlib.fderivWithin_scalarOneForm_symm_of_isOpen
    (s := wedgeSet) isOpen_wedgeSet hx (hfdiff := hfdiff)

open MeasureTheory Set Complex Real

/-- The contour permutation identity underlying the Fourier invariance of the `I₁`/`I₂` part. -/
private lemma perm_I12_contour (r : ℝ) :
    (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
          scalarOneForm (Φ₁_fourier r) z) +
        ∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Φ₁_fourier r) z =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
            scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r) z) +
          ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r) z :=
  SpherePacking.perm_I12_contour_mobiusInv_wedgeSet
    (Ψ₁_fourier := Φ₁_fourier)
    (Ψ₁' := MagicFunction.a.ComplexIntegrands.Φ₃')
    (Ψ₁_fourier_eq_deriv_mul := Φ₁_fourier_eq_deriv_mobiusInv_mul_Φ₃')
    (closed_ω_wedgeSet := fun r =>
      ⟨diffContOnCl_ω_wedgeSet (r := r), fderivWithin_ω_wedgeSet_symm (r := r)⟩)
    (r := r)

theorem perm_I₁_I₂ :
    FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) (I₁ + I₂ : SchwartzMap ℝ⁸ ℂ) =
      (I₃ + I₄ : SchwartzMap ℝ⁸ ℂ) := by
  ext w
  simp only [FourierTransform.fourierCLE_apply, FourierAdd.fourier_add, add_apply, I₃_apply,
    I₄_apply, fourier_coe]
  rw [fourier_I₁_eq_curveIntegral (w := w), fourier_I₂_eq_curveIntegral (w := w),
    I₃'_add_I₄'_eq_curveIntegral_segments (r := ‖w‖ ^ 2)]
  simpa using perm_I12_contour (r := ‖w‖ ^ 2)

theorem perm_I₃_I₄ :
    FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) (I₃ + I₄ : SchwartzMap ℝ⁸ ℂ) =
      (I₁ + I₂ : SchwartzMap ℝ⁸ ℂ) := by
  rw [← perm_I₁_I₂]
  simpa using radial_inversion (I₁ + I₂) fun _ => by simp [I₁, I₂]

theorem perm_I₆ : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) I₆ = I₅ := by
  simpa [← perm_I₅] using radial_inversion I₅ fun _ => by
    simp [I₅, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply]

end Integral_Permutations

section Eigenfunction

/-- The magic function `a` is invariant under the Fourier transform. -/
public theorem eig_a : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) a = a := by
  rw [show a = I₁ + I₂ + I₃ + I₄ + I₅ + I₆ from rfl,
    show I₁ + I₂ + I₃ + I₄ + I₅ + I₆ = (I₁ + I₂) + (I₃ + I₄) + I₅ + I₆ by ac_rfl,
    map_add, map_add, map_add, perm_I₁_I₂, perm_I₅, perm_I₃_I₄, perm_I₆]
  ac_rfl

end Eigenfunction
end
end MagicFunction.a.Fourier
