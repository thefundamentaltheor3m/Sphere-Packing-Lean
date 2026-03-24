module
public import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12Regularity
import SpherePacking.ForMathlib.ScalarOneFormDiffContOnCl
import SpherePacking.ForMathlib.ScalarOneFormFDeriv
import SpherePacking.Contour.PermJ12DiffContOnCl

/-!
# Perm J12 Diff Cont On Cl (Dim 8)

This file proves `DiffContOnCl` for `Ψ₁'` and `scalarOneForm (Ψ₁' _)` on `wedgeSet`, together with
the `dω = 0` symmetry predicate needed for the Poincaré-lemma based contour deformation.
-/

namespace MagicFunction.b.Fourier

noncomputable section

open scoped Interval Topology RealInnerProductSpace UpperHalfPlane Manifold

open MeasureTheory Set Complex Real Filter SpherePacking.ForMathlib
open SpherePacking

section Integral_Permutations

section PermJ12

/-- `Ψ₁' r` is `DiffContOnCl` on `wedgeSet`. -/
public lemma diffContOnCl_Ψ₁'_wedgeSet (r : ℝ) :
    DiffContOnCl ℝ (Ψ₁' r) wedgeSet := by
  refine SpherePacking.Contour.diffContOnCl_wedgeSet_of (f := Ψ₁' r)
    (differentiableOn_Ψ₁'_upper (r := r)) ?_ ?_
  · simpa using (tendsto_Ψ₁'_one_within_closure_wedgeSet (r := r))
  · simp [Ψ₁', ψT']

/-- The scalar one-form `scalarOneForm (Ψ₁' r)` is `DiffContOnCl` on `wedgeSet`. -/
public lemma diffContOnCl_ω_wedgeSet (r : ℝ) :
    DiffContOnCl ℝ (scalarOneForm (Ψ₁' r)) wedgeSet :=
  diffContOnCl_scalarOneForm (s := wedgeSet) (diffContOnCl_Ψ₁'_wedgeSet (r := r))

/-- Symmetry of the within-derivative of the scalar one-form on `wedgeSet`, i.e. `dω = 0`. -/
public lemma fderivWithin_ω_wedgeSet_symm (r : ℝ) :
    ∀ x ∈ wedgeSet, ∀ u ∈ tangentConeAt ℝ wedgeSet x, ∀ v ∈ tangentConeAt ℝ wedgeSet x,
      fderivWithin ℝ (scalarOneForm (Ψ₁' r)) wedgeSet x u v =
        fderivWithin ℝ (scalarOneForm (Ψ₁' r)) wedgeSet x v u := by
  simpa using (SpherePacking.Contour.fderivWithin_scalarOneForm_wedgeSet_symm_of (f := Ψ₁' r)
    (hdiffC := differentiableOn_Ψ₁'_upper (r := r)))

end PermJ12
end Integral_Permutations

end

end MagicFunction.b.Fourier
