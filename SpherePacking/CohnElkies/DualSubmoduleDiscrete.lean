module
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice


/-!
# Discreteness of the dual lattice submodule

If `Λ` is a discrete `ℤ`-lattice in `R^d`, then the dual submodule defined using the inner product
is also discrete. This file provides the corresponding `DiscreteTopology` instance for
`LinearMap.BilinForm.dualSubmodule`.
-/

open scoped RealInnerProductSpace

open Module

namespace SpherePacking.CohnElkies

variable {d : ℕ}

/-- A discrete `ℤ`-lattice has a discrete dual submodule (for the Euclidean inner product). -/
public instance (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] :
    DiscreteTopology
      (LinearMap.BilinForm.dualSubmodule (B := innerₗ (EuclideanSpace ℝ (Fin d))) Λ) := by
  let ι := Module.Free.ChooseBasisIndex ℤ Λ
  let bZ : Basis ι ℤ Λ := Module.Free.chooseBasis ℤ Λ
  let bR : Basis ι ℝ (EuclideanSpace ℝ (Fin d)) := bZ.ofZLatticeBasis ℝ Λ
  have hB :
      LinearMap.BilinForm.Nondegenerate (innerₗ (EuclideanSpace ℝ (Fin d)) :
        LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin d))) := by
    constructor <;> intro x hx
    all_goals
      have : ⟪x, x⟫ = (0 : ℝ) := by
        simpa [innerₗ_apply_apply] using hx x
      exact inner_self_eq_zero.1 this
  have hdual :
      LinearMap.BilinForm.dualSubmodule (B := innerₗ (EuclideanSpace ℝ (Fin d))) Λ =
        Submodule.span ℤ
          (Set.range
            (LinearMap.BilinForm.dualBasis
              (B := innerₗ (EuclideanSpace ℝ (Fin d))) hB bR)) := by
    simpa [bR, bZ.ofZLatticeBasis_span (K := ℝ) (L := Λ)] using
      (LinearMap.BilinForm.dualSubmodule_span_of_basis (B := innerₗ (EuclideanSpace ℝ (Fin d)))
        (R := ℤ) (S := ℝ) (M := EuclideanSpace ℝ (Fin d)) hB bR)
  exact hdual ▸
    (inferInstance :
      DiscreteTopology (Submodule.span ℤ
        (Set.range
          (LinearMap.BilinForm.dualBasis (B := innerₗ (EuclideanSpace ℝ (Fin d))) hB bR))))

end SpherePacking.CohnElkies
