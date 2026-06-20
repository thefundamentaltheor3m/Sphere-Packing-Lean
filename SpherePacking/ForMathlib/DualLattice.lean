/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Data.Real.Hom
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice

/-! # The dual of a `ℤ`-lattice is a discrete `ℤ`-lattice

For a nondegenerate bilinear form `B` on a finite-dimensional real vector space `M`, the dual
`ℤ`-submodule `B.dualSubmodule Λ` of a full `ℤ`-lattice `Λ` is again discrete: by
`BilinForm.dualSubmodule_span_of_basis` it is spanned by the dual basis of an integral basis of
`Λ`, hence is itself the span of an `ℝ`-basis, i.e. a `ℤ`-lattice.

This closes part of the TODO in `Mathlib/LinearAlgebra/BilinearForm/DualLattice.lean`
("Properly develop the material in the context of lattices"). For the Euclidean inner product the
nondegeneracy hypothesis is automatic, so we additionally register the discreteness as an instance
(`instDiscreteTopology_dualSubmodule_innerₗ` below); this is what the Cohn–Elkies linear-programming
bound consumes when summing over the dual lattice.

Upstream target: `Mathlib/LinearAlgebra/BilinearForm/DualLattice.lean` (plus the inner-product
instance near `Mathlib/Analysis/InnerProductSpace/`). At upstreaming time one would also add the
companion `IsZLattice ℝ (B.dualSubmodule Λ)` (not needed here — the LP bound consumes only
discreteness). Imports here are left as `public import Mathlib`; they are narrowed at upstreaming
time.
-/

open scoped RealInnerProductSpace
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]

/-- The dual of a full `ℤ`-lattice with respect to a nondegenerate bilinear form is discrete: it
is spanned by the dual basis of an integral basis of the lattice. -/
public theorem discreteTopology_dualSubmodule {B : BilinForm ℝ M} (hB : B.Nondegenerate)
    (Λ : Submodule ℤ M) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    DiscreteTopology (B.dualSubmodule Λ) := by
  -- `bZ` is an integral basis of `Λ`; its `B`-dual basis spans the dual submodule.
  let bZ := Module.Free.chooseBasis ℤ Λ
  have hspan : B.dualSubmodule Λ =
      Submodule.span ℤ (Set.range (B.dualBasis hB (bZ.ofZLatticeBasis ℝ Λ))) := by
    simpa [bZ.ofZLatticeBasis_span (K := ℝ) (L := Λ)] using
      dualSubmodule_span_of_basis (B := B) (R := ℤ) (S := ℝ) hB (bZ.ofZLatticeBasis ℝ Λ)
  exact hspan ▸ inferInstance

end LinearMap.BilinForm

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The dual of a full `ℤ`-lattice for the Euclidean inner product is discrete. The nondegeneracy
of `innerₗ E` is automatic (`⟪x, x⟫ = 0 ↔ x = 0`), so this is an instance. -/
public instance instDiscreteTopology_dualSubmodule_innerₗ [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    DiscreteTopology (LinearMap.BilinForm.dualSubmodule (innerₗ E) Λ) :=
  LinearMap.BilinForm.discreteTopology_dualSubmodule
    (by constructor <;> intro x hx <;>
      exact inner_self_eq_zero.1 (by simpa [innerₗ_apply_apply] using hx x : ⟪x, x⟫ = (0 : ℝ))) Λ

end InnerProduct
