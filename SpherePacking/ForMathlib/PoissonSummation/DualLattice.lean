import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.BilinearForm.DualLattice

/-!
# The Dual Lattice

In this file, we build some basic theory about the dual lattice of a given `ZLattice`. We build on
API developed by Andrew Yang in `Mathlib.LinearAlgebra.BilinearForm.DualLattice`. We show that the
dual lattice with respect to a nondegenerate bilinear form on a lattice is itself a lattice, which
will allow us to construct an isomorphism with the canonical free ℤ-module of its rank.

Note that parts of this file can probably be generalised to `RCLike 𝕜`. We do not do this here.

## Main Definition
`ZLattice.Dual`: The dual of a `ZLattice` as a ℤ-submodule.

## Main Results
1. `ZLattice.Dual.eq_Zspan` : The dual of a `ZLattice` is the ℤ-span of its associated dual basis.
2. `ZLattice.Dual.instZLattice` : The dual of a `ZLattice` is itself a `ZLattice`.
-/

open LinearMap (BilinForm)
open ZLattice Submodule LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (B : BilinForm ℝ E) (hB : B.Nondegenerate)
variable (Λ : Submodule ℤ E) [hdiscrete : DiscreteTopology Λ] [hlattice : IsZLattice ℝ Λ]

section Preliminaries

end Preliminaries

/-- The dual of a `ZLattice` is its dual as a ℤ-submodule. -/
noncomputable def ZLattice.Dual : Submodule ℤ E := LinearMap.BilinForm.dualSubmodule B Λ

namespace ZLattice.Dual

section ZSpan

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Basis ι ℤ Λ)

/-- The dual of a `ZLattice` is the `ℤ`-span of the dual basis of its `ofZLatticeBasis`. -/
theorem eq_ZSpan : Dual B Λ = span ℤ (Set.range (B.dualBasis hB (b.ofZLatticeBasis ℝ))) := by
  simp only [← Basis.ofZLatticeBasis_span ℝ Λ b]
  exact BilinForm.dualSubmodule_span_of_basis B hB (b.ofZLatticeBasis ℝ)

end ZSpan

section ZLattice

/-
Note that #lint fails on this file because the following results have "arguments that are not
instance-implicit and do not appear in another instance-implicit argument or the return type."

I don't see a way around this...
-/

include hB in
/-- The dual of a `ZLattice` has the discrete topology. -/
instance instDiscreteTopology : DiscreteTopology (Dual B Λ) := by
  rw [eq_ZSpan B hB Λ (Module.Free.chooseBasis ℤ Λ)]
  -- infer_instance
  exact ZSpan.instDiscreteTopologySubtypeMemSubmoduleIntSpanRangeCoeBasisRealOfFinite
    (B.dualBasis hB (Basis.ofZLatticeBasis ℝ Λ (Module.Free.chooseBasis ℤ ↥Λ)))

include hB in
/-- The dual of a `ZLattice` is itself a `ZLattice`. -/
instance instIsZLattice [DiscreteTopology (Dual B Λ)] : IsZLattice ℝ (Dual B Λ) := by
  simp only [eq_ZSpan B hB Λ (Module.Free.chooseBasis ℤ Λ)]
  -- infer_instance
  exact instIsZLatticeRealSpan (B.dualBasis hB (Basis.ofZLatticeBasis ℝ Λ (Module.Free.chooseBasis ℤ ↥Λ)))

end ZLattice

end ZLattice.Dual
