import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # A Few Facts that Hold in Euclidean Spaces

The contents of this file should, in my opinion, be in Mathlib. I'm not sure about tagging them with
`simp`, but they seem `simp`able... not sure about this.
-/

namespace EuclideanSpace

variable {ι : Type*} {𝕜 : Type*} [RCLike 𝕜] [DecidableEq ι]

section single

/-!
The results in this section are relevant to my attempt to build a canonical lattice in Euclidean
space. I got close, but there are certain results in `Mathlib` that better suit spaces of the form
`ι → ℝ` (that is, Pi types that have not been endowed with the additional structure of the
Euclidean inner product, norm, and metric). These are still nice results, though.
-/

/-- Multiplying `EuclideanSpace.single` by scalars results in a `EuclideanSpace.single`. -/
@[simp]
theorem smul_single (i : ι) (r s : 𝕜) :
    s • EuclideanSpace.single i r = EuclideanSpace.single i (s * r) := by
  ext i
  simp only [PiLp.smul_apply, EuclideanSpace.single_apply, smul_eq_mul, mul_ite, mul_zero]


-- We also add a version of this that is compatible with `EuclideanSpace.single i 1`, because such
-- vectors come up often (as they form bases).
@[simp]
theorem smul_single_one (i : ι) (s : 𝕜) :
    s • EuclideanSpace.single i 1 = EuclideanSpace.single i s := by
  rw [smul_single, mul_one]

/- TODO(bump)
@[simp]
theorem sum_smul_single_one [Fintype ι] (v : ι → 𝕜) :
    ∑ i : ι, (v i) • EuclideanSpace.single i 1 = WithLp.toLp 2 v := by
  ext j; simp; rw [Fintype.sum_apply]; simp

@[simp]
theorem sum_single [Fintype ι] (v : ι → 𝕜) : ∑ i : ι, EuclideanSpace.single i (v i) = v := by
  ext j; rw [Fintype.sum_apply]; simp
-/

end single

section zero

variable [IsEmpty ι]

noncomputable def ofIsEmpty : EuclideanSpace 𝕜 ι ≃ₗ[𝕜] (0 : Submodule 𝕜 (EuclideanSpace 𝕜 ι)) :=
    LinearEquiv.ofFinrankEq _ _ <| by
  haveI : Fintype ι := Fintype.ofIsEmpty
  calc Module.finrank 𝕜 (EuclideanSpace 𝕜 ι)
  _ = 0 := by rw [finrank_euclideanSpace, Fintype.card_eq_zero]
  _ = Module.finrank 𝕜 (0 : Submodule 𝕜 (EuclideanSpace 𝕜 ι)) := by simp

end zero
end EuclideanSpace
