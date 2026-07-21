/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Seewoo Lee
-/
module

public import Mathlib

/-! # Radial Schwartz Functions

The plan for this PR is to define a type of Radial Schwartz functions (as a `structure` extending
`SchwartzMap`) and prove some basic properties about the type.

The first goal will be to prove that we have a `StarModule` instance on it, where the `star`
operation will be nothing but the Fourier transform. One key result needed for this is the fact
that the Fourier transform of a radial Schwartz function is radial itself, which can be found in
Appendix A (specifically, (A.23)) of Dan Romik's book *Topics in Complex Analysis*.

The second goal will be to show that we can construct a radial Schwartz function from a smooth,
rapidly decaying function on the nonnegative reals by composing with the norm squared, using this
whole multiplying-by-a-smooth-transition-function trick.
-/

@[expose] public section

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

structure RadialSchwartzMap extends SchwartzMap E F where
  radial : ∀ x y : E, ‖x‖ = ‖y‖ → toSchwartzMap x = toSchwartzMap y

section Rotation

open Module

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The reflection through the hyperplane orthogonal to a nonzero vector has determinant `-1`. -/
private theorem det_reflection_orthogonal_span_singleton [FiniteDimensional ℝ V] {v : V}
    (hv : v ≠ 0) : LinearMap.det (Submodule.reflection (ℝ ∙ v)ᗮ).toLinearMap = -1 := by
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal, finrank_span_singleton hv,
    pow_one]

/-- In a real inner product space that is not one-dimensional, two vectors have the same norm if
and only if there is a rotation (a linear isometry equivalence of determinant `1`) mapping one to
the other.

The hypothesis `finrank ℝ V ≠ 1` is necessary: in `ℝ` the only rotation is the identity, yet
`‖1‖ = ‖-1‖`. It holds both for finite-dimensional spaces of dimension `≠ 1` and for
infinite-dimensional spaces, where `finrank` is `0` and the determinant condition is vacuous
(by convention `LinearMap.det` is `1` there). The inner product structure also matters: in a
general normed space, linear isometries need not act transitively on spheres (e.g. `ℝ²` with the
sup norm). -/
theorem norm_eq_iff_exists_rotation (hV : finrank ℝ V ≠ 1) (x y : V) :
    ‖x‖ = ‖y‖ ↔ ∃ T : V ≃ₗᵢ[ℝ] V, LinearMap.det T.toLinearMap = 1 ∧ T x = y := by
  refine ⟨fun h => ?_, fun ⟨T, _, hTx⟩ => by rw [← hTx]; exact (T.norm_map x).symm⟩
  by_cases hfin : FiniteDimensional ℝ V
  · rcases eq_or_ne x y with rfl | hxy
    · exact ⟨.refl ℝ V, LinearMap.det_id, rfl⟩
    have hy : y ≠ 0 := by
      rintro rfl
      exact hxy (norm_eq_zero.mp (h.trans norm_zero))
    -- Since `V` is not a line, there is a nonzero vector `u` orthogonal to `y`.
    obtain ⟨u, hu_mem, hu⟩ : ∃ u ∈ (ℝ ∙ y)ᗮ, u ≠ 0 := by
      rw [← Submodule.ne_bot_iff]
      intro hbot
      exact hV (by
        rw [← finrank_span_singleton hy, Submodule.orthogonal_eq_bot_iff.mp hbot, finrank_top])
    -- Composing the reflection sending `x` to `y` with a reflection fixing `y` gives a rotation
    -- sending `x` to `y`.
    refine ⟨(Submodule.reflection (ℝ ∙ (x - y))ᗮ).trans (Submodule.reflection (ℝ ∙ u)ᗮ), ?_, ?_⟩
    · rw [show ((Submodule.reflection (ℝ ∙ (x - y))ᗮ).trans
            (Submodule.reflection (ℝ ∙ u)ᗮ)).toLinearMap =
          (Submodule.reflection (ℝ ∙ u)ᗮ).toLinearMap ∘ₗ
            (Submodule.reflection (ℝ ∙ (x - y))ᗮ).toLinearMap from rfl,
        LinearMap.det_comp, det_reflection_orthogonal_span_singleton hu,
        det_reflection_orthogonal_span_singleton (sub_ne_zero.mpr hxy)]
      norm_num
    · rw [LinearIsometryEquiv.trans_apply, Submodule.reflection_sub h]
      refine Submodule.reflection_mem_subspace_eq_self ?_
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left, real_inner_comm]
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp hu_mem
  · -- In infinite dimension every determinant is `1`, so the reflection sending `x` to `y`
    -- already counts as a rotation.
    exact ⟨Submodule.reflection (ℝ ∙ (x - y))ᗮ,
      LinearMap.det_eq_one_of_finrank_eq_zero (finrank_of_infinite_dimensional hfin) _,
      Submodule.reflection_sub h⟩

end Rotation
