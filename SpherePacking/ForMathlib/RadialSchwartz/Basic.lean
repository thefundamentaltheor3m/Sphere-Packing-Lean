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

/- Transitivity of the orthogonal group on spheres requires an inner product: in a general normed
space, linear isometries need not act transitively on spheres (e.g. `ℝ²` with the sup norm). -/
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- In a real inner product space, any two vectors of the same norm are related by a rotation,
formalised here as a linear isometry equivalence. The witness is the reflection through the
hyperplane orthogonal to `x - y`. -/
theorem exists_linearIsometryEquiv_apply_eq_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) :
    ∃ T : V ≃ₗᵢ[ℝ] V, T x = y :=
  ⟨Submodule.reflection (ℝ ∙ (x - y))ᗮ, Submodule.reflection_sub h⟩

end Rotation
