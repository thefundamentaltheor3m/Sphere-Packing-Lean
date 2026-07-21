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

section Radial_Functions

namespace Function

variable {E F : Type*} [Norm E] [Norm F]

def IsRadial (f : E → F) : Prop := ∀ {x y : E}, ‖x‖ = ‖y‖ → f x = f y

end Function



-- Do some work on rotations. See here: https://www.math.columbia.edu/~woit/fourier-analysis/higherdimensions.pdf

#check ContinuousLinearMap.rotation
#check Matrix.orthogonalGroup
#check Matrix.specialOrthogonalGroup

end Radial_Functions

section RadialSchwartz

open SchwartzMap

@[simps]
def RadialSchwartzMap (E F : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Submodule ℝ 𝓢(E, F) where
  carrier := {f | Function.IsRadial f}
  add_mem' := by grind [Function.IsRadial]
  zero_mem' := by simp [Function.IsRadial]
  smul_mem' := by grind [Function.IsRadial]

section fourier

open SchwartzMap Real FourierTransform

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [NormedSpace ℂ F]

lemma radialSchwartzMap_map_le : (RadialSchwartzMap E F).map
    (fourierTransformCLM ℝ (V := E) (E := F)).toLinearMap ≤ RadialSchwartzMap E F := by
  intro f hf x y hxy
  simp only [Submodule.mem_map, ContinuousLinearMap.coe_coe, fourierTransformCLM_apply] at hf
  obtain ⟨g, hg, hg_fourier⟩ := hf
  rw [← hg_fourier, SchwartzMap.fourier_coe, Real.fourier_eq g x, Real.fourier_eq g y]
  congr with v
  congr 1
  sorry

#check FourierTransform.fourier
#check SchwartzMap.instFourierTransform.fourier

end fourier

end RadialSchwartz
