/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv


/-!
# Multidimensional

This file defines `schwartzMap_multidimensional_of_schwartzMap_real` and proves results such as
`hasFDerivAt_norm_sq`, `differentiableAt_norm_sq`, and `differentiable_norm_sq`.
-/

section SchwartzMap_multidimensional_of_schwartzMap_real

-- The `‖·‖²` differentiability helpers formerly here are now mathlib's
-- `hasStrictFDerivAt_norm_sq` / `DifferentiableAt.norm_sq` / `Differentiable.norm_sq`.

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : 𝓢(ℝ, ℂ))

/-- Lift a Schwartz function on `ℝ` to a Schwartz function on `F` by composing with `‖x‖ ^ 2`. -/
@[expose, simps!]
public noncomputable def schwartzMap_multidimensional_of_schwartzMap_real : 𝓢(F, ℂ) :=
    f.compCLM ℝ (Function.hasTemperateGrowth_norm_sq F) <| by
  use 1, 1
  intro _
  simp only [norm_pow, norm_norm]
  nlinarith

@[simp] lemma schwartzMap_multidimensional_of_schwartzMap_real_apply (x : F) :
    schwartzMap_multidimensional_of_schwartzMap_real (F := F) f x = f (‖x‖ ^ 2) := by
  simp [schwartzMap_multidimensional_of_schwartzMap_real]

end SchwartzMap_multidimensional_of_schwartzMap_real
