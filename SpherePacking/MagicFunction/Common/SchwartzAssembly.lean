/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SpherePacking.ForMathlib.RadialSchwartz.OneSided

/-!
# Schwartz assembly from six radial integrals

Shared infrastructure for assembling a Schwartz function on `EuclideanSpace ℝ (Fin 8)` from
six one-dimensional radial integrals. Both magic functions `a` and `b` follow this pattern.

## Main definitions
* `MagicFunction.Common.schwartzSum6` -- sum of 6 Schwartz functions
* `MagicFunction.Common.schwartzRadialSum6` -- radial lift to `ℝ⁸`
-/

namespace MagicFunction.Common

noncomputable section

open SchwartzMap RadialSchwartz.Bridge

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

/-- The sum of six one-dimensional Schwartz functions. -/
@[expose] public def schwartzSum6 (f₁ f₂ f₃ f₄ f₅ f₆ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  f₁ + f₂ + f₃ + f₄ + f₅ + f₆

/-- Lift a one-dimensional Schwartz function to a radial Schwartz function on `ℝ⁸`. -/
@[expose] public def liftRadial (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ⁸, ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real ℝ⁸ f

/-- The sum of six radial Schwartz functions on `ℝ⁸`. -/
@[expose] public def schwartzRadialSum6 (f₁ f₂ f₃ f₄ f₅ f₆ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ⁸, ℂ) :=
  liftRadial (schwartzSum6 f₁ f₂ f₃ f₄ f₅ f₆)

/-- Evaluate the radial sum at a point using `‖x‖^2`. -/
public theorem schwartzRadialSum6_apply (f₁ f₂ f₃ f₄ f₅ f₆ : 𝓢(ℝ, ℂ)) (x : ℝ⁸) :
    schwartzRadialSum6 f₁ f₂ f₃ f₄ f₅ f₆ x =
      f₁ (‖x‖ ^ 2) + f₂ (‖x‖ ^ 2) + f₃ (‖x‖ ^ 2) +
      f₄ (‖x‖ ^ 2) + f₅ (‖x‖ ^ 2) + f₆ (‖x‖ ^ 2) := by
  simp [schwartzRadialSum6, liftRadial, schwartzSum6,
    schwartzMap_multidimensional_of_schwartzMap_real, add_assoc]

end

end MagicFunction.Common
