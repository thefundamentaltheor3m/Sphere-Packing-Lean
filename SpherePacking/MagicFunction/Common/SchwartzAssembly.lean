/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SpherePacking.ForMathlib.RadialSchwartz.OneSided

/-!
# Schwartz assembly from six radial integrals

This module provides shared infrastructure for assembling a Schwartz function on
`EuclideanSpace ℝ (Fin 8)` from six one-dimensional radial integrals. Both the magic functions
`a` and `b` follow this pattern.

## Main definitions
* `MagicFunction.Common.schwartzSum6` -- the sum of 6 Schwartz functions
* `MagicFunction.Common.schwartzRadialSum6` -- the radial lift to `ℝ⁸`
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

/-- The radial sum decomposes as the sum of the six lifted components. -/
public theorem schwartzRadialSum6_eq_sum
    (f₁ f₂ f₃ f₄ f₅ f₆ : 𝓢(ℝ, ℂ)) :
    schwartzRadialSum6 f₁ f₂ f₃ f₄ f₅ f₆ =
      liftRadial f₁ + liftRadial f₂ + liftRadial f₃ +
      liftRadial f₄ + liftRadial f₅ + liftRadial f₆ := rfl

/-- Evaluate the radial sum at a point using `‖x‖^2`. -/
public theorem schwartzRadialSum6_apply
    (f₁ f₂ f₃ f₄ f₅ f₆ : 𝓢(ℝ, ℂ)) (x : ℝ⁸) :
    schwartzRadialSum6 f₁ f₂ f₃ f₄ f₅ f₆ x =
      f₁ (‖x‖ ^ 2) + f₂ (‖x‖ ^ 2) + f₃ (‖x‖ ^ 2) +
      f₄ (‖x‖ ^ 2) + f₅ (‖x‖ ^ 2) + f₆ (‖x‖ ^ 2) := by
  simp [schwartzRadialSum6, liftRadial, schwartzSum6,
    schwartzMap_multidimensional_of_schwartzMap_real, add_assoc]

/-- When the component functions agree with raw integrals on `0 ≤ r`,
the radial sum agrees with the sum of raw integrals at any point. -/
public theorem schwartzRadialSum6_eq_rawSum
    (f₁ f₂ f₃ f₄ f₅ f₆ : 𝓢(ℝ, ℂ))
    (g₁ g₂ g₃ g₄ g₅ g₆ : ℝ → ℂ)
    (h₁ : ∀ r, 0 ≤ r → (f₁ : ℝ → ℂ) r = g₁ r)
    (h₂ : ∀ r, 0 ≤ r → (f₂ : ℝ → ℂ) r = g₂ r)
    (h₃ : ∀ r, 0 ≤ r → (f₃ : ℝ → ℂ) r = g₃ r)
    (h₄ : ∀ r, 0 ≤ r → (f₄ : ℝ → ℂ) r = g₄ r)
    (h₅ : ∀ r, 0 ≤ r → (f₅ : ℝ → ℂ) r = g₅ r)
    (h₆ : ∀ r, 0 ≤ r → (f₆ : ℝ → ℂ) r = g₆ r)
    (x : ℝ⁸) :
    schwartzRadialSum6 f₁ f₂ f₃ f₄ f₅ f₆ x =
      g₁ (‖x‖ ^ 2) + g₂ (‖x‖ ^ 2) + g₃ (‖x‖ ^ 2) +
      g₄ (‖x‖ ^ 2) + g₅ (‖x‖ ^ 2) + g₆ (‖x‖ ^ 2) := by
  have hr : 0 ≤ ‖x‖ ^ 2 := sq_nonneg ‖x‖
  simp [schwartzRadialSum6_apply, h₁ _ hr, h₂ _ hr, h₃ _ hr, h₄ _ hr, h₅ _ hr, h₆ _ hr]

end

end MagicFunction.Common
