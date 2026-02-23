/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module
public import SpherePacking.MagicFunction.b.psi
public import SpherePacking.MagicFunction.IntegralParametrisations

/-!
# Defining integrals for `b`

This file defines the six contour integrals `J₁'`-`J₆'` used to build the magic function `b`.
The prime indicates the radial profile as a function of the real parameter `x = ‖v‖^2`; the
unprimed versions `J₁`-`J₆` are the induced functions on `EuclideanSpace ℝ (Fin 8)`.

## Main definitions
* `MagicFunction.b.RealIntegrals.J₁'` ... `J₆'`, `MagicFunction.b.RealIntegrals.b'`
* `MagicFunction.b.RadialFunctions.J₁` ... `J₆`, `MagicFunction.b.RadialFunctions.b`

## Main statement
* `MagicFunction.b.RadialFunctions.b_eq`
-/

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 8)

open Set Complex Real MagicFunction.Parametrisations

namespace MagicFunction.b.RealIntegrals

/--
The first auxiliary contour integral defining the radial profile of `b`.

The prime indicates that this is a function of the real parameter `x = ‖v‖^2`.
-/
@[expose] public def J₁' (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..1, I -- CV factor.
  * ψT' (z₁' t)
  * cexp (π * I * x * (z₁' t))

/--
The second auxiliary contour integral defining the radial profile of `b`.

The prime indicates that this is a function of the real parameter `x = ‖v‖^2`.
-/
@[expose] public def J₂' (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..1,
  ψT' (z₂' t)
  * cexp (π * I * x * (z₂' t))

/--
The third auxiliary contour integral defining the radial profile of `b`.

The prime indicates that this is a function of the real parameter `x = ‖v‖^2`.
-/
@[expose] public def J₃' (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..1, I -- CV factor.
  * ψT' (z₃' t)
  * cexp (π * I * x * (z₃' t))

/--
The fourth auxiliary contour integral defining the radial profile of `b`.

The prime indicates that this is a function of the real parameter `x = ‖v‖^2`.
-/
@[expose] public def J₄' (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..1, -1 -- CV factor.
  * ψT' (z₄' t)
  * cexp (π * I * x * (z₄' t))

/--
The fifth auxiliary contour integral defining the radial profile of `b`.

The prime indicates that this is a function of the real parameter `x = ‖v‖^2`.
-/
@[expose] public def J₅' (x : ℝ) : ℂ := -2 * ∫ t in (0 : ℝ)..1, I -- CV factor.
  * ψI' (z₅' t)
  * cexp (π * I * x * (z₅' t))

/--
The sixth auxiliary contour integral defining the radial profile of `b`.

The prime indicates that this is a function of the real parameter `x = ‖v‖^2`.
-/
@[expose] public def J₆' (x : ℝ) : ℂ := -2 * ∫ t in Ici (1 : ℝ), I -- CV factor.
  * ψS' (z₆' t)
  * cexp (π * I * x * (z₆' t))

/--
The radial profile defining the magic function `b` as a function of `x = ‖v‖^2`.

The prime indicates that this is a function of the real parameter `x = ‖v‖^2`.
-/
@[expose] public def b' (x : ℝ) := J₁' x + J₂' x + J₃' x + J₄' x + J₅' x + J₆' x

end MagicFunction.b.RealIntegrals
open MagicFunction.b.RealIntegrals

namespace MagicFunction.b.RadialFunctions

/-- The function on `V` induced from the radial profile `J₁'` by `x = ‖v‖^2`. -/
@[expose] public def J₁ (x : V) : ℂ := J₁' (‖x‖ ^ 2)

/-- The function on `V` induced from the radial profile `J₂'` by `x = ‖v‖^2`. -/
@[expose] public def J₂ (x : V) : ℂ := J₂' (‖x‖ ^ 2)

/-- The function on `V` induced from the radial profile `J₃'` by `x = ‖v‖^2`. -/
@[expose] public def J₃ (x : V) : ℂ := J₃' (‖x‖ ^ 2)

/-- The function on `V` induced from the radial profile `J₄'` by `x = ‖v‖^2`. -/
@[expose] public def J₄ (x : V) : ℂ := J₄' (‖x‖ ^ 2)

/-- The function on `V` induced from the radial profile `J₅'` by `x = ‖v‖^2`. -/
@[expose] public def J₅ (x : V) : ℂ := J₅' (‖x‖ ^ 2)

/-- The function on `V` induced from the radial profile `J₆'` by `x = ‖v‖^2`. -/
@[expose] public def J₆ (x : V) : ℂ := J₆' (‖x‖ ^ 2)

/-- The magic function `b` on `V`, obtained from the radial profile `b'` by `x = ‖v‖^2`. -/
@[expose] public def b (x : V) : ℂ := b' (‖x‖ ^ 2)

section Eq

/-- Expand `b` as the sum of the six defining integrals. -/
public lemma b_eq (x : V) : b x = J₁ x + J₂ x + J₃ x + J₄ x + J₅ x + J₆ x := rfl

end Eq

end MagicFunction.b.RadialFunctions

end
