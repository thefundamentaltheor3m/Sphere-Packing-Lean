/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.IntegralParametrisations
public import SpherePacking.MagicFunction.a.Phi

/-!
# The Function `a`: definitions

This file defines Viazovska's function `a` via its integral representations: the complex
integrands `Φⱼ'`, their restrictions `Φⱼ` to the contours, the integrals `Iⱼ'` as functions of a
real variable, and the radial functions `Iⱼ` and `a` on `ℝ⁸`.

The bundled Schwartz versions of these functions are defined in
`SpherePacking.MagicFunction.a.Schwartz`, since they depend on proofs of smoothness and decay.
-/

@[expose] public section

local notation "V" => EuclideanSpace ℝ (Fin 8)

open Set Complex Real MagicFunction.Parametrisations
open scoped UpperHalfPlane

noncomputable section Integrands

variable (s : ℝ)

namespace MagicFunction.a.ComplexIntegrands

def Φ₁' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * cexp (π * I * s * (z : ℂ))

def Φ₂' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * cexp (π * I * s * (z : ℂ))

def Φ₃' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 * cexp (π * I * s * (z : ℂ))

def Φ₄' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 * cexp (π * I * s * (z : ℂ))

def Φ₅' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / z) * z ^ 2 * cexp (π * I * s * (z : ℂ))

def Φ₆' : ℂ → ℂ := fun z ↦ φ₀'' (z) * cexp (π * I * s * (z : ℂ))

end MagicFunction.a.ComplexIntegrands

namespace MagicFunction.a.RealIntegrands

open MagicFunction.a.ComplexIntegrands

def Φ₁ : ℝ → ℂ := fun t ↦ I * Φ₁' s (z₁' t)

def Φ₂ : ℝ → ℂ := fun t ↦ Φ₂' s (z₂' t)

def Φ₃ : ℝ → ℂ := fun t ↦ I * Φ₃' s (z₃' t)

def Φ₄ : ℝ → ℂ := fun t ↦ -1 * Φ₄' s (z₄' t)

def Φ₅ : ℝ → ℂ := fun t ↦ I * Φ₅' s (z₅' t)

def Φ₆ : ℝ → ℂ := fun t ↦ I * Φ₆' s (z₆' t)

end MagicFunction.a.RealIntegrands

end Integrands

namespace MagicFunction.a.RealIntegrals

noncomputable section Real_Input

open MagicFunction.a.RealIntegrands

def I₁' : ℝ → ℂ := fun s ↦ ∫ t in (0 : ℝ)..1, Φ₁ s t

def I₂' : ℝ → ℂ := fun s ↦ ∫ t in (0 : ℝ)..1, Φ₂ s t

def I₃' : ℝ → ℂ := fun s ↦ ∫ t in (0 : ℝ)..1, Φ₃ s t

def I₄' : ℝ → ℂ := fun s ↦ ∫ t in (0 : ℝ)..1, Φ₄ s t

def I₅' : ℝ → ℂ := fun s ↦ -2 * ∫ t in (0 : ℝ)..1, Φ₅ s t

def I₆' : ℝ → ℂ := fun s ↦ 2 * ∫ t in Ici (1 : ℝ), Φ₆ s t

def a' : ℝ → ℂ := fun s ↦ I₁' s + I₂' s + I₃' s + I₄' s + I₅' s + I₆' s

end Real_Input

end MagicFunction.a.RealIntegrals

open MagicFunction.a.RealIntegrals

namespace MagicFunction.a.RadialFunctions

noncomputable section Vector_Input

def I₁ : V → ℂ := fun x ↦ I₁' (‖x‖ ^ 2)

def I₂ : V → ℂ := fun x ↦ I₂' (‖x‖ ^ 2)

def I₃ : V → ℂ := fun x ↦ I₃' (‖x‖ ^ 2)

def I₄ : V → ℂ := fun x ↦ I₄' (‖x‖ ^ 2)

def I₅ : V → ℂ := fun x ↦ I₅' (‖x‖ ^ 2)

def I₆ : V → ℂ := fun x ↦ I₆' (‖x‖ ^ 2)

def a : V → ℂ := fun x ↦ a' (‖x‖ ^ 2)

end Vector_Input

end MagicFunction.a.RadialFunctions
