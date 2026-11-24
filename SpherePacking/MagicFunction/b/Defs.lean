/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.b.Psi

/-!
# The Function `b`: definitions

This file defines Viazovska's function `b` via its integral representations: the complex
integrands `Ψⱼ'`, their restrictions `Ψⱼ` to the contours, the integrals `Jⱼ'` as functions of a
real variable, and the radial functions `Jⱼ` and `b` on `ℝ⁸`.

The bundled Schwartz versions of these functions are defined in
`SpherePacking.MagicFunction.b.Schwartz`, since they depend on proofs of smoothness and decay.
-/

@[expose] public section

local notation "V" => EuclideanSpace ℝ (Fin 8)

open Set Complex Real MagicFunction.Parametrisations
open scoped UpperHalfPlane

noncomputable section Integrands

variable (s : ℝ)

namespace MagicFunction.b.ComplexIntegrands

def Ψ₁' : ℂ → ℂ := fun z ↦ (ψT' z) * cexp (π * I * s * z)

def Ψ₂' : ℂ → ℂ := fun z ↦ (ψT' z) * cexp (π * I * s * z)

def Ψ₃' : ℂ → ℂ := fun z ↦ (ψT' z) * cexp (π * I * s * z)

def Ψ₄' : ℂ → ℂ := fun z ↦ (ψT' z) * cexp (π * I * s * z)

def Ψ₅' : ℂ → ℂ := fun z ↦ (ψI' z) * cexp (π * I * s * z)

def Ψ₆' : ℂ → ℂ := fun z ↦ (ψS' z) * cexp (π * I * s * z)

end MagicFunction.b.ComplexIntegrands

namespace MagicFunction.b.RealIntegrands

open MagicFunction.b.ComplexIntegrands

def Ψ₁ : ℝ → ℂ := fun t ↦ I * Ψ₁' s (z₁' t)

def Ψ₂ : ℝ → ℂ := fun t ↦ Ψ₂' s (z₂' t)

def Ψ₃ : ℝ → ℂ := fun t ↦ I * Ψ₃' s (z₃' t)

def Ψ₄ : ℝ → ℂ := fun t ↦ -1 * Ψ₄' s (z₄' t)

def Ψ₅ : ℝ → ℂ := fun t ↦ I * Ψ₅' s (z₅' t)

def Ψ₆ : ℝ → ℂ := fun t ↦ I * Ψ₆' s (z₆' t)

end MagicFunction.b.RealIntegrands

end Integrands

namespace MagicFunction.b.RealIntegrals

noncomputable section Real_Input

open MagicFunction.b.RealIntegrands

def J₁' : ℝ → ℂ := fun s ↦ ∫ t in (0 : ℝ)..1, Ψ₁ s t

def J₂' : ℝ → ℂ := fun s ↦ ∫ t in (0 : ℝ)..1, Ψ₂ s t

def J₃' : ℝ → ℂ := fun s ↦ ∫ t in (0 : ℝ)..1, Ψ₃ s t

def J₄' : ℝ → ℂ := fun s ↦ ∫ t in (0 : ℝ)..1, Ψ₄ s t

def J₅' : ℝ → ℂ := fun s ↦ -2 * ∫ t in (0 : ℝ)..1, Ψ₅ s t

def J₆' : ℝ → ℂ := fun s ↦ -2 * ∫ t in Ici (1 : ℝ), Ψ₆ s t

def b' : ℝ → ℂ := fun s ↦ J₁' s + J₂' s + J₃' s + J₄' s + J₅' s + J₆' s

end Real_Input

end MagicFunction.b.RealIntegrals

open MagicFunction.b.RealIntegrals

namespace MagicFunction.b.RadialFunctions

noncomputable section Vector_Input

def J₁ : V → ℂ := fun x ↦ J₁' (‖x‖ ^ 2)

def J₂ : V → ℂ := fun x ↦ J₂' (‖x‖ ^ 2)

def J₃ : V → ℂ := fun x ↦ J₃' (‖x‖ ^ 2)

def J₄ : V → ℂ := fun x ↦ J₄' (‖x‖ ^ 2)

def J₅ : V → ℂ := fun x ↦ J₅' (‖x‖ ^ 2)

def J₆ : V → ℂ := fun x ↦ J₆' (‖x‖ ^ 2)

def b : V → ℂ := fun x ↦ b' (‖x‖ ^ 2)

end Vector_Input

end MagicFunction.b.RadialFunctions
