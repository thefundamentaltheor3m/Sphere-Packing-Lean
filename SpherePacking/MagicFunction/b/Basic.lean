/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import SpherePacking.MagicFunction.b.psi
import SpherePacking.MagicFunction.IntegralParametrisations

local notation "V" => EuclideanSpace ℝ (Fin 8)

open Set Complex Real MagicFunction.Parametrisations

namespace MagicFunction.b.RealIntegrals

noncomputable section Real_Input

def J₁' (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..1, I -- Added factor due to variable change!!
  * ψT' (z₁' t)
  * cexp (π * I * x * (z₁' t))

def J₂' (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..1,
  ψT' (z₂' t)
  * cexp (π * I * x * (z₂' t))

def J₃' (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..1, I -- Added factor due to variable change!!
  * ψT' (z₃' t)
  * cexp (π * I * x * (z₃' t))

def J₄' (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..1,
  ψT' (z₄' t)
  * cexp (π * I * x * (z₄' t))

def J₅' (x : ℝ) : ℂ := -2 * ∫ t in (0 : ℝ)..1, I -- Added factor due to variable change!!
  * ψI' (z₅' t)
  * cexp (π * I * x * (z₅' t))

def J₆' (x : ℝ) : ℂ := 2 * ∫ t in Ici (1 : ℝ), I -- Added factor due to variable change!!
  * ψS' (z₆' t)
  * cexp (π * I * x * (z₆' t))

def b' (x : ℝ) := J₁' x + J₂' x + J₃' x + J₄' x + J₅' x + J₆' x

end Real_Input

end MagicFunction.b.RealIntegrals

open MagicFunction.b.RealIntegrals

namespace MagicFunction.b.RadialFunctions

noncomputable section Vector_Input

def J₁ (x : V) : ℂ := J₁' (‖x‖ ^ 2)

def J₂ (x : V) : ℂ := J₂' (‖x‖ ^ 2)

def J₃ (x : V) : ℂ := J₃' (‖x‖ ^ 2)

def J₄ (x : V) : ℂ := J₄' (‖x‖ ^ 2)

def J₅ (x : V) : ℂ := J₅' (‖x‖ ^ 2)

def J₆ (x : V) : ℂ := J₆' (‖x‖ ^ 2)

def b (x : V) : ℂ := b' (‖x‖ ^ 2)

end Vector_Input

open intervalIntegral

section Eq

lemma b_eq (x : V) : b x = J₁ x + J₂ x + J₃ x + J₄ x + J₅ x + J₆ x := rfl

/- # TODO:

Express the Jⱼ in a similar manner to the Iⱼ, with ψS being the analogue of φ₀.
-/

end Eq

end MagicFunction.b.RadialFunctions
