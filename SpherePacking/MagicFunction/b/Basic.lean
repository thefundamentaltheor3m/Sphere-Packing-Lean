/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import SpherePacking.MagicFunction.b.psi
import SpherePacking.MagicFunction.IntegralParametrisations

local notation "V" => EuclideanSpace ℝ (Fin 8)

open Set Complex Real MagicFunction.Parametrisations
open scoped UpperHalfPlane

noncomputable section Integrands

variable (r : ℝ)

namespace MagicFunction.b.ComplexIntegrands

def Ψ₁' : ℂ → ℂ := fun z ↦ (ψT' z) * cexp (π * I * r * z)

def Ψ₂' : ℂ → ℂ := fun z ↦ (ψT' z) * cexp (π * I * r * z)

def Ψ₃' : ℂ → ℂ := fun z ↦ (ψT' z) * cexp (π * I * r * z)

def Ψ₄' : ℂ → ℂ := fun z ↦ (ψT' z) * cexp (π * I * r * z)

def Ψ₅' : ℂ → ℂ := fun z ↦ (ψI' z) * cexp (π * I * r * z)

def Ψ₆' : ℂ → ℂ := fun z ↦ (ψS' z) * cexp (π * I * r * z)

section Def

-- We write some API that allows us to express the `(Ψᵢ' r)` as functions when needed.

lemma Ψ₁'_def : Ψ₁' r = fun z ↦ (ψT' z) * cexp (π * I * r * z) :=
  rfl

lemma Ψ₂'_def : Ψ₂' r = fun z ↦ (ψT' z) * cexp (π * I * r * z) :=
  rfl

lemma Ψ₃'_def : Ψ₃' r = fun z ↦ (ψT' z) * cexp (π * I * r * z) :=
  rfl

lemma Ψ₄'_def : Ψ₄' r = fun z ↦ (ψT' z) * cexp (π * I * r * z) :=
  rfl

lemma Ψ₅'_def : Ψ₅' r = fun z ↦ (ψI' z) * cexp (π * I * r * z) :=
  rfl

lemma Ψ₆'_def : Ψ₆' r = fun z ↦ (ψS' z) * cexp (π * I * r * z) :=
  rfl

end Def

end MagicFunction.b.ComplexIntegrands

namespace MagicFunction.b.RealIntegrands

open MagicFunction.b.ComplexIntegrands

def Ψ₁ : ℝ → ℂ := fun t ↦ I * Ψ₁' r (z₁' t)

def Ψ₂ : ℝ → ℂ := fun t ↦ Ψ₂' r (z₂' t)

def Ψ₃ : ℝ → ℂ := fun t ↦ I * Ψ₃' r (z₃' t)

def Ψ₄ : ℝ → ℂ := fun t ↦ -1 * Ψ₄' r (z₄' t)

def Ψ₅ : ℝ → ℂ := fun t ↦ I * Ψ₅' r (z₅' t)

def Ψ₆ : ℝ → ℂ := fun t ↦ I * Ψ₆' r (z₆' t)

section Def

-- We write some API that allows us to express the `(Ψᵢ r)` as functions when needed.

lemma Ψ₁_def : Ψ₁ r = fun t ↦ I * Ψ₁' r (z₁' t) :=
  rfl

lemma Ψ₂_def : Ψ₂ r = fun t ↦ Ψ₂' r (z₂' t) :=
  rfl

lemma Ψ₃_def : Ψ₃ r = fun t ↦ I * Ψ₃' r (z₃' t) :=
  rfl

lemma Ψ₄_def : Ψ₄ r = fun t ↦ -1 * Ψ₄' r (z₄' t) :=
  rfl

lemma Ψ₅_def : Ψ₅ r = fun t ↦ I * Ψ₅' r (z₅' t) :=
  rfl

lemma Ψ₆_def : Ψ₆ r = fun t ↦ I * Ψ₆' r (z₆' t) :=
  rfl

end Def

end MagicFunction.b.RealIntegrands

end Integrands

namespace MagicFunction.b.RealIntegrals

noncomputable section Real_Input

open MagicFunction.b.RealIntegrands

def J₁' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Ψ₁ x t

def J₂' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Ψ₂ x t

def J₃' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Ψ₃ x t

def J₄' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Ψ₄ x t

def J₅' : ℝ → ℂ := fun x ↦ -2 * ∫ t in (0 : ℝ)..1, Ψ₅ x t

def J₆' : ℝ → ℂ := fun x ↦ 2 * ∫ t in Ici (1 : ℝ), Ψ₆ x t

def b' : ℝ → ℂ := fun x ↦ J₁' x + J₂' x + J₃' x + J₄' x + J₅' x + J₆' x

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

open intervalIntegral MagicFunction.b.ComplexIntegrands MagicFunction.b.RealIntegrands
  MagicFunction.b.RealIntegrals

section Eq₀

lemma b_eq (x : V) : b x = J₁ x + J₂ x + J₃ x + J₄ x + J₅ x + J₆ x := rfl

/- # TODO:

Express the Jⱼ in a similar manner to the Iⱼ, with ψS being the analogue of φ₀.
-/

private lemma aux_I :  I ≠ 0 := by norm_num

lemma J₁'_eq₀ (r : ℝ) : J₁' r = ∫ t in (0 : ℝ)..1,
    I * ψS' (-1 / ((z₁' t) + (1 : ℂ))) * ((z₁' t) + (1 : ℂ)) ^ 2 * cexp (π * I * r * (z₁' t)) := by
  rw [J₁', Ψ₁_def r, Ψ₁'_def r]
  apply integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t ht
  rw [uIoc_of_le zero_le_one] at ht
  simp only [ψS_slash_ST_explicit₁ ht]
  ac_rfl

lemma J₂'_eq₀ (r : ℝ) : J₂' r = ∫ t in (0 : ℝ)..1,
    ψS' (-1 / ((z₂' t) + (1 : ℂ))) * ((z₂' t) + (1 : ℂ)) ^ 2 * cexp (π * I * r * (z₂' t)) := by
  rw [J₂', Ψ₂_def r, Ψ₂'_def r]
  apply integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  simp only [ψS_slash_ST_explicit₂ ht]

lemma J₃'_eq₀ (r : ℝ) : J₃' r = ∫ t in (0 : ℝ)..1,
    I * ψS' (-1 / ((z₃' t) + (1 : ℂ))) * ((z₃' t) + (1 : ℂ)) ^ 2 * cexp (π * I * r * (z₃' t)) := by
  rw [J₃', Ψ₃_def r, Ψ₃'_def r]
  apply integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t ht
  rw [uIoc_of_le zero_le_one] at ht
  simp only [ψS_slash_ST_explicit₃ ht]
  ac_rfl

lemma J₄'_eq₀ (r : ℝ) : J₄' r = ∫ t in (0 : ℝ)..1,
    -1 * ψS' (-1 / ((z₄' t) + (1 : ℂ))) * ((z₄' t) + (1 : ℂ)) ^ 2 * cexp (π * I * r * (z₄' t)) := by
  rw [J₄', Ψ₄_def r, Ψ₄'_def r]
  apply integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  simp only [ψS_slash_ST_explicit₄ ht]
  ac_rfl

lemma J₅'_eq₀ (r : ℝ) : J₅' r = -2 * ∫ t in (0 : ℝ)..1,
    I * ψS' (-1 / (z₅' t)) * (z₅' t) ^ 2 * cexp (π * I * r * (z₅' t)) := by
  rw [J₅', Ψ₅_def r, Ψ₅'_def r]
  congr 1
  apply integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t ht
  rw [uIoc_of_le zero_le_one] at ht
  simp only [ψS_slash_S_explicit₅ ht]
  ac_rfl

lemma J₆'_eq₀ (r : ℝ) : J₆' r = 2 * ∫ t in Ici (1 : ℝ),
    I * ψS' (z₆' t) * cexp (π * I * r * (z₆' t)) := by
  rw [J₆', Ψ₆_def r, Ψ₆'_def r]
  ring_nf

end Eq₀

end MagicFunction.b.RadialFunctions
