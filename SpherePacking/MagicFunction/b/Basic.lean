/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.b.Defs

/-!
# The Function `b`: explicit integral formulas

This file rewrites the integrals `Jⱼ'` defining Viazovska's function `b` (see
`SpherePacking.MagicFunction.b.Defs`) in terms of `ψS`.
-/

@[expose] public section

local notation "V" => EuclideanSpace ℝ (Fin 8)

open Set Complex Real MagicFunction.Parametrisations MagicFunction.b.ComplexIntegrands
  MagicFunction.b.RealIntegrands MagicFunction.b.RealIntegrals intervalIntegral

namespace MagicFunction.b.ComplexIntegrands

variable (s : ℝ)

-- We write some API that allows us to express the `(Ψᵢ' s)` as functions when needed.

lemma Ψ₁'_def : Ψ₁' s = fun z ↦ (ψT' z) * cexp (π * I * s * z) :=
  rfl

lemma Ψ₂'_def : Ψ₂' s = fun z ↦ (ψT' z) * cexp (π * I * s * z) :=
  rfl

lemma Ψ₃'_def : Ψ₃' s = fun z ↦ (ψT' z) * cexp (π * I * s * z) :=
  rfl

lemma Ψ₄'_def : Ψ₄' s = fun z ↦ (ψT' z) * cexp (π * I * s * z) :=
  rfl

lemma Ψ₅'_def : Ψ₅' s = fun z ↦ (ψI' z) * cexp (π * I * s * z) :=
  rfl

lemma Ψ₆'_def : Ψ₆' s = fun z ↦ (ψS' z) * cexp (π * I * s * z) :=
  rfl

end MagicFunction.b.ComplexIntegrands

namespace MagicFunction.b.RealIntegrands

open MagicFunction.b.ComplexIntegrands

variable (s : ℝ)

-- We write some API that allows us to express the `(Ψᵢ s)` as functions when needed.

lemma Ψ₁_def : Ψ₁ s = fun t ↦ I * Ψ₁' s (z₁' t) :=
  rfl

lemma Ψ₂_def : Ψ₂ s = fun t ↦ Ψ₂' s (z₂' t) :=
  rfl

lemma Ψ₃_def : Ψ₃ s = fun t ↦ I * Ψ₃' s (z₃' t) :=
  rfl

lemma Ψ₄_def : Ψ₄ s = fun t ↦ -1 * Ψ₄' s (z₄' t) :=
  rfl

lemma Ψ₅_def : Ψ₅ s = fun t ↦ I * Ψ₅' s (z₅' t) :=
  rfl

lemma Ψ₆_def : Ψ₆ s = fun t ↦ I * Ψ₆' s (z₆' t) :=
  rfl

end MagicFunction.b.RealIntegrands

namespace MagicFunction.b.RadialFunctions

lemma b_eq (x : V) : b x = J₁ x + J₂ x + J₃ x + J₄ x + J₅ x + J₆ x := rfl

section Eq₀

/- # TODO:

Express the Jⱼ in a similar manner to the Iⱼ, with ψS being the analogue of φ₀.
-/

private lemma aux_I :  I ≠ 0 := by norm_num

lemma J₁'_eq₀ (s : ℝ) : J₁' s = ∫ t in (0 : ℝ)..1,
    I * ψS' (-1 / ((z₁' t) + (1 : ℂ))) * ((z₁' t) + (1 : ℂ)) ^ 2 * cexp (π * I * s * (z₁' t)) := by
  rw [J₁', Ψ₁_def s, Ψ₁'_def s]
  apply integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t ht
  rw [uIoc_of_le zero_le_one] at ht
  simp only [ψS_slash_ST_explicit₁ ht]
  ac_rfl

lemma J₂'_eq₀ (s : ℝ) : J₂' s = ∫ t in (0 : ℝ)..1,
    ψS' (-1 / ((z₂' t) + (1 : ℂ))) * ((z₂' t) + (1 : ℂ)) ^ 2 * cexp (π * I * s * (z₂' t)) := by
  rw [J₂', Ψ₂_def s, Ψ₂'_def s]
  apply integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  simp only [ψS_slash_ST_explicit₂ ht]

lemma J₃'_eq₀ (s : ℝ) : J₃' s = ∫ t in (0 : ℝ)..1,
    I * ψS' (-1 / ((z₃' t) + (1 : ℂ))) * ((z₃' t) + (1 : ℂ)) ^ 2 * cexp (π * I * s * (z₃' t)) := by
  rw [J₃', Ψ₃_def s, Ψ₃'_def s]
  apply integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t ht
  rw [uIoc_of_le zero_le_one] at ht
  simp only [ψS_slash_ST_explicit₃ ht]
  ac_rfl

lemma J₄'_eq₀ (s : ℝ) : J₄' s = ∫ t in (0 : ℝ)..1,
    -1 * ψS' (-1 / ((z₄' t) + (1 : ℂ))) * ((z₄' t) + (1 : ℂ)) ^ 2 * cexp (π * I * s * (z₄' t)) := by
  rw [J₄', Ψ₄_def s, Ψ₄'_def s]
  apply integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  simp only [ψS_slash_ST_explicit₄ ht]
  ac_rfl

lemma J₅'_eq₀ (s : ℝ) : J₅' s = -2 * ∫ t in (0 : ℝ)..1,
    I * ψS' (-1 / (z₅' t)) * (z₅' t) ^ 2 * cexp (π * I * s * (z₅' t)) := by
  rw [J₅', Ψ₅_def s, Ψ₅'_def s]
  congr 1
  apply integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t ht
  rw [uIoc_of_le zero_le_one] at ht
  simp only [ψS_slash_S_explicit₅ ht]
  ac_rfl

lemma J₆'_eq₀ (s : ℝ) : J₆' s = -2 * ∫ t in Ici (1 : ℝ),
    I * ψS' (z₆' t) * cexp (π * I * s * (z₆' t)) := by
  rw [J₆', Ψ₆_def s, Ψ₆'_def s]
  ring_nf

end Eq₀

end MagicFunction.b.RadialFunctions
