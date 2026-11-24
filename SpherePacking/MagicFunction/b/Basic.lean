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

open Set Complex Real MagicFunction.Parametrisations MagicFunction.b.ComplexIntegrands
  MagicFunction.b.RealIntegrands MagicFunction.b.RealIntegrals intervalIntegral

namespace MagicFunction.b.RadialFunctions

section Eq₀

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
