/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.a.Defs

/-!
# The Function `a`: explicit integral formulas

This file rewrites the integrals `Iⱼ'` defining Viazovska's function `a` (see
`SpherePacking.MagicFunction.a.Defs`) as explicit integrals in the real variable `t`.
-/

@[expose] public section

local notation "V" => EuclideanSpace ℝ (Fin 8)

open Set Complex Real MagicFunction.Parametrisations MagicFunction.a.RealIntegrals intervalIntegral

namespace MagicFunction.a.ComplexIntegrands

variable (s : ℝ)

-- We write some API that allows us to express the `(Φᵢ' s)` as functions when needed.

lemma Φ₁'_def : Φ₁' s = fun z ↦ φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * cexp (π * I * s * (z : ℂ)) :=
  rfl

lemma Φ₂'_def : Φ₂' s = fun z ↦ φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * cexp (π * I * s * (z : ℂ)) :=
  rfl

lemma Φ₃'_def : Φ₃' s = fun z ↦ φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 * cexp (π * I * s * (z : ℂ)) :=
  rfl

lemma Φ₄'_def : Φ₄' s = fun z ↦ φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 * cexp (π * I * s * (z : ℂ)) :=
  rfl

lemma Φ₅'_def : Φ₅' s = fun z ↦ φ₀'' (-1 / z) * z ^ 2 * cexp (π * I * s * (z : ℂ)) :=
  rfl

lemma Φ₆'_def : Φ₆' s = fun z ↦ φ₀'' (z) * cexp (π * I * s * (z : ℂ)) :=
  rfl

end MagicFunction.a.ComplexIntegrands

namespace MagicFunction.a.RealIntegrands

open MagicFunction.a.ComplexIntegrands

variable (s : ℝ)

-- We write some API that allows us to express the `(Φᵢ s)` as functions when needed.

lemma Φ₁_def : Φ₁ s = fun t ↦ I * Φ₁' s (z₁' t) :=
  rfl

lemma Φ₂_def : Φ₂ s = fun t ↦ Φ₂' s (z₂' t) :=
  rfl

lemma Φ₃_def : Φ₃ s = fun t ↦ I * Φ₃' s (z₃' t) :=
  rfl

lemma Φ₄_def : Φ₄ s = fun t ↦ -1 * Φ₄' s (z₄' t) :=
  rfl

lemma Φ₅_def : Φ₅ s = fun t ↦ I * Φ₅' s (z₅' t) :=
  rfl

lemma Φ₆_def : Φ₆ s = fun t ↦ I * Φ₆' s (z₆' t) :=
  rfl

end MagicFunction.a.RealIntegrands

namespace MagicFunction.a.RadialFunctions

section Eq

open MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands

lemma a_eq (x : V) : a x = I₁ x + I₂ x + I₃ x + I₄ x + I₅ x + I₆ x := rfl

lemma I₁_eq (x : V) : I₁ x = I₁' (‖x‖ ^ 2) := rfl

lemma I₂_eq (x : V) : I₂ x = I₂' (‖x‖ ^ 2) := rfl

lemma I₃_eq (x : V) : I₃ x = I₃' (‖x‖ ^ 2) := rfl

lemma I₄_eq (x : V) : I₄ x = I₄' (‖x‖ ^ 2) := rfl

lemma I₅_eq (x : V) : I₅ x = I₅' (‖x‖ ^ 2) := rfl

lemma I₆_eq (x : V) : I₆ x = I₆' (‖x‖ ^ 2) := rfl

lemma I₁'_eq (s : ℝ) : I₁' s = ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * I * s)
    * cexp (-π * s * t) := by
  simp only [I₁', Φ₁, Φ₁']
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  have hmem : t ∈ Icc 0 1 := ⟨ht₀, ht₁⟩
  simp only [z₁'_eq_of_mem hmem]
  calc
  _ = I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (-π * s * (I + t)) := by
      conv_rhs => rw [mul_assoc, mul_assoc]
      conv_lhs => rw [mul_assoc]
      congr 2 <;> ring_nf
      rw [I_sq]
      ring_nf
  _ = I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (-π * I * s) * cexp (-π * s * t) := by
      conv_rhs => rw [mul_assoc]
      rw [← Complex.exp_add]
      congr
      ring_nf
  _ = _ := by
      rw [mul_pow, I_sq]
      ring_nf

lemma I₁'_eq' (s : ℝ) : I₁' s = -I * ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * I * s)
    * cexp (-π * s * t) := by
  rw [I₁'_eq s]
  rw [← smul_eq_mul (-I), ← integral_smul]
  simp only [smul_eq_mul (-I), neg_mul]
  congr
  ext x
  ring

lemma I₁'_eq_Ioc (s : ℝ) : I₁' s = ∫ (t : ℝ) in Ioc 0 1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * I * s)
    * cexp (-π * s * t) := by
  rw [I₁'_eq, integral_of_le zero_le_one]

lemma I₁'_eq'_Ioc (s : ℝ) : I₁' s = -I * ∫ t in (0 : ℝ)..1,
      φ₀'' (-1 / (I * t))
      * t ^ 2
      * cexp (-π * I * s)
      * cexp (-π * s * t) := by
    simp [I₁'_eq', intervalIntegral_eq_integral_uIoc]

lemma I₂'_eq (s : ℝ) : I₂' s = ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (t + I))
    * (t + I) ^ 2
    * cexp (-π * I * s)
    * cexp (π * I * s * t)
    * cexp (-π * s) := by
  simp only [I₂', Φ₂, Φ₂']
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  have hmem : t ∈ Icc 0 1 := ⟨ht₀, ht₁⟩
  simp only [z₂'_eq_of_mem hmem]
  calc
  _ = φ₀'' (-1 / (t + I)) * (t + I) ^ 2 * cexp (π * I * s * (-1 + t + I)) := by
      congr 2 <;> ring_nf
  _ = _ := by
      conv_rhs => rw [mul_assoc, mul_assoc]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr
      ring_nf
      rw [I_sq]
      ring_nf

lemma I₃'_eq (s : ℝ) : I₃' s = ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (π * I * s)
    * cexp (-π * s * t) := by
  simp only [I₃', Φ₃, Φ₃']
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  have hmem : t ∈ Icc 0 1 := ⟨ht₀, ht₁⟩
  simp only [z₃'_eq_of_mem hmem]
  calc
  _ = I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (-π * s * (-I + t)) := by
      conv_rhs => rw [mul_assoc, mul_assoc]
      conv_lhs => rw [mul_assoc]
      congr 2 <;> ring_nf
      rw [I_sq]
      ring_nf
  _ = I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (π * I * s) * cexp (-π * s * t) := by
    conv_rhs => rw [mul_assoc]
    rw [← Complex.exp_add]
    congr
    ring_nf
  _ = _ := by
    rw [mul_pow, I_sq]
    ring_nf

lemma I₃'_eq' (s : ℝ) : I₃' s = -I * ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (π * I * s)
    * cexp (-π * s * t) := by
  rw [I₃'_eq s]
  rw [← smul_eq_mul (-I), ← integral_smul]
  simp only [smul_eq_mul (-I), neg_mul]
  congr
  ext x
  ring

lemma I₃'_eq_Ioc (s : ℝ) : I₃' s = ∫ (t : ℝ) in Ioc 0 1, -I
  * φ₀'' (-1 / (I * t))
  * t ^ 2
  * cexp (π * I * s)
  * cexp (-π * s * t) := by
    rw [I₃'_eq, integral_of_le zero_le_one]

lemma I₃'_eq'_Ioc (s : ℝ) : I₃' s = -I * ∫ (t : ℝ) in Ioc 0 1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (π * I * s)
    * cexp (-π * s * t) := by
  rw [I₃'_eq', integral_of_le zero_le_one]

lemma I₄'_eq (s : ℝ) : I₄' s = ∫ t in (0 : ℝ)..1, -1
    * φ₀'' (-1 / (-t + I))
    * (-t + I) ^ 2
    * cexp (π * I * s)
    * cexp (-π * I * s * t)
    * cexp (-π * s) := by
  simp only [I₄', Φ₄, Φ₄']
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  have hmem : t ∈ Icc 0 1 := ⟨ht₀, ht₁⟩
  simp only [z₄'_eq_of_mem hmem]
  calc
  _ = -1 * φ₀'' (-1 / (-t + I)) * (-t + I) ^ 2 * cexp (π * I * s * (1 - t + I)) := by ring_nf
  _ = _ := by
      conv_rhs => rw [mul_assoc, mul_assoc]
      rw [← Complex.exp_add, ← Complex.exp_add]
      ring_nf
      rw [I_sq]
      ring_nf

lemma I₅'_eq (s : ℝ) : I₅' s = -2 * ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * s * t) := by
  simp only [I₅', Φ₅, Φ₅']; congr 1
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  have hmem : t ∈ Icc 0 1 := ⟨ht₀, ht₁⟩
  simp only [z₅'_eq_of_mem hmem]
  calc
  _ = I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (-π * s * t) := by
      conv_rhs => rw [mul_assoc, mul_assoc]
      conv_lhs => rw [mul_assoc]
      congr 2
      ring_nf
      rw [I_sq]
      ring_nf
  _ = _ := by
    rw [mul_pow, I_sq]
    ring_nf

lemma I₅'_eq' (s : ℝ) : I₅' s = 2 * I * ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * s * t) := by
  rw [I₅'_eq s]
  simp only [neg_mul, integral_neg, mul_neg, neg_neg, mul_assoc, ← smul_eq_mul I]
  rw [← integral_smul]
  congr; ext x
  simp only [smul_eq_mul I]
  ring_nf

lemma I₅'_eq_Ioc (s : ℝ) : I₅' s = -2 * ∫ (t : ℝ) in Ioc 0 1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * s * t) := by
  rw [I₅'_eq, integral_of_le zero_le_one]

lemma I₅'_eq'_Ioc (s : ℝ) : I₅' s = 2 * I * ∫ (t : ℝ) in Ioc 0 1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * s * t) := by
  rw [I₅'_eq', integral_of_le zero_le_one]

lemma I₆'_eq (s : ℝ) : I₆' s = 2 * ∫ t in Ici (1 : ℝ), I
    * φ₀'' (I * t)
    * cexp (-π * s * t) := by
  simp only [I₆', Φ₆, Φ₆']
  congr 1
  apply MeasureTheory.setIntegral_congr_fun (X := ℝ) (E := ℂ) (measurableSet_Ici)
  simp only [EqOn, neg_mul]
  intro t ht
  rw [z₆'_eq_of_mem ht]
  conv_rhs => rw [mul_assoc]
  congr
  ring_nf
  rw [I_sq]
  ring_nf

lemma I₆'_eq' (s : ℝ) : I₆' s = 2 * I * ∫ t in Ici (1 : ℝ),
  φ₀'' (I * t)
  * cexp (-π * s * t) := by
  rw [I₆'_eq s]
  simp only [mul_assoc, ← smul_eq_mul I]
  rw [← MeasureTheory.integral_smul]
  congr; ext t
  simp only [smul_eq_mul I]
  ring_nf

end Eq

end MagicFunction.a.RadialFunctions
