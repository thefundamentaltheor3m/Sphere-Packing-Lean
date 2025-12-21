/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

import SpherePacking.ModularForms.Eisenstein
import SpherePacking.MagicFunction.IntegralParametrisations

local notation "V" => EuclideanSpace ℝ (Fin 8)

open Set Complex Real MagicFunction.Parametrisations
open scoped UpperHalfPlane

noncomputable section Integrands

variable (r : ℝ)

namespace MagicFunction.a.ComplexIntegrands

def Φ₁' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * cexp (π * I * r * (z : ℂ))

def Φ₂' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * cexp (π * I * r * (z : ℂ))

def Φ₃' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 * cexp (π * I * r * (z : ℂ))

def Φ₄' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 * cexp (π * I * r * (z : ℂ))

def Φ₅' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / z) * z ^ 2 * cexp (π * I * r * (z : ℂ))

def Φ₆' : ℂ → ℂ := fun z ↦ φ₀'' (z) * cexp (π * I * r * (z : ℂ))

end MagicFunction.a.ComplexIntegrands

namespace MagicFunction.a.RealIntegrands

open MagicFunction.a.ComplexIntegrands

def Φ₁ : ℝ → ℂ := fun t ↦ I * Φ₁' r (z₁' t)

def Φ₂ : ℝ → ℂ := fun t ↦ Φ₂' r (z₂' t)

def Φ₃ : ℝ → ℂ := fun t ↦ I * Φ₃' r (z₃' t)

def Φ₄ : ℝ → ℂ := fun t ↦ -1 * Φ₄' r (z₄' t)

def Φ₅ : ℝ → ℂ := fun t ↦ I * Φ₅' r (z₅' t)

def Φ₆ : ℝ → ℂ := fun t ↦ I * Φ₆' r (z₆' t)

end MagicFunction.a.RealIntegrands

end Integrands

namespace MagicFunction.a.RealIntegrals

noncomputable section Real_Input

open MagicFunction.a.RealIntegrands

def I₁' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₁ x t

def I₂' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₂ x t

def I₃' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₃ x t

def I₄' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₄ x t

def I₅' : ℝ → ℂ := fun x ↦ -2 * ∫ t in (0 : ℝ)..1, Φ₅ x t

def I₆' : ℝ → ℂ := fun x ↦ 2 * ∫ t in Ici (1 : ℝ), Φ₆ x t

def a' : ℝ → ℂ := fun x ↦ I₁' x + I₂' x + I₃' x + I₄' x + I₅' x + I₆' x

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

open intervalIntegral

section Eq

open MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands

lemma a_eq (x : V) : a x = I₁ x + I₂ x + I₃ x + I₄ x + I₅ x + I₆ x := rfl

lemma I₁_eq (x : V) : I₁ x = I₁' (‖x‖ ^ 2) := rfl

lemma I₂_eq (x : V) : I₂ x = I₂' (‖x‖ ^ 2) := rfl

lemma I₃_eq (x : V) : I₃ x = I₃' (‖x‖ ^ 2) := rfl

lemma I₄_eq (x : V) : I₄ x = I₄' (‖x‖ ^ 2) := rfl

lemma I₅_eq (x : V) : I₅ x = I₅' (‖x‖ ^ 2) := rfl

lemma I₆_eq (x : V) : I₆ x = I₆' (‖x‖ ^ 2) := rfl

lemma I₁'_eq (r : ℝ) : I₁' r = ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * I * r)
    * cexp (-π * r * t) := by
  simp only [I₁', Φ₁, Φ₁']
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  have hmem : t ∈ Icc 0 1 := ⟨ht₀, ht₁⟩
  simp only [z₁'_eq_of_mem hmem]
  calc
  _ = I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (-π * r * (I + t)) := by
      conv_rhs => rw [mul_assoc, mul_assoc]
      conv_lhs => rw [mul_assoc]
      congr 2 <;> ring_nf
      rw [I_sq]
      ring_nf
  _ = I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (-π * I * r) * cexp (-π * r * t) := by
      conv_rhs => rw [mul_assoc]
      rw [← Complex.exp_add]
      congr
      ring_nf
  _ = _ := by
      rw [mul_pow, I_sq]
      ring_nf

lemma I₁'_eq' (r : ℝ) : I₁' r = -I * ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * I * r)
    * cexp (-π * r * t) := by
  rw [I₁'_eq r]
  rw [← smul_eq_mul (-I), ← integral_smul]
  simp only [smul_eq_mul (-I), neg_mul]
  congr
  ext x
  ring

lemma I₁'_eq_Ioc (r : ℝ) : I₁' r = ∫ (t : ℝ) in Ioc 0 1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * I * r)
    * cexp (-π * r * t) := by
  simp [I₁'_eq, intervalIntegral_eq_integral_uIoc]

lemma I₁'_eq'_Ioc (r : ℝ) : I₁' r = -I * ∫ t in (0 : ℝ)..1,
      φ₀'' (-1 / (I * t))
      * t ^ 2
      * cexp (-π * I * r)
      * cexp (-π * r * t) := by
    simp [I₁'_eq', intervalIntegral_eq_integral_uIoc]

lemma I₂'_eq (r : ℝ) : I₂' r = ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (t + I))
    * (t + I) ^ 2
    * cexp (-π * I * r)
    * cexp (π * I * r * t)
    * cexp (-π * r) := by
  simp only [I₂', Φ₂, Φ₂']
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  have hmem : t ∈ Icc 0 1 := ⟨ht₀, ht₁⟩
  simp only [z₂'_eq_of_mem hmem]
  calc
  _ = φ₀'' (-1 / (t + I)) * (t + I) ^ 2 * cexp (π * I * r * (-1 + t + I)) := by
      congr 2 <;> ring_nf
  _ = _ := by
      conv_rhs => rw [mul_assoc, mul_assoc]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr
      ring_nf
      rw [I_sq]
      ring_nf

lemma I₃'_eq (r : ℝ) : I₃' r = ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (π * I * r)
    * cexp (-π * r * t) := by
  simp only [I₃', Φ₃, Φ₃']
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  have hmem : t ∈ Icc 0 1 := ⟨ht₀, ht₁⟩
  simp only [z₃'_eq_of_mem hmem]
  calc
  _ = I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (-π * r * (-I + t)) := by
      conv_rhs => rw [mul_assoc, mul_assoc]
      conv_lhs => rw [mul_assoc]
      congr 2 <;> ring_nf
      rw [I_sq]
      ring_nf
  _ = I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (π * I * r) * cexp (-π * r * t) := by
    conv_rhs => rw [mul_assoc]
    rw [← Complex.exp_add]
    congr
    ring_nf
  _ = _ := by
    rw [mul_pow, I_sq]
    ring_nf

lemma I₃'_eq' (r : ℝ) : I₃' r = -I * ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (π * I * r)
    * cexp (-π * r * t) := by
  rw [I₃'_eq r]
  rw [← smul_eq_mul (-I), ← integral_smul]
  simp only [smul_eq_mul (-I), neg_mul]
  congr
  ext x
  ring

lemma I₃'_eq_Ioc (r : ℝ) : I₃' r = ∫ (t : ℝ) in Ioc 0 1, -I
  * φ₀'' (-1 / (I * t))
  * t ^ 2
  * cexp (π * I * r)
  * cexp (-π * r * t) := by
    simp [I₃'_eq, intervalIntegral_eq_integral_uIoc]

lemma I₃'_eq'_Ioc (r : ℝ) : I₃' r = -I * ∫ (t : ℝ) in Ioc 0 1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (π * I * r)
    * cexp (-π * r * t) := by
  simp [I₃'_eq', intervalIntegral_eq_integral_uIoc]

lemma I₄'_eq (r : ℝ) : I₄' r = ∫ t in (0 : ℝ)..1, -1
    * φ₀'' (-1 / (-t + I))
    * (-t + I) ^ 2
    * cexp (π * I * r)
    * cexp (-π * I * r * t)
    * cexp (-π * r) := by
  simp only [I₄', Φ₄, Φ₄']
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  have hmem : t ∈ Icc 0 1 := ⟨ht₀, ht₁⟩
  simp only [z₄'_eq_of_mem hmem]
  calc
  _ = -1 * φ₀'' (-1 / (-t + I)) * (-t + I) ^ 2 * cexp (π * I * r * (1 - t + I)) := by ring_nf
  _ = _ := by
      conv_rhs => rw [mul_assoc, mul_assoc]
      rw [← Complex.exp_add, ← Complex.exp_add]
      ring_nf
      rw [I_sq]
      ring_nf

lemma I₅'_eq (r : ℝ) : I₅' r = -2 * ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * r * t) := by
  simp only [I₅', Φ₅, Φ₅']; congr 1
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  have hmem : t ∈ Icc 0 1 := ⟨ht₀, ht₁⟩
  simp only [z₅'_eq_of_mem hmem]
  calc
  _ = I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (-π * r * t) := by
      conv_rhs => rw [mul_assoc, mul_assoc]
      conv_lhs => rw [mul_assoc]
      congr 2
      ring_nf
      rw [I_sq]
      ring_nf
  _ = _ := by
    rw [mul_pow, I_sq]
    ring_nf

lemma I₅'_eq' (r : ℝ) : I₅' r = 2 * I * ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * r * t) := by
  rw [I₅'_eq r]
  simp only [neg_mul, integral_neg, mul_neg, neg_neg, mul_assoc, ← smul_eq_mul I]
  rw [← integral_smul]
  congr; ext x
  simp only [smul_eq_mul I]
  ring_nf

lemma I₅'_eq_Ioc (r : ℝ) : I₅' r = -2 * ∫ (t : ℝ) in Ioc 0 1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * r * t) := by
  simp [I₅'_eq, intervalIntegral_eq_integral_uIoc]

lemma I₅'_eq'_Ioc (r : ℝ) : I₅' r = 2 * I * ∫ (t : ℝ) in Ioc 0 1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * r * t) := by
  simp [I₅'_eq', intervalIntegral_eq_integral_uIoc]

lemma I₆'_eq (r : ℝ) : I₆' r = 2 * ∫ t in Ici (1 : ℝ), I
    * φ₀'' (I * t)
    * cexp (-π * r * t) := by
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

lemma I₆'_eq' (r : ℝ) : I₆' r = 2 * I * ∫ t in Ici (1 : ℝ),
  φ₀'' (I * t)
  * cexp (-π * r * t) := by
  rw [I₆'_eq r]
  simp only [mul_assoc, ← smul_eq_mul I]
  rw [← MeasureTheory.integral_smul]
  congr; ext t
  simp only [smul_eq_mul I]
  ring_nf

end Eq

end MagicFunction.a.RadialFunctions
