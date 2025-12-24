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

namespace MagicFunction.a.RealIntegrals

noncomputable section Real_Input

def I₁' (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..1, I -- Added factor due to variable change!!
  * φ₀'' (-1 / ((z₁' t) + (1 : ℂ)))
  * ((z₁' t) + (1 : ℂ)) ^ 2
  * cexp (π * I * x * (z₁' t))

def I₂' (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..1,
  φ₀'' (-1 / ((z₂' t) + (1 : ℂ)))
  * ((z₂' t) + (1 : ℂ)) ^ 2
  * cexp (π * I * x * (z₂' t))

def I₃' (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..1, I -- Added factor due to variable change!!
  * φ₀'' (-1 / ((z₃' t) - (1 : ℂ)))
  * ((z₃' t) - (1 : ℂ)) ^ 2
  * cexp (π * I * x * (z₃' t))

def I₄' (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..1, -1 -- Added factor due to variable change!!
  * φ₀'' (-1 / ((z₄' t) - (1 : ℂ)))
  * ((z₄' t) - (1 : ℂ)) ^ 2
  * cexp (π * I * x * (z₄' t))

def I₅' (x : ℝ) : ℂ := -2 * ∫ t in (0 : ℝ)..1, I -- Added factor due to variable change!!
  * φ₀'' (-1 / (z₅' t))
  * (z₅' t) ^ 2
  * cexp (π * I * x * (z₅' t))

def I₆' (x : ℝ) : ℂ := 2 * ∫ t in Ici (1 : ℝ), I -- Added factor due to variable change!!
  * φ₀'' (z₆' t)
  * cexp (π * I * x * (z₆' t))

def a' (x : ℝ) := I₁' x + I₂' x + I₃' x + I₄' x + I₅' x + I₆' x

end Real_Input

end MagicFunction.a.RealIntegrals

open MagicFunction.a.RealIntegrals

namespace MagicFunction.a.RadialFunctions

noncomputable section Vector_Input

def I₁ (x : V) : ℂ := I₁' (‖x‖ ^ 2)

def I₂ (x : V) : ℂ := I₂' (‖x‖ ^ 2)

def I₃ (x : V) : ℂ := I₃' (‖x‖ ^ 2)

def I₄ (x : V) : ℂ := I₄' (‖x‖ ^ 2)

def I₅ (x : V) : ℂ := I₅' (‖x‖ ^ 2)

def I₆ (x : V) : ℂ := I₆' (‖x‖ ^ 2)

def a (x : V) : ℂ := a' (‖x‖ ^ 2)

end Vector_Input

open intervalIntegral

section Eq

lemma a_eq (x : V) : a x = I₁ x + I₂ x + I₃ x + I₄ x + I₅ x + I₆ x := rfl

lemma I₁'_eq (r : ℝ) : I₁' r = ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * I * r)
    * cexp (-π * r * t) := by
  rw [I₁']
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  have hmem : t ∈ Icc 0 1 := ⟨ht₀, ht₁⟩
  simp only [z₁'_eq_of_mem hmem]
  calc
  _ = I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (-π * r * (I + t)) := by
      congr 2 <;> ring_nf
      rw [I_sq]
      ring
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
  * cexp (-π * r * t) := by simp [I₁'_eq, intervalIntegral_eq_integral_uIoc]

lemma I₁'_eq'_Ioc (r : ℝ) : I₁' r = -I * ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * I * r)
    * cexp (-π * r * t) := by simp [I₁'_eq', intervalIntegral_eq_integral_uIoc]

lemma I₂'_eq (r : ℝ) : I₂' r = ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (t + I))
    * (t + I) ^ 2
    * cexp (-π * I * r)
    * cexp (π * I * r * t)
    * cexp (-π * r) := by
  rw [I₂']
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
  rw [I₃']
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  have hmem : t ∈ Icc 0 1 := ⟨ht₀, ht₁⟩
  simp only [z₃'_eq_of_mem hmem]
  calc
  _ = I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (-π * r * (-I + t)) := by
    congr 2 <;> ring_nf
    rw [I_sq]
    ring
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
  rw [I₄']
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
  rw [I₅']; congr 1
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  have hmem : t ∈ Icc 0 1 := ⟨ht₀, ht₁⟩
  simp only [z₅'_eq_of_mem hmem]
  calc
  _ = I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (-π * r * t) := by
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
  rw [I₆']; congr 1
  apply MeasureTheory.setIntegral_congr_fun (X := ℝ) (E := ℂ) (measurableSet_Ici)
  simp only [EqOn, neg_mul]
  intro t ht
  rw [z₆'_eq_of_mem ht]
  congr
  ring_nf
  simp

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
