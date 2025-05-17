/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

import SpherePacking.ModularForms.Eisenstein
import Mathlib

local notation "V" => EuclideanSpace ℝ (Fin 8)

open Set Complex Real

namespace MagicFunction.a.Parametrisations

noncomputable section Parametrisations

def z₁ (t : Icc (0 : ℝ) 1) : ℂ := -1 + I * t

def z₁' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₁ t -- `by norm_num` also works

def z₂ (t : Icc (0 : ℝ) 1) : ℂ := -1 + t + I

def z₂' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₂ t -- `by norm_num` also works

def z₃ (t : Icc (0 : ℝ) 1) : ℂ := 1 + I * t

def z₃' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₃ t -- `by norm_num` also works

def z₄ (t : Icc (0 : ℝ) 1) : ℂ := 1 - t + I

def z₄' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₄ t -- `by norm_num` also works

def z₅ (t : Icc (0 : ℝ) 1) : ℂ := I * t

def z₅' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₅ t -- `by norm_num` also works

def z₆ (t : NNReal) : ℂ := I * (1 + t)

def z₆' (t : ℝ) : ℂ := IciExtend z₆ t -- `by norm_num` also works

end Parametrisations

section UpperHalfPlane

-- Show that the things that go into φ₀ are in the upper half plane

lemma z₁_in_upper_half_plane {t : ℝ} (ht : t ∈ Ioo 0 1) : 0 < (z₁' t).im := by
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioo ht
  rw [z₁', IccExtend_of_mem zero_le_one z₁ ht', z₁]; simp
  exact ht.1

lemma z₂_in_upper_half_plane {t : ℝ} (ht : t ∈ Ioo 0 1) : 0 < (z₂' t).im := by
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioo ht
  rw [z₂', IccExtend_of_mem zero_le_one z₂ ht', z₂]; simp

lemma z₃_in_upper_half_plane {t : ℝ} (ht : t ∈ Ioo 0 1) : 0 < (z₃' t).im := by
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioo ht
  rw [z₃', IccExtend_of_mem zero_le_one z₃ ht', z₃]; simp
  exact ht.1

lemma z₄_in_upper_half_plane {t : ℝ} (ht : t ∈ Ioo 0 1) : 0 < (z₄' t).im := by
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioo ht
  rw [z₄', IccExtend_of_mem zero_le_one z₄ ht', z₄]; simp

lemma z₅_in_upper_half_plane {t : ℝ} (ht : t ∈ Ioo 0 1) : 0 < (z₅' t).im := by
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioo ht
  rw [z₅', IccExtend_of_mem zero_le_one z₅ ht', z₅]; simp
  exact ht.1

lemma z₆_in_upper_half_plane {t : ℝ} (ht : t ∈ Ioi 0) : 0 < (z₆' t).im := by
  have ht' : t ∈ Ici 0 := mem_Ici_of_Ioi ht
  rw [z₆', IciExtend_of_mem z₆ ht', z₆]; simp
  have : 0 ≤ t := ht'
  positivity

end UpperHalfPlane

end MagicFunction.a.Parametrisations

open MagicFunction.a.Parametrisations

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

def I₄' (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..1,
  φ₀'' (-1 / ((z₄' t) - (1 : ℂ)))
  * ((z₄' t) - (1 : ℂ)) ^ 2
  * cexp (π * I * x * (z₄' t))

def I₅' (x : ℝ) : ℂ := -2 * ∫ t in (0 : ℝ)..1, I -- Added factor due to variable change!!
  * φ₀'' (-1 / (z₅' t))
  * (z₅' t) ^ 2
  * cexp (π * I * x * (z₅' t))

def I₆' (x : ℝ) : ℂ := 2 * ∫ t in Ioi (0 : ℝ), I -- Added factor due to variable change!!
  * φ₀'' (-1 / z₆' t)
  * (z₆' t) ^ 2
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

lemma z₁'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₁' t = -1 + I * t := by
  rw [z₁', IccExtend_of_mem zero_le_one z₁ ht, z₁]

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

lemma I_1'_eq' (r : ℝ) : I₁' r = -I * ∫ t in (0 : ℝ)..1,
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

lemma z₂'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₂' t = -1 + t + I := by
  rw [z₂', IccExtend_of_mem zero_le_one z₂ ht, z₂]

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

lemma z₃'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₃' t = 1 + I * t := by
  rw [z₃', IccExtend_of_mem zero_le_one z₃ ht, z₃]

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

lemma z₄'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₄' t = 1 - t + I := by
  rw [z₄', IccExtend_of_mem zero_le_one z₄ ht, z₄]

lemma I₄'_eq (r : ℝ) : I₄' r = ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (-t + I))
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
  _ = φ₀'' (-1 / (-t + I)) * (-t + I) ^ 2 * cexp (π * I * r * (1 - t + I)) := by
      congr 2 <;> ring_nf
  _ = _ := by
      conv_rhs => rw [mul_assoc, mul_assoc]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr
      ring_nf
      rw [I_sq]
      ring_nf

lemma z₅'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₅' t = I * t := by
  rw [z₅', IccExtend_of_mem zero_le_one z₅ ht, z₅]

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

end Eq

end MagicFunction.a.RadialFunctions
