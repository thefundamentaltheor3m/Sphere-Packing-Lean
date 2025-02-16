/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

import SpherePacking.ModularForms.Eisenstein
import Mathlib

local notation "V" => EuclideanSpace ℝ (Fin 8)

open Set Complex Real

namespace MagicFunction

noncomputable section Parametrisations

def z₁ (t : Icc (0 : ℝ) 1) : ℂ := -1 * (1 - t) + I * t

def z₁' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₁ t -- `by norm_num` also works

def z₂ (t : Icc (0 : ℝ) 1) : ℂ := (1 - t) + I * t

def z₂' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₂ t -- `by norm_num` also works

def z₃ (t : Icc (0 : ℝ) 1) : ℂ := I * t

def z₃' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₃ t -- `by norm_num` also works

def z₄ (t : NNReal) : ℂ := I * (1 + t)

def z₄' (t : ℝ) : ℂ := IciExtend z₄ t -- `by norm_num` also works

end Parametrisations

section UpperHalfPlane

-- Show that the things that go into φ₀ are in the upper half plane

private lemma z₁_in_upper_half_plane {t : ℝ} (ht : t ∈ Ioo 0 1) : 0 < (z₁' t).im := by
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioo ht
  rw [z₁', IccExtend_of_mem zero_le_one z₁ ht', z₁]; simp
  exact ht.1

private lemma z₂_in_upper_half_plane {t : ℝ} (ht : t ∈ Ioo 0 1) : 0 < (z₂' t).im := by
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioo ht
  rw [z₂', IccExtend_of_mem zero_le_one z₂ ht', z₂]; simp
  exact ht.1

private lemma z₃_in_upper_half_plane {t : ℝ} (ht : t ∈ Ioo 0 1) : 0 < (z₃' t).im := by
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioo ht
  rw [z₃', IccExtend_of_mem zero_le_one z₃ ht', z₃]; simp
  exact ht.1

private lemma z₄_in_upper_half_plane {t : ℝ} (ht : t ∈ Ioi 0) : 0 < (z₄' t).im := by
  have ht' : t ∈ Ici 0 := mem_Ici_of_Ioi ht
  rw [z₄', IciExtend_of_mem z₄ ht', z₄]; simp
  have : 0 ≤ t := ht'
  positivity

end UpperHalfPlane

noncomputable section Real_Input

def I₁' (x : ℝ) := ∫ t in Ioo (0 : ℝ) 1, (1 + I) -- Added factor due to variable change!!
  * φ₀'' (-1 / ((z₁' t) + (1 : ℂ)))
  * ((z₁' t) + (1 : ℂ)) ^ 2
  * cexp (π * I * |x| ^ 2 * (z₁' t))

def I₂' (x : ℝ) := ∫ t in Ioo (0 : ℝ) 1, (1 - I) -- Added factor due to variable change!!
  * φ₀'' (-1 / ((z₂' t) - (1 : ℂ)))
  * ((z₂' t) - (1 : ℂ)) ^ 2
  * cexp (π * I * |x| ^ 2 * (z₂' t))

def I₃' (x : ℝ) := ∫ t in Ioo (0 : ℝ) 1, I -- Added factor due to variable change!!
  * φ₀'' (-1 / (z₃' t))
  * (z₃' t) ^ 2
  * cexp (π * I * |x| ^ 2 * (z₃' t))

def I₄' (x : ℝ) := ∫ t in Ioi (0 : ℝ), I -- Added factor due to variable change!!
  * φ₀'' (-1 / z₄' t)
  * (z₄' t) ^ 2
  * cexp (π * I * |x| ^ 2 * (z₄' t))

def a' (x : ℝ) := I₁' x + I₂' x + I₃' x + I₄' x

end Real_Input

noncomputable section Vector_Input

def I₁ (x : V) := I₁' ‖x‖

def I₂ (x : V) := I₂' ‖x‖

def I₃ (x : V) := I₃' ‖x‖

def I₄ (x : V) := I₄' ‖x‖

def a (x : V) := a' ‖x‖

end Vector_Input

#check a

#min_imports
