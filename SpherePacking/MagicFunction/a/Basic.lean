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

noncomputable section Parametrisations

private def z₁ (t : Icc (0 : ℝ) 1) : ℂ := -1 * t + I * (1 - t)

private def z₁' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₁ t -- `by norm_num` also works

private def z₂ (t : Icc (0 : ℝ) 1) : ℂ := t + I * (1 - t)

private def z₂' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₂ t -- `by norm_num` also works

private def z₃ (t : Icc (0 : ℝ) 1) : ℂ := I * (1 - t)

private def z₃' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₃ t -- `by norm_num` also works

private def z₄ (t : NNReal) : ℂ := I * t

private def z₄' (t : ℝ) : ℂ := IciExtend z₄ t -- `by norm_num` also works

end Parametrisations

section UpperHalfPlane

-- Show that the things that go into φ₀ are in the upper half plane

private lemma z₁_in_upper_half_plane {t : ℝ} (ht : t ∈ Ioo 0 1) : 0 < (z₁' t).im := by
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioo ht
  rw [z₁', IccExtend_of_mem zero_le_one z₁ ht', z₁]; simp
  exact ht.2

private lemma z₂_in_upper_half_plane {t : ℝ} (ht : t ∈ Ioo 0 1) : 0 < (z₂' t).im := by
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioo ht
  rw [z₂', IccExtend_of_mem zero_le_one z₂ ht', z₂]; simp
  exact ht.2

private lemma z₃_in_upper_half_plane {t : ℝ} (ht : t ∈ Ioo 0 1) : 0 < (z₃' t).im := by
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioo ht
  rw [z₃', IccExtend_of_mem zero_le_one z₃ ht', z₃]; simp
  exact ht.2

private lemma z₄_in_upper_half_plane {t : ℝ} (ht : t ∈ Ioi 0) : 0 < (z₄' t).im := by
  have ht' : t ∈ Ici 0 := mem_Ici_of_Ioi ht
  rw [z₄', IciExtend_of_mem z₄ ht', z₄]; simp
  exact ht

end UpperHalfPlane

noncomputable section Integrals

private def I₁ (x : V) := ∫ t in Ioo (0 : ℝ) 1,
  φ₀'' (-1 / ((z₁' t) + (1 : ℂ))) *
  ((z₁' t) + (1 : ℂ)) ^ 2 *
  cexp (π * I * ‖x‖ ^ 2 * (z₁' t))

private def I₂ (x : V) := ∫ t in Ioo (0 : ℝ) 1,
  φ₀'' (-1 / ((z₂' t) - (1 : ℂ))) *
  ((z₂' t) - (1 : ℂ)) ^ 2 *
  cexp (π * I * ‖x‖ ^ 2 * (z₂' t))

private def I₃ (x : V) := ∫ t in Ioo (0 : ℝ) 1,
  φ₀'' (-1 / (z₃' t)) *
  (z₃' t) ^ 2 *
  cexp (π * I * ‖x‖ ^ 2 * (z₃' t))

private def I₄ (x : V) := ∫ t in Ioi (0 : ℝ),
  φ₀'' (-1 / z₄' t) *
  (z₄' t) ^ 2 *
  cexp (π * I * ‖x‖ ^ 2 * (z₄' t))

end Integrals

noncomputable def a (x : V) := I₁ x + I₂ x + I₃ x + I₄ x
#check a

#min_imports
