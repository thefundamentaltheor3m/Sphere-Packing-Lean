/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

open Set Complex Real

local notation "V" => EuclideanSpace ℝ (Fin 8)

local notation "ℍ₀" => UpperHalfPlane.upperHalfPlaneSet

namespace MagicFunction.Parametrisations

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

def z₆ (t : Ici (1 : ℝ)) : ℂ := I * t

def z₆' (t : ℝ) : ℂ := IciExtend z₆ t -- `by norm_num` also works

end Parametrisations

section UpperHalfPlane

open scoped UpperHalfPlane

lemma im_z₁'_pos {t : ℝ} (ht : t ∈ Ioc 0 1) : 0 < (z₁' t).im := by
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioc ht
  simp only [z₁', IccExtend_of_mem zero_le_one z₁ ht', z₁, add_im, neg_im, one_im, neg_zero, mul_im,
    I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul, zero_add, gt_iff_lt]
  exact ht.1

lemma im_z₂'_pos {t : ℝ} (ht : t ∈ Icc 0 1) : 0 < (z₂' t).im := by
  simp [z₂', IccExtend_of_mem zero_le_one z₂ ht, z₂]

lemma im_z₃'_pos {t : ℝ} (ht : t ∈ Ioc 0 1) : 0 < (z₃' t).im := by
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioc ht
  simp only [z₃', IccExtend_of_mem zero_le_one z₃ ht', z₃, add_im, one_im, mul_im, I_re, ofReal_im,
    mul_zero, I_im, ofReal_re, one_mul, zero_add, gt_iff_lt]
  exact ht.1

lemma im_z₄'_pos {t : ℝ} (ht : t ∈ Icc 0 1) : 0 < (z₄' t).im := by
  simp [z₄', IccExtend_of_mem zero_le_one z₄ ht, z₄]

lemma im_z₅'_pos {t : ℝ} (ht : t ∈ Ioc 0 1) : 0 < (z₅' t).im := by
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioc ht
  simp only [z₅', IccExtend_of_mem zero_le_one z₅ ht', z₅, mul_im, I_re, ofReal_im, mul_zero, I_im,
    ofReal_re, one_mul, zero_add, gt_iff_lt]
  exact ht.1

lemma im_z₆'_pos {t : ℝ} (ht : t ∈ Ici (1 : ℝ)) : 0 < (z₆' t).im := by
  simp only [z₆', IciExtend_of_mem z₆ ht, z₆, mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re,
    one_mul, zero_add]
  rw [mem_Ici] at ht
  linarith

lemma z₁'_mem_upperHalfPlane_set {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : z₁' t ∈ ℍ₀ := im_z₁'_pos ht

lemma z₂'_mem_upperHalfPlane_set {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : z₂' t ∈ ℍ₀ := im_z₂'_pos ht

lemma z₃'_mem_upperHalfPlane_set {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : z₃' t ∈ ℍ₀ := im_z₃'_pos ht

lemma z₄'_mem_upperHalfPlane_set {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : z₄' t ∈ ℍ₀ := im_z₄'_pos ht

lemma z₅'_mem_upperHalfPlane_set {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : z₅' t ∈ ℍ₀ := im_z₅'_pos ht

lemma z₆'_mem_upperHalfPlane_set {t : ℝ} (ht : t ∈ Ici (1 : ℝ)) : z₆' t ∈ ℍ₀ := im_z₆'_pos ht

lemma z₁'_mapsto : MapsTo z₁' (Ioc 0 1) ℍ₀ := fun _ ht ↦ z₁'_mem_upperHalfPlane_set ht

lemma z₂'_mapsto : MapsTo z₂' (Icc 0 1) ℍ₀ := fun _ ht ↦ z₂'_mem_upperHalfPlane_set ht

lemma z₃'_mapsto : MapsTo z₃' (Ioc 0 1) ℍ₀ := fun _ ht ↦ z₃'_mem_upperHalfPlane_set ht

lemma z₄'_mapsto : MapsTo z₄' (Icc 0 1) ℍ₀ := fun _ ht ↦ z₄'_mem_upperHalfPlane_set ht

lemma z₅'_mapsto : MapsTo z₅' (Ioc 0 1) ℍ₀ := fun _ ht ↦ z₅'_mem_upperHalfPlane_set ht

lemma z₆'_mapsto : MapsTo z₆' (Ici 1) ℍ₀ := fun _ ht ↦ z₆'_mem_upperHalfPlane_set ht

end UpperHalfPlane

section eq_of_mem

lemma z₁'_eq_z₁_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₁' t = z₁ ⟨t, ht⟩ := by
  rw [z₁', IccExtend_of_mem zero_le_one z₁ ht]

lemma z₂'_eq_z₂_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₂' t = z₂ ⟨t, ht⟩ := by
  rw [z₂', IccExtend_of_mem zero_le_one z₂ ht]

lemma z₃'_eq_z₃_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₃' t = z₃ ⟨t, ht⟩ := by
  rw [z₃', IccExtend_of_mem zero_le_one z₃ ht]

lemma z₄'_eq_z₄_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₄' t = z₄ ⟨t, ht⟩ := by
  rw [z₄', IccExtend_of_mem zero_le_one z₄ ht]

lemma z₅'_eq_z₅_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₅' t = z₅ ⟨t, ht⟩ := by
  rw [z₅', IccExtend_of_mem zero_le_one z₅ ht]

lemma z₆'_eq_z₆_of_mem {t : ℝ} (ht : t ∈ Ici 1) : z₆' t = z₆ ⟨t, ht⟩ := by
  rw [z₆', IciExtend_of_mem z₆ ht]

lemma z₁'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₁' t = -1 + I * t := by
  rw [z₁'_eq_z₁_of_mem ht, z₁]

lemma z₂'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₂' t = -1 + t + I := by
  rw [z₂'_eq_z₂_of_mem ht, z₂]

lemma z₃'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₃' t = 1 + I * t := by
  rw [z₃'_eq_z₃_of_mem ht, z₃]

lemma z₄'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₄' t = 1 - t + I := by
  rw [z₄'_eq_z₄_of_mem ht, z₄]

lemma z₅'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₅' t = I * t := by
  rw [z₅'_eq_z₅_of_mem ht, z₅]

lemma z₆'_eq_of_mem {t : ℝ} (ht : t ∈ Ici 1) : z₆' t = I * t := by
  rw [z₆'_eq_z₆_of_mem ht, z₆]

end eq_of_mem

section transforms_mem

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup
open scoped MatrixGroups ComplexConjugate

lemma _root_.ModularGroup.ST_eq : S * T = !![(0 : ℤ), -1; 1, 1] := by decide

lemma _root_.ModularGroup.S_eq : S = !![(0 : ℤ), -1; 1, 0] := by rfl

private lemma det_aux : !![(0 : ℤ), -1; 1, 1].det = 1 := by decide

lemma _root_.ModularGroup.ST_eq' : S * T = ⟨!![(0 : ℤ), -1; 1, 1], det_aux⟩ := by
  simp only [← ModularGroup.ST_eq]; norm_cast

lemma _root_.ModularGroup.S_eq' : S = ⟨!![(0 : ℤ), -1; 1, 0], det_aux⟩ := by
  simp only [← ModularGroup.S_eq]; norm_cast

lemma neg_inv_one_add_eq_ST_coe (z : ℍ) :
    -1 / ((z : ℂ) + 1) = UpperHalfPlane.coe ((S * T) • z) := by
  rw [specialLinearGroup_apply]
  simp_all [ST_eq]

lemma neg_inv_one_add_mem (z : ℍ) : 0 < (-1 / ((z : ℂ) + 1)).im := by
  rw [neg_inv_one_add_eq_ST_coe, coe_im]
  exact ((S * T) • z).2

lemma neg_inv_one_add_eq_ST (z : ℍ) :
    ⟨-1 / ((z : ℂ) + 1), neg_inv_one_add_mem z⟩ = (S * T) • z := by
  apply UpperHalfPlane.ext
  rw [← neg_inv_one_add_eq_ST_coe]
  norm_cast

lemma neg_inv_eq_S_coe (z : ℍ) :
    -1 / (z) = UpperHalfPlane.coe (S • z) := by
  rw [specialLinearGroup_apply]
  simp_all [S_eq]

lemma neg_inv_mem (z : ℍ) : 0 < (-1 / (z : ℂ)).im := by
  rw [neg_inv_eq_S_coe, coe_im]
  exact (S • z).2

lemma neg_inv_eq_S (z : ℍ) :
    ⟨-1 / (z : ℂ), neg_inv_mem z⟩ = S • z := by
  apply UpperHalfPlane.ext
  rw [← neg_inv_eq_S_coe]
  norm_cast

end transforms_mem

end MagicFunction.Parametrisations
