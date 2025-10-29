/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Raphael Appenzeller
-/

-- import Mathlib

import SpherePacking.ModularForms.JacobiTheta
import SpherePacking.MagicFunction.IntegralParametrisations

/-! # The ψ Functions

In this file, we define the functions `ψI`, `ψT` and `ψS` that are defined using the
Jacobi theta functions and are used in the definition of the -1-eigenfunction `b`.
-/

open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

-- namespace MagicFunction.b.psi

noncomputable section matrices

/- The matrices `S` and `T` are given by `ModularGroup.S` and `ModularGroup.T`. -/

-- #check ModularGroup.S
-- #check ModularGroup.T

def ModularGroup.I : SL(2, ℤ) := ⟨!![1, 0; 0, 1], by decide⟩

end matrices

noncomputable section defs

/- We begin by defining the `h` function. The `ψ` functions are defined in terms of `h`
via slash actions. -/

def h : ℍ → ℂ := 128 • (H₃_MF + H₄_MF) / (H₂_MF ^ 2)

def ψI : ℍ → ℂ := h - h ∣[-2] (S * T)
def ψT : ℍ → ℂ := ψI ∣[-2] T
def ψS : ℍ → ℂ := ψI ∣[-2] S

def ψI' (z : ℂ) : ℂ := if hz : 0 < z.im then ψI ⟨z, hz⟩ else 0
def ψS' (z : ℂ) : ℂ := if hz : 0 < z.im then ψS ⟨z, hz⟩ else 0
def ψT' (z : ℂ) : ℂ := if hz : 0 < z.im then ψT ⟨z, hz⟩ else 0

end defs

section eq

/- It is possible to express ψI, ψT, ψS in terms of `H`-functions directly. -/

/- We first prove some auxiliary results. -/

section aux

private lemma z_plus_one_nonzero (z : ℍ) : (z + 1 : ℂ) ≠ 0 := by
  have hh : 0 < (z + 1 : ℂ).im  := by
    calc
      0 < z.im := z.2
      _ = (z + 1 : ℂ).im := by simp
  by_contra hz
  rw [hz] at hh
  exact (lt_self_iff_false 0).mp hh

private lemma slashS (z : ℍ) (F : ℍ → ℂ) : (F ∣[(2 : ℤ)] (S)) (z) =
    F (S • z) * (z : ℂ) ^ (-2 : ℤ) := by
  rw [SL_slash_apply, S, denom]
  simp

private lemma slashS' (z : ℍ) (F : ℍ → ℂ) : (F ∣[(-2 : ℤ)] (S)) (z) =
    F (S • z) * (z : ℂ) ^ (2 : ℕ) := by
  rw [SL_slash_apply, S, denom]
  simp only [Int.reduceNeg, sl_moeb, coe2_smul, Fin.isValue,
    SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Int.coe_castRingHom, map_apply, of_apply, cons_val', cons_val_zero,
    cons_val_fin_one, cons_val_one, Int.cast_one, ofReal_one, one_mul, Int.cast_zero,
    ofReal_zero, add_zero, neg_neg, mul_eq_mul_left_iff]
  have pow_coe_nat (a : ℂ) : a ^ (2 : ℕ) = a ^ (2 : ℤ) := by
    rw [zpow_two, pow_two]
  left
  rw [pow_coe_nat]

private lemma slashS'' (z : ℍ) (F : ℍ → ℂ) : F (S • z) =
    (F ∣[(2 : ℤ)] (S)) (z) * (z : ℂ) ^ (2 : ℕ) := by
  rw [slashS, mul_assoc]
  simp only [sl_moeb, Int.reduceNeg, _root_.zpow_neg]
  have inv_mul_cancel (a : ℂ) (nonzero : a ≠ 0) : a⁻¹ * a = (1 : ℂ) := by
    rw [mul_comm]
    apply Complex.mul_inv_cancel
    exact nonzero
  have helper (a : ℂ) : a * a = 0 → a = 0 := by
    simp only [mul_eq_zero, or_self, imp_self]
  have pow_coe_nat (a : ℂ) : a ^ (2 : ℕ) = a ^ (2 : ℤ) := by
    rw [zpow_two, pow_two]
  have sp : (((z : ℂ) ^ (2 : ℤ))⁻¹ * (z : ℂ) ^ 2) = 1 := by
    apply inv_mul_cancel ((z : ℂ) ^ (2 : ℤ))
    simp only [ne_eq]
    intro hP
    apply UpperHalfPlane.ne_zero z
    apply helper
    rw [← pow_two]
    exact hP
  rw [sp]
  simp

private lemma slashT (z : ℍ) (F : ℍ → ℂ) : ((F) ∣[(2 : ℤ)] (T)) (z) = (F) (T • z) := by
  rw [SL_slash_apply, T, denom]
  simp

private lemma slashT' (z : ℍ) (F : ℍ → ℂ) : ((F) ∣[(-2 : ℤ)] (T)) (z) =  (F) (T • z) := by
  rw [SL_slash_apply, T, denom]
  simp
 -- no need for slashT'', as ← slashT already fulfils that role

private lemma S_mul_T : S * T = ⟨!![0, -1; 1, 1], by norm_num [det_fin_two_of]⟩ := by
  ext (i : Fin 2) (j : Fin 2)
  fin_cases i <;> fin_cases j <;> simp [mul_apply, S, T]

-- the following statements will be applied of F = H₂, H₃, H₄ or (H₃+H₄)/H₂^2
private lemma slashST (z : ℍ) (F : ℍ → ℂ) : ((F) ∣[(2 : ℤ)] (S * T)) (z) =
    F ((S * T) • z ) * (z + 1 : ℂ) ^ (-2 : ℤ) := by
  rw [SL_slash_apply, S_mul_T, denom]
  simp

private lemma slashST' (z : ℍ) (F : ℍ → ℂ) : ((F) ∣[(-2 : ℤ)] (S * T)) (z) =
    F ((S * T) • z ) * (z + 1 : ℂ) ^ (2 : ℕ) := by
  rw [SL_slash_apply, S_mul_T, denom]
  simp only [Int.reduceNeg, Fin.isValue, SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom, map_apply,
    of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one, Int.cast_one, ofReal_one,
    one_mul]
  rw [zpow_two, pow_two]

private lemma slashST'' (z : ℍ) (F : ℍ → ℂ) : F ((S * T) • z) =
    (F ∣[(2 : ℤ)] (S * T)) (z) * (z + 1 : ℂ) ^ 2 := by
  rw [slashST, mul_assoc]
  simp only [sl_moeb, map_mul, Int.reduceNeg, _root_.zpow_neg]
  have inv_mul_cancel (a : ℂ) (nonzero : a ≠ 0) : a⁻¹ * a = (1 : ℂ) := by
    rw [mul_comm]
    exact Complex.mul_inv_cancel nonzero
  have helper (a : ℂ) : a * a = 0 → a = 0 := by
    simp only [mul_eq_zero, or_self, imp_self]
  have sp : (((z + 1 : ℂ) ^ (2 : ℤ))⁻¹ * (z + 1 : ℂ) ^ 2) = 1 := by
    apply inv_mul_cancel ((z + 1 : ℂ) ^ (2 : ℤ) )
    simp only [ne_eq]
    intro hP
    apply z_plus_one_nonzero z
    apply helper
    rw [← pow_two]
    exact hP
  rw [sp]
  simp only [mul_one]

end aux

/- We can now prove the main results of this section. Namely Lemma 7.16 in the blueprint -/

lemma ψI_eq : ψI = 128 • ((H₃_MF + H₄_MF) / (H₂_MF ^ 2) + (H₄_MF - H₂_MF) / H₃_MF ^ 2) := by
  rw [ψI, h]
  conv_rhs => rw [smul_add]
  conv_lhs => rw [sub_eq_add_neg, smul_div_assoc 128 (⇑H₃_MF + ⇑H₄_MF) (⇑H₂_MF ^ 2)]
  simp only [Int.reduceNeg, add_right_inj]
  have h2' (z : ℍ) : (H₂_MF : ℍ → ℂ) ((S * T) • z) =
      ((H₂_MF : ℍ → ℂ) ∣[(2 : ℤ)] (S * T)) (z) * (z + 1 : ℂ) ^ 2 := by
    simp only [slashST'']
  have h3' (z : ℍ) : (H₃_MF : ℍ → ℂ) ((S * T) • z) =
      ((H₃_MF : ℍ → ℂ) ∣[(2 : ℤ)] (S * T)) (z) * (z + 1 : ℂ) ^ 2 := by
    simp only [slashST'']
  have h4' (z : ℍ) : (H₄_MF : ℍ → ℂ) ((S * T) • z) =
      ((H₄_MF : ℍ → ℂ) ∣[(2 : ℤ)] (S * T)) (z) * (z + 1 : ℂ) ^ 2 := by
    simp only [slashST'']
  ext z
  rw [Pi.neg_apply, slashST']
  have rewriting (z : ℍ) (F2 F3 F4 : ℍ → ℂ) : (128 • ((F3 + F4) / (F2 ^ 2))) ((S * T) • z) =
      128 • ((F3 ((S * T) • z) + F4 ((S * T) • z)) / ((F2 ((S * T) • z)) ^ 2)) := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat, sl_moeb, map_mul, Pi.div_apply, Pi.add_apply,
      Pi.mul_apply, Pi.ofNat_apply, Pi.pow_apply]
  rw [rewriting, h2', h3' , h4']
  have hh2 : (H₂_MF : ℍ → ℂ) = H₂ := by exact rfl
  have hh3 : (H₃_MF : ℍ → ℂ) = H₃ := by exact rfl
  have hh4 : (H₄_MF : ℍ → ℂ) = H₄ := by exact rfl
  rw [hh2 , hh3, hh4]
  rw [slash_mul, slash_mul, slash_mul, H₂_S_action, H₃_S_action, H₄_S_action,
    SlashAction.neg_slash, SlashAction.neg_slash, SlashAction.neg_slash, H₂_T_action,
    H₃_T_action, H₄_T_action, neg_neg, ← add_mul]
  nth_rw 2 [pow_two]
  have z_plus_one_squared_nonzero (z : ℍ) : (z + 1 : ℂ) ^ 2 ≠ 0 := by
    rw [pow_two, mul_self_ne_zero]
    exact z_plus_one_nonzero (z : ℍ)
  rw [← mul_assoc, mul_div_mul_comm, div_self (z_plus_one_squared_nonzero z), mul_one]
  nth_rw 2 [mul_comm]
  rw [← mul_assoc, ← pow_two, ← div_div, smul_mul_assoc, div_mul_comm,
    div_self (z_plus_one_squared_nonzero z), one_mul, ← neg_nsmul, neg_div', add_comm ]
  simp only [Pi.neg_apply, neg_add_rev, neg_neg, even_two, Even.neg_pow, nsmul_eq_mul,
    Nat.cast_ofNat, Pi.smul_apply, Pi.div_apply, Pi.sub_apply, Pi.pow_apply, mul_eq_mul_left_iff,
    OfNat.ofNat_ne_zero, or_false]
  rw [sub_eq_add_neg]
-- this completes the proof of ψI_eq

lemma ψT_eq : ψT = 128 * ((H₃_MF + H₄_MF) / (H₂_MF ^ 2) + (H₂_MF + H₃_MF) / H₄_MF ^ 2) := by
  rw [ψT, ψI_eq]
  ext z
  rw [slashT']
  simp only [Pi.smul_apply, Pi.add_apply, Pi.div_apply, Pi.pow_apply,
    Pi.sub_apply, smul_add, nsmul_eq_mul, Nat.cast_ofNat, Pi.mul_apply, Pi.ofNat_apply]
  have H2slashT' (z : ℍ) : (H₂_MF : ℍ → ℂ) (T • z) = ((H₂_MF : ℍ → ℂ) ∣[(2 : ℤ)] (T)) (z) := by
    exact Eq.symm (Complex.ext (congrArg Complex.re (slashT z ⇑H₂_MF))
        (congrArg Complex.im (slashT z ⇑H₂_MF)))
  have H3slashT' (z : ℍ) : (H₃_MF : ℍ → ℂ) (T • z) = ((H₃_MF : ℍ → ℂ) ∣[(2 : ℤ)] (T)) (z) := by
    exact Eq.symm (Complex.ext (congrArg Complex.re (slashT z ⇑H₃_MF))
        (congrArg Complex.im (slashT z ⇑H₃_MF)))
  have H4slashT' (z : ℍ): (H₄_MF : ℍ → ℂ) (T • z) = ((H₄_MF : ℍ → ℂ) ∣[(2 : ℤ)] (T)) (z) := by
    exact Eq.symm (Complex.ext (congrArg Complex.re (slashT z ⇑H₄_MF))
        (congrArg Complex.im (slashT z ⇑H₄_MF)))
  rw [H2slashT', H3slashT', H4slashT']
  have hh2 : (H₂_MF : ℍ → ℂ) = H₂ := by exact rfl
  have hh3 : (H₃_MF : ℍ → ℂ) = H₃ := by exact rfl
  have hh4 : (H₄_MF : ℍ → ℂ) = H₄ := by exact rfl
  rw [hh2, hh3, hh4, H₂_T_action, H₃_T_action, H₄_T_action]
  simp [← mul_add, add_comm (H₄ z) (H₃ z), add_comm (H₃ z) (H₂ z)]
-- proof of ψT_eq complete.

-- there was a typo in the blueprint, thats why we first formalized the following version of ψS_eq
-- here is the description that can be found in Maryna's paper.
lemma ψS_eq' : ψS = 128 * ((H₄_MF - H₂_MF) / (H₃_MF ^ 2) - (H₂_MF + H₃_MF) / H₄_MF ^ 2) := by
  rw [ψS, ψI_eq]
  ext z
  rw [slashS']
  simp only [Pi.smul_apply, Pi.add_apply, Pi.div_apply, Pi.pow_apply,
    Pi.sub_apply, smul_add, nsmul_eq_mul, Nat.cast_ofNat, Pi.mul_apply, Pi.ofNat_apply]
  have H2slashS'' (z : ℍ) : (H₂_MF : ℍ → ℂ) (S • z) =
      ((H₂_MF : ℍ → ℂ) ∣[(2 : ℤ)] (S)) (z) * (z : ℂ) ^ (2 : ℕ) := by
    exact slashS'' z ⇑H₂_MF
  have H3slashS'' (z : ℍ) : (H₃_MF : ℍ → ℂ) (S • z) =
      ((H₃_MF : ℍ → ℂ) ∣[(2 : ℤ)] (S)) (z) * (z : ℂ) ^ (2 : ℕ) := by
    exact slashS'' z ⇑H₃_MF
  have H4slashS'' (z : ℍ): (H₄_MF : ℍ → ℂ) (S • z) =
      ((H₄_MF : ℍ → ℂ) ∣[(2 : ℤ)] (S)) (z) * (z : ℂ) ^ (2 : ℕ) := by
    exact slashS'' z ⇑H₄_MF
  rw [H2slashS'', H3slashS'', H4slashS'']
  have hh2 : (H₂_MF : ℍ → ℂ) = H₂ := by exact rfl
  have hh3 : (H₃_MF : ℍ → ℂ) = H₃ := by exact rfl
  have hh4 : (H₄_MF : ℍ → ℂ) = H₄ := by exact rfl
  rw [hh2 , hh3, hh4, H₂_S_action, H₃_S_action, H₄_S_action]
  have z_square_nonzero : (z : ℂ) ^ 2 ≠ 0 := by
    rw [pow_two, mul_self_ne_zero]
    exact ne_zero z
  rw [← add_mul, ← sub_mul, ← mul_add, mul_assoc, add_mul]
  nth_rw 2 [pow_two]
  rw [mul_assoc]
  nth_rw 5 [mul_comm]
  rw [← mul_assoc, ← mul_assoc, div_mul, ← mul_div_assoc',  ← mul_div_assoc',
    div_self z_square_nonzero, mul_one]
  nth_rw 3 [mul_comm]
  rw [← div_div, mul_div, div_self z_square_nonzero, mul_one, add_comm]
  nth_rw 2 [pow_two]
  rw [mul_assoc]
  nth_rw 5 [mul_comm]
  rw [← mul_assoc, ← mul_assoc, div_mul, ← mul_div_assoc',  ← mul_div_assoc',
    div_self z_square_nonzero, mul_one]
  nth_rw 3 [mul_comm]
  rw [← div_div, mul_div, div_self z_square_nonzero, mul_one]
  simp only [Pi.neg_apply, sub_neg_eq_add, mul_neg, neg_mul, neg_neg, mul_eq_mul_left_iff,
    OfNat.ofNat_ne_zero, or_false]
  nth_rw 2 [add_comm]
  rw [← sub_eq_add_neg, ← pow_two, ← pow_two, ← neg_add, ← neg_div', ← sub_eq_add_neg ]
  nth_rw 2 [add_comm]
-- proof of ψS_eq' complete.

lemma ψS_eq : ψS = 128 * (- ((H₂_MF + H₃_MF) / H₄_MF ^ 2) - (H₂_MF - H₄_MF) / (H₃_MF ^ 2)) := by
  rw [ψS_eq', sub_eq_add_neg (H₄_MF : ℍ → ℂ), add_comm (H₄_MF : ℍ → ℂ) _,
    ← sub_neg_eq_add, ← neg_sub', neg_div, ← neg_add', add_comm, neg_add']
-- proof of ψS_eq complete.

end eq

section rels

lemma ψT_slash_T : ψT ∣[-2] T = ψI := by
  ext z
  rw [ψT_eq , ψI_eq , slashT']
  simp only [Pi.mul_apply, Pi.ofNat_apply, Pi.add_apply, Pi.div_apply,
    Pi.pow_apply, Pi.smul_apply, Pi.sub_apply, smul_add, nsmul_eq_mul, Nat.cast_ofNat]
  rw [← slashT z ⇑H₂_MF, ← slashT z ⇑H₃_MF, ← slashT z ⇑H₄_MF]
  have hh2 : (H₂_MF : ℍ → ℂ) = H₂ := by exact rfl
  have hh3 : (H₃_MF : ℍ → ℂ) = H₃ := by exact rfl
  have hh4 : (H₄_MF : ℍ → ℂ) = H₄ := by exact rfl
  rw [hh2, hh3, hh4, H₂_T_action, H₃_T_action, H₄_T_action]
  simp [← mul_add, add_comm (H₄ z) (H₃ z), add_comm  (- (H₂ z)) (H₄ z), sub_eq_add_neg]
-- proof of ψT_slash_T complete.

lemma ψS_slash_S : ψS ∣[-2] S = ψI := by
  ext z
  rw [ψS_eq' , ψI_eq , slashS']
  simp only [Pi.mul_apply, Pi.ofNat_apply, Pi.add_apply, Pi.div_apply,
    Pi.pow_apply, Pi.smul_apply, Pi.sub_apply, smul_add, nsmul_eq_mul, Nat.cast_ofNat]
  rw [slashS'' z ⇑H₂_MF, slashS'' z ⇑H₃_MF, slashS'' z ⇑H₄_MF]
  have hh2 : (H₂_MF : ℍ → ℂ) = H₂ := by exact rfl
  have hh3 : (H₃_MF : ℍ → ℂ) = H₃ := by exact rfl
  have hh4 : (H₄_MF : ℍ → ℂ) = H₄ := by exact rfl
  rw [hh2 , hh3, hh4, H₂_S_action, H₃_S_action, H₄_S_action]
  simp only [Pi.neg_apply, neg_mul, sub_neg_eq_add, even_two, Even.neg_pow]
  have z_square_nonzero : (z : ℂ) ^ 2 ≠ 0 := by
    rw [pow_two, mul_self_ne_zero]
    exact ne_zero z
  rw [add_comm, ← sub_eq_add_neg, ← mul_sub_right_distrib]
  nth_rw 2 [pow_two]
  rw [mul_assoc, mul_assoc]
  nth_rw 5 [mul_comm]
  rw [← mul_assoc, ← mul_assoc, ← mul_div, ← div_div, div_right_comm, mul_div,
    div_self z_square_nonzero, mul_one, ← mul_assoc, ← pow_two, mul_assoc, mul_sub_right_distrib,
    div_mul, mul_div_assoc, div_self z_square_nonzero, mul_one]
  rw[← neg_add, ← neg_div', neg_mul, sub_neg_eq_add, add_comm, ← add_mul]
  nth_rw 2 [pow_two]
  rw [← mul_assoc]
  nth_rw 6 [mul_comm]
  rw [div_mul]
  nth_rw 2 [← mul_div]
  rw [div_self z_square_nonzero, mul_one, mul_assoc, ← pow_two, ← mul_div, ← div_div, mul_div,
    div_self z_square_nonzero, mul_one, ← mul_add]
  nth_rw 2 [add_comm]
-- proof of ψS_slash_S complete

lemma ψS_slash_ST : ψS ∣[-2] (S * T) = ψT := by
  ext z
  rw [ψS_eq', ψT_eq, slashST']
  simp only [Pi.mul_apply, Pi.ofNat_apply, Pi.sub_apply, Pi.div_apply,
    Pi.pow_apply, Pi.add_apply]
  rw [slashST'' z ⇑H₂_MF, slashST'' z ⇑H₃_MF, slashST'' z ⇑H₄_MF]
  have hh2 : (H₂_MF : ℍ → ℂ) = H₂ := by exact rfl
  have hh3 : (H₃_MF : ℍ → ℂ) = H₃ := by exact rfl
  have hh4 : (H₄_MF : ℍ → ℂ) = H₄ := by exact rfl
  rw [hh2 , hh3, hh4, slash_mul, slash_mul, slash_mul, H₂_S_action, H₃_S_action, H₄_S_action,
    SlashAction.neg_slash, SlashAction.neg_slash, SlashAction.neg_slash,
    H₂_T_action, H₃_T_action, H₄_T_action]
  simp only [Pi.neg_apply, neg_neg, neg_mul, sub_neg_eq_add, even_two, Even.neg_pow]
  have z_plus_one_squared_nonzero (z : ℍ) : (z + 1 : ℂ) ^ 2 ≠ 0 := by
    rw [pow_two, mul_self_ne_zero]
    exact z_plus_one_nonzero (z : ℍ)
  rw [mul_assoc, ← add_mul]
  nth_rw 2 [pow_two]
  rw [mul_assoc]
  nth_rw 5 [mul_comm]
  rw [← mul_assoc, ← mul_assoc, ← mul_div, ← div_div, div_right_comm, mul_div,
    div_self (z_plus_one_squared_nonzero z), mul_one, ← mul_assoc, ← pow_two, mul_assoc,
    mul_sub_right_distrib, div_mul, mul_div_assoc, div_self (z_plus_one_squared_nonzero z), mul_one]
  rw[← neg_add, ← neg_div', neg_mul, sub_neg_eq_add, add_comm, ← add_mul]
  nth_rw 2 [pow_two]
  rw [← mul_assoc]
  nth_rw 6 [mul_comm]
  rw [div_mul]
  nth_rw 2 [← mul_div]
  rw [div_self (z_plus_one_squared_nonzero z), mul_one, mul_assoc, ← pow_two, ← mul_div,
     ← div_div, mul_div, div_self (z_plus_one_squared_nonzero z), mul_one]

-- In my thesis, the - sign before ψS is missing. Makes no difference because we bound integrals in
-- absolute value, but point is that this way the Js look even more similar to the Is!
lemma ψS_slash_T : ψS ∣[-2] T = -ψS := by
  ext z
  rw [ψS_eq', slashT']
  simp only [Pi.mul_apply, Pi.add_apply, Pi.div_apply,
    Pi.pow_apply,  Pi.sub_apply]
  rw [← slashT z ⇑H₂_MF, ← slashT z ⇑H₃_MF, ← slashT z ⇑H₄_MF]
  have hh2 : (H₂_MF : ℍ → ℂ) = H₂ := by exact rfl
  have hh3 : (H₃_MF : ℍ → ℂ) = H₃ := by exact rfl
  have hh4 : (H₄_MF : ℍ → ℂ) = H₄ := by exact rfl
  rw [hh2 , hh3, hh4, H₂_T_action, H₃_T_action, H₄_T_action]
  simp only [Pi.ofNat_apply, Pi.neg_apply, sub_neg_eq_add, Pi.mul_apply, Pi.sub_apply, Pi.div_apply,
    Pi.pow_apply, Pi.add_apply]
  rw [sub_eq_add_neg, add_comm, ← sub_neg_eq_add, ← neg_sub', mul_neg, add_comm,
    ← sub_eq_add_neg, add_comm (H₃ z) _ ]
-- proof of ψS_slash_T complete

lemma ψT_slash_S : ψT ∣[-2] S = -ψT := by
  ext z
  rw [ψT_eq, slashS']
  simp only [Pi.mul_apply, Pi.ofNat_apply, Pi.add_apply, Pi.div_apply,
    Pi.pow_apply, Pi.neg_apply]
  rw [slashS'' z ⇑H₂_MF, slashS'' z ⇑H₃_MF, slashS'' z ⇑H₄_MF]
  have hh2 : (H₂_MF : ℍ → ℂ) = H₂ := rfl
  have hh3 : (H₃_MF : ℍ → ℂ) = H₃ := rfl
  have hh4 : (H₄_MF : ℍ → ℂ) = H₄ := rfl
  rw [hh2 , hh3, hh4, H₂_S_action, H₃_S_action, H₄_S_action]
  simp only [Pi.neg_apply, neg_mul, even_two, Even.neg_pow]
  have z_square_nonzero : (z : ℂ) ^ 2 ≠ 0 := by
    rw [pow_two, mul_self_ne_zero]
    exact ne_zero z
  rw [mul_assoc, ← neg_add, ← add_mul, add_mul]
  nth_rw 2 [pow_two]
  rw [mul_assoc]
  nth_rw 5 [mul_comm]
  rw [← mul_assoc, ← mul_assoc, neg_div, ← mul_div, ← div_div, div_right_comm, mul_div,
    div_self z_square_nonzero, mul_one, neg_mul,  ← div_div, div_mul, ← pow_two,
    div_self z_square_nonzero, div_one]
  rw[← neg_add, ← neg_div', neg_mul, add_comm, ← add_mul]
  nth_rw 2 [pow_two]
  rw [← mul_assoc]
  nth_rw 6 [mul_comm]
  rw [div_mul]
  nth_rw 2 [← mul_div]
  rw [div_self z_square_nonzero, mul_one, mul_assoc, ← pow_two, ← mul_div, ← div_div,
    mul_div, div_self z_square_nonzero, mul_one, ← sub_eq_add_neg, ← neg_add', mul_neg]
  nth_rw 2 [add_comm]
  nth_rw 3 [add_comm]
-- proof of ψT_slash_S complete

lemma ψI_slash_TS : ψI ∣[-2] (T * S) = -ψT := by
  ext z
  rw [slash_mul]
  have def_ψT : ψT = ψI ∣[-2] (T) := rfl
  rw [← def_ψT, ψT_slash_S]


lemma ψS_slash_STS : ψS ∣[-2] (S * T * S) = -ψT := by
  ext z
  rw [slash_mul, slash_mul, ψS_slash_S]
  have def_ψT : ψT = ψI ∣[-2] (T) := rfl
  rw [← def_ψT, ψT_slash_S]

lemma ψS_slash_TSTS : ψS ∣[-2] (T * S * T * S) = ψT := by
  ext z
  rw [slash_mul, slash_mul, slash_mul, ψS_slash_T, neg_slash, ψS_slash_S, neg_slash]
  have def_ψT : ψT = ψI ∣[-2] (T) := rfl
  rw [← def_ψT, neg_slash, ψT_slash_S]
  simp

end rels

open MagicFunction.Parametrisations Set

example {t : ℝ} (ht : t ∈ Ioc 0 1) : t ∈ Icc 0 1 := mem_Icc_of_Ioc ht

section eq_of_mem

lemma ψI'_eq_ψI_of_mem {z : ℂ} (hz : 0 < z.im) : ψI' z = ψI ⟨z, hz⟩ := by simp [ψI', hz]

lemma ψS'_eq_ψS_of_mem {z : ℂ} (hz : 0 < z.im) : ψS' z = ψS ⟨z, hz⟩ := by simp [ψS', hz]

lemma ψT'_eq_ψT_of_mem {z : ℂ} (hz : 0 < z.im) : ψT' z = ψT ⟨z, hz⟩ := by simp [ψT', hz]

lemma ψT'_comp_z₁'_eq_ψT_comp_z₁'_of_mem {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψT' (z₁' t) = ψT ⟨z₁' t, z₁'_in_upper_half_plane ht⟩ :=
  ψT'_eq_ψT_of_mem (z₁'_in_upper_half_plane ht)

lemma ψS'_comp_z₁'_eq_ψS_comp_z₁'_of_mem {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψS' (z₁' t) = ψS ⟨z₁' t, z₁'_in_upper_half_plane ht⟩ :=
  ψS'_eq_ψS_of_mem (z₁'_in_upper_half_plane ht)

lemma ψI'_comp_z₁'_eq_ψI_comp_z₁'_of_mem {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψI' (z₁' t) = ψI ⟨z₁' t, z₁'_in_upper_half_plane ht⟩ :=
  ψI'_eq_ψI_of_mem (z₁'_in_upper_half_plane ht)

lemma ψT'_comp_z₂'_eq_ψT_comp_z₂'_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) :
  ψT' (z₂' t) = ψT ⟨z₂' t, z₂'_in_upper_half_plane ht⟩ :=
  ψT'_eq_ψT_of_mem (z₂'_in_upper_half_plane ht)

lemma ψS'_comp_z₂'_eq_ψS_comp_z₂'_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) :
  ψS' (z₂' t) = ψS ⟨z₂' t, z₂'_in_upper_half_plane ht⟩ :=
  ψS'_eq_ψS_of_mem (z₂'_in_upper_half_plane ht)

lemma ψI'_comp_z₂'_eq_ψI_comp_z₂'_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) :
  ψI' (z₂' t) = ψI ⟨z₂' t, z₂'_in_upper_half_plane ht⟩ :=
  ψI'_eq_ψI_of_mem (z₂'_in_upper_half_plane ht)

lemma ψT'_comp_z₃'_eq_ψT_comp_z₃'_of_mem {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψT' (z₃' t) = ψT ⟨z₃' t, z₃'_in_upper_half_plane ht⟩ :=
  ψT'_eq_ψT_of_mem (z₃'_in_upper_half_plane ht)

lemma ψS'_comp_z₃'_eq_ψS_comp_z₃'_of_mem {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψS' (z₃' t) = ψS ⟨z₃' t, z₃'_in_upper_half_plane ht⟩ :=
  ψS'_eq_ψS_of_mem (z₃'_in_upper_half_plane ht)

lemma ψI'_comp_z₃'_eq_ψI_comp_z₃'_of_mem {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψI' (z₃' t) = ψI ⟨z₃' t, z₃'_in_upper_half_plane ht⟩ :=
  ψI'_eq_ψI_of_mem (z₃'_in_upper_half_plane ht)

lemma ψT'_comp_z₄'_eq_ψT_comp_z₄'_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) :
  ψT' (z₄' t) = ψT ⟨z₄' t, z₄'_in_upper_half_plane ht⟩ :=
  ψT'_eq_ψT_of_mem (z₄'_in_upper_half_plane ht)

lemma ψS'_comp_z₄'_eq_ψS_comp_z₄'_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) :
  ψS' (z₄' t) = ψS ⟨z₄' t, z₄'_in_upper_half_plane ht⟩ :=
  ψS'_eq_ψS_of_mem (z₄'_in_upper_half_plane ht)

lemma ψI'_comp_z₄'_eq_ψI_comp_z₄'_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) :
  ψI' (z₄' t) = ψI ⟨z₄' t, z₄'_in_upper_half_plane ht⟩ :=
  ψI'_eq_ψI_of_mem (z₄'_in_upper_half_plane ht)

lemma ψT'_comp_z₅'_eq_ψT_comp_z₅'_of_mem {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψT' (z₅' t) = ψT ⟨z₅' t, z₅'_in_upper_half_plane ht⟩ :=
  ψT'_eq_ψT_of_mem (z₅'_in_upper_half_plane ht)

lemma ψS'_comp_z₅'_eq_ψS_comp_z₅'_of_mem {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψS' (z₅' t) = ψS ⟨z₅' t, z₅'_in_upper_half_plane ht⟩ :=
  ψS'_eq_ψS_of_mem (z₅'_in_upper_half_plane ht)

lemma ψI'_comp_z₅'_eq_ψI_comp_z₅'_of_mem {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψI' (z₅' t) = ψI ⟨z₅' t, z₅'_in_upper_half_plane ht⟩ :=
  ψI'_eq_ψI_of_mem (z₅'_in_upper_half_plane ht)

lemma ψT'_comp_z₆'_eq_ψT_comp_z₆'_of_mem {t : ℝ} (ht : t ∈ Ioi 1) :
  ψT' (z₆' t) = ψT ⟨z₆' t, z₆'_in_upper_half_plane ht⟩ :=
  ψT'_eq_ψT_of_mem (z₆'_in_upper_half_plane ht)

lemma ψS'_comp_z₆'_eq_ψS_comp_z₆'_of_mem {t : ℝ} (ht : t ∈ Ioi 1) :
  ψS' (z₆' t) = ψS ⟨z₆' t, z₆'_in_upper_half_plane ht⟩ :=
  ψS'_eq_ψS_of_mem (z₆'_in_upper_half_plane ht)

lemma ψI'_comp_z₆'_eq_ψI_comp_z₆'_of_mem {t : ℝ} (ht : t ∈ Ioi 1) :
  ψI' (z₆' t) = ψI ⟨z₆' t, z₆'_in_upper_half_plane ht⟩ :=
  ψI'_eq_ψI_of_mem (z₆'_in_upper_half_plane ht)

end eq_of_mem

section slash_explicit

lemma ψS_slash_ST_apply (z : ℍ) :
    (ψS ∣[-2] (S * T)) z = ψS ⟨-1 / (z + 1), neg_inv_one_add_mem z⟩ * (z + 1) ^ 2 := by
  rw [SL_slash_apply ψS (S * T) z, ← neg_inv_one_add_eq_ST z]
  congr 1
  rw [denom, ModularGroup.ST_eq']
  simp only [Int.reduceNeg, Fin.isValue, SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom, map_apply,
    of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one, Int.cast_one, ofReal_one,
    one_mul, neg_neg]
  norm_cast

lemma ψS_slash_ST_apply' (z : ℍ) : (ψS ∣[-2] (S * T)) z = ψS' (-1 / (z + 1)) * (z + 1) ^ 2 := by
  rw [ψS_slash_ST_apply, ← ψS'_eq_ψS_of_mem]

end slash_explicit

section rels_explicit

lemma ψS_slash_ST_explicit₁ {t : ℝ} (ht : t ∈ Ioc 0 1) :
    ψT' (z₁' t) = ψS' (-1 / (z₁' t + 1)) * (z₁' t + 1) ^ 2 := by
  rw [ψT'_comp_z₁'_eq_ψT_comp_z₁'_of_mem ht, ← ψS_slash_ST, ψS_slash_ST_apply' _]
  congr

lemma ψS_slash_ST_explicit₂ {t : ℝ} (ht : t ∈ Icc 0 1) :
    ψT' (z₂' t) = ψS' (-1 / (z₂' t + 1)) * (z₂' t + 1) ^ 2 := by
  rw [ψT'_comp_z₂'_eq_ψT_comp_z₂'_of_mem ht, ← ψS_slash_ST, ψS_slash_ST_apply' _]
  congr

lemma ψS_slash_ST_explicit₃ {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψT' (z₃' t) = ψS' (-1 / (z₃' t + 1)) * (z₃' t + 1) ^ 2 := by
  rw [ψT'_comp_z₃'_eq_ψT_comp_z₃'_of_mem ht, ← ψS_slash_ST, ψS_slash_ST_apply' _]
  congr

lemma ψS_slash_ST_explicit₄ {t : ℝ} (ht : t ∈ Icc 0 1) :
  ψT' (z₄' t) = ψS' (-1 / (z₄' t + 1)) * (z₄' t + 1) ^ 2 := by
  rw [ψT'_comp_z₄'_eq_ψT_comp_z₄'_of_mem ht, ← ψS_slash_ST, ψS_slash_ST_apply' _]
  congr

lemma ψS_slash_ST_explicit₅ {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψT' (z₅' t) = ψS' (-1 / (z₅' t + 1)) * (z₅' t + 1) ^ 2 := by
  rw [ψT'_comp_z₅'_eq_ψT_comp_z₅'_of_mem ht, ← ψS_slash_ST, ψS_slash_ST_apply' _]
  congr

lemma ψS_slash_ST_explicit₆ {t : ℝ} (ht : t ∈ Ioi 1) :
  ψT' (z₆' t) = ψS' (-1 / (z₆' t + 1)) * (z₆' t + 1) ^ 2 := by
  rw [ψT'_comp_z₆'_eq_ψT_comp_z₆'_of_mem ht, ← ψS_slash_ST, ψS_slash_ST_apply' _]
  congr

end rels_explicit
