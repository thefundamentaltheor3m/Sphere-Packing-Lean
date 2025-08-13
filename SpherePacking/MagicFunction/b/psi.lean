/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Raphael Appenzeller
-/

-- import Mathlib

import SpherePacking.ModularForms.JacobiTheta

/-! # The ψ Functions

In this file, we define the functions `ψI`, `ψT` and `ψS` that are defined using the
Jacobi theta functions and are used in the definition of the -1-eigenfunction `b`.
-/

open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R
local notation "SL(" n ", " R ")" "⁺" => Matrix.SLPos (Fin n) R

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
  simp only [sl_moeb, Int.reduceNeg, zpow_neg]
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
  fin_cases i; fin_cases j <;>
  · simp [mul_apply, S, T]
  · simp [mul_apply, S, T]

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
  have pow_coe_nat (a : ℂ) : a ^ (2 : ℕ) = a ^ (2 : ℤ) := by
    rw [zpow_two, pow_two]
  rw [pow_coe_nat]

private lemma slashST'' (z : ℍ) (F : ℍ → ℂ) : F ((S * T) • z) =
    (F ∣[(2 : ℤ)] (S * T)) (z) * (z + 1 : ℂ) ^ 2 := by
  rw [slashST, mul_assoc]
  simp only [sl_moeb, map_mul, Int.reduceNeg, zpow_neg]
  have inv_mul_cancel (a : ℂ) (nonzero : a ≠ 0) : a⁻¹ * a = (1 : ℂ) := by
    rw [mul_comm]
    apply Complex.mul_inv_cancel
    exact nonzero
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
    H₃_T_action, H₄_T_action]
  field_simp -- if I replace this with the result of simp? the proof breaks
  -- d = (z +1)^2
  have resolve (a2 a3 a4 d : ℂ) :  - (128 * ( - (a4 * d) + a2 *d) * d)
    = 128 * (a4 - a2) * d * d := by
    have resolve' : - (a4 * d) + a2 * d = - (a4 - a2) * d := by
      simp only [neg_sub]
      rw [@neg_add_eq_sub, @mul_sub_right_distrib]
    rw [resolve', mul_comm, ← mul_neg, ← mul_neg, neg_mul_eq_neg_mul, neg_neg]
    field_simp only [div_eq_mul_inv, mul_comm, sub_eq_add_neg, sub_eq_iff_eq_add]
    simp only [mul_eq_mul_left_iff]
    rw [mul_assoc]
    left
    simp only
  rw [resolve]
  -- a = H₄ - H₂ , d = (z +1)^2
  · have resolve'' (a a3 d : ℂ) (dnonzero : d ≠ 0): 128 * a *d * d / (a3 * d) ^ 2
      = 128 * a / a3 ^ 2 := by
      rw [pow_two, pow_two, mul_comm a3 d, ← mul_assoc (d * a3) d a3, mul_comm (d * a3) d,
        ← mul_assoc d d a3, ← div_div, ←  div_div, ← div_div, ← mul_div_assoc',
        div_self, mul_one, ← mul_div_assoc', div_self, mul_one, div_div]
      exact dnonzero
      exact dnonzero
    rw [resolve'']
    exact pow_ne_zero 2 (z_plus_one_nonzero z)
  -- this is a weird additional goal that got generated at some point..
  · exact h z
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
  field_simp -- if I replace this with the result of simp? the proof breaks
  rw [← mul_div_assoc', ← mul_div_assoc', ←  mul_add, add_comm (H₄ z) (H₃ z),
    add_comm (H₃ z) (H₂ z) ]
-- proof of ψT_eq complete.

-- there was a typo in the blueprint, thats why we first formalized the following version of ψS_eq
-- the description that can be found in Maryna's paper can be found below.
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
  field_simp -- if I replace this with the result of simp? the proof breaks
  have resolve (h2 h3 h4 d : ℂ) (dnonzero : d ≠ 0) :
    128 * ( - (h3 * d) + - (h2 * d)) / (h4 * d) ^ 2 = - (128 * ((h2 + h3) / (h4) ^ 2 )) / d := by
    have resolve' : -(h3 * d) + -(h2 * d) = - ((h2 + h3) * d) := by
      rw [← @neg_add, @right_distrib, add_comm]
    rw [resolve', mul_neg, ← neg_div', pow_two, ← mul_assoc 128 _ _, mul_comm h4 d,
      mul_assoc d h4 (d * h4), ← div_div, ← mul_div_assoc', div_self, mul_one,
      mul_comm d h4, ← mul_assoc h4 h4 d, ← div_div, mul_div_assoc, ← pow_two, neg_div']
    exact dnonzero
  rw [resolve]
  · have resolve' (h2 h3 h4 d : ℂ) (dnonzero : d ≠ 0) :
      128 * ( - (h2 * d) + (h4 * d) ) / (h3 * d) ^ 2 = (128 * ((h4 - h2) / (h3) ^ 2 )) / d := by
      have resolve'' : - (h2 * d) + (h4 * d) = (h4 - h2) * d := by
        rw [@neg_add_eq_sub, ← sub_mul]
      rw [resolve'', ← mul_assoc 128 _ _, pow_two, mul_comm h3 d, mul_assoc d h3 (d * h3),
        ← div_div, ← mul_div_assoc', div_self, mul_one, mul_comm d h3,
        ← mul_assoc h3 h3 d, ← div_div, mul_div_assoc, ← pow_two ]
      exact dnonzero
    rw [resolve']
    · rw [← add_div, div_mul, div_self]
      · rw [div_one, ← mul_neg, ← mul_add, add_comm]
        simp only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
        rw [@Mathlib.Tactic.RingNF.add_neg]
      · exact pow_ne_zero 2 (UpperHalfPlane.ne_zero z)
    · exact pow_ne_zero 2 (UpperHalfPlane.ne_zero z)
  · exact pow_ne_zero 2 (UpperHalfPlane.ne_zero z)
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
  field_simp -- if I replace this by the result of simp?, the proof no longer works.
  rw [← mul_div_assoc', ← mul_div_assoc', ← mul_add, add_comm (H₄ z) (H₃ z),
    add_comm  (- (H₂ z)) (H₄ z), Mathlib.Tactic.RingNF.add_neg]
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
  have resolve (h2 h3 h4 d : ℂ) (d_nonzero : d ≠ 0) : (- (h2 * d) + h4 * d) / (h3 * d) ^ 2 =
      (h4 - h2) / (h3 ^ 2) / d := by
    rw [← neg_mul, add_comm, ← right_distrib, ← sub_eq_add_neg, pow_two,
      mul_comm h3 d, mul_assoc d h3 (d * h3), ← div_div, ← mul_div_assoc',
      div_self, mul_one, mul_comm d h3, ← mul_assoc, ←  div_div, ← pow_two]
    exact d_nonzero
  rw [resolve]
  · have resolve' (h2 h3 h4 d : ℂ) (d_nonzero : d ≠ 0) : (- (h4 * d) + - (h3 * d)) / (h2 * d) ^ 2 =
        - ((h4 + h3) / (h2 ^ 2) / d) := by
      rw [← neg_add, ← neg_div', ← right_distrib, pow_two, mul_comm h2 d,
        mul_assoc d h2 (d * h2), ← div_div, ← mul_div_assoc', div_self]
      · rw [mul_one, mul_comm d h2, ← mul_assoc, ← div_div, ← pow_two]
      · exact d_nonzero
    rw [resolve']
    · rw [sub_neg_eq_add, ← add_div, mul_assoc, div_mul, div_self]
      · rw [div_one, left_distrib, add_comm, add_comm (H₄ z) (H₃ z)]
      · exact pow_ne_zero 2 (UpperHalfPlane.ne_zero z)
    · exact pow_ne_zero 2 (UpperHalfPlane.ne_zero z)
  · exact pow_ne_zero 2 (UpperHalfPlane.ne_zero z)
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
  have resolve (h2 h3 h4 d : ℂ) (d_nonzero : d ≠ 0) : ((h2 * d) + h3 * d) / (h4 * d) ^ 2 =
      (h2 + h3) / (h4 ^ 2) / d := by
    rw [← right_distrib, pow_two, mul_comm h4 d, mul_assoc d h4 (d * h4), ← div_div,
       ← mul_div_assoc', div_self, mul_one, mul_comm d h4, ← mul_assoc,←  div_div, ← pow_two ]
    exact d_nonzero
  rw [resolve]
  · have resolve' (h2 h3 h4 d : ℂ) (d_nonzero : d ≠ 0) : (- (h4 * d) + - (h3 * d) ) / (h2 * d) ^ 2 =
        - ((h4 + h3) / (h2 ^ 2) / d ) := by
      rw [← neg_add, ← neg_div', ← right_distrib, pow_two, mul_comm h2 d,
        mul_assoc d h2 (d * h2), ← div_div, ← mul_div_assoc', div_self,
        mul_one, mul_comm d h2, ← mul_assoc,←  div_div, ← pow_two ]
      exact d_nonzero
    rw [resolve']
    · rw [sub_neg_eq_add, ← add_div, mul_assoc, div_mul, div_self]
      · rw [div_one, left_distrib, add_comm, left_distrib]
      · exact pow_ne_zero 2 (z_plus_one_nonzero z)
    · exact pow_ne_zero 2 (z_plus_one_nonzero z)
  · exact pow_ne_zero 2 (z_plus_one_nonzero z)
-- proof of ψS_slash_ST complete

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
  have hh2 : (H₂_MF : ℍ → ℂ) = H₂ := by exact rfl
  have hh3 : (H₃_MF : ℍ → ℂ) = H₃ := by exact rfl
  have hh4 : (H₄_MF : ℍ → ℂ) = H₄ := by exact rfl
  rw [hh2 , hh3, hh4, H₂_S_action, H₃_S_action, H₄_S_action]
  simp only [Pi.neg_apply, neg_mul, even_two, Even.neg_pow]
  have resolve (h2 h3 h4 d : ℂ) (d_nonzero : d ≠ 0) : (- (h4 * d) + - (h3 * d)) / (h2 * d) ^ 2 =
      - ((h4 + h3) / (h2 ^ 2) / d ) := by
    rw [← neg_add, ← neg_div', ← right_distrib, pow_two, mul_comm h2 d,
      mul_assoc d h2 (d * h2), ← div_div, ← mul_div_assoc', div_self]
    · rw [mul_one, mul_comm d h2, ← mul_assoc, ← div_div, ← pow_two]
    · exact d_nonzero
  rw [resolve]
  · rw [resolve]
    · rw [neg_div', neg_div', neg_div', ← add_div, mul_div_assoc', div_mul, div_self]
      · rw [div_one, neg_div, ← sub_eq_add_neg, ← neg_add', mul_neg, add_comm,
          add_comm (H₄ z) _, add_comm (H₃ z) (H₂  z)]
      · exact pow_ne_zero 2 (UpperHalfPlane.ne_zero z)
    · exact pow_ne_zero 2 (UpperHalfPlane.ne_zero z)
  · exact pow_ne_zero 2 (UpperHalfPlane.ne_zero z)
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

section rels_explicit

end rels_explicit
