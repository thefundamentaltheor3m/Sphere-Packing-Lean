/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Raphael Appenzeller
-/

module
public import SpherePacking.ModularForms.JacobiTheta
public import SpherePacking.MagicFunction.IntegralParametrisations
import SpherePacking.ForMathlib.UpperHalfPlane

/-! # The ψ Functions

In this file, we define the functions `ψI`, `ψT` and `ψS` that are defined using the
Jacobi theta functions and are used in the definition of the -1-eigenfunction `b`.
-/

open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

noncomputable section matrices

/- The matrices `S` and `T` are given by `ModularGroup.S` and `ModularGroup.T`. -/

-- #check ModularGroup.S
-- #check ModularGroup.T

def ModularGroup.I : SL(2, ℤ) := ⟨!![1, 0; 0, 1], by decide⟩

end matrices

noncomputable section defs

/- We begin by defining the `h` function. The `ψ` functions are defined in terms of `h`
via slash actions. -/

/-- Auxiliary function used to define the `ψ`-functions. -/
@[expose] public def h : ℍ → ℂ := 128 • (H₃_MF + H₄_MF) / (H₂_MF ^ 2)

/-- The function `ψI`, defined from `h` and its slash transform by `S * T` (weight `-2`). -/
@[expose] public def ψI : ℍ → ℂ := h - h ∣[-2] (S * T)

/-- The function `ψT`, obtained from `ψI` by the slash action of `T` (weight `-2`). -/
@[expose] public def ψT : ℍ → ℂ := ψI ∣[-2] T

/-- The function `ψS`, obtained from `ψI` by the slash action of `S` (weight `-2`). -/
@[expose] public def ψS : ℍ → ℂ := ψI ∣[-2] S

/-- Extend `ψI` to a function on `ℂ`, defined as `0` outside the upper half-plane.

The prime in `ψI'` indicates this extension-to-`ℂ` convention. -/
@[expose] public def ψI' (z : ℂ) : ℂ := if hz : 0 < z.im then ψI ⟨z, hz⟩ else 0

/-- Extend `ψS` to a function on `ℂ`, defined as `0` outside the upper half-plane.

The prime in `ψS'` indicates this extension-to-`ℂ` convention. -/
@[expose] public def ψS' (z : ℂ) : ℂ := if hz : 0 < z.im then ψS ⟨z, hz⟩ else 0

/-- Extend `ψT` to a function on `ℂ`, defined as `0` outside the upper half-plane.

The prime in `ψT'` indicates this extension-to-`ℂ` convention. -/
@[expose] public def ψT' (z : ℂ) : ℂ := if hz : 0 < z.im then ψT ⟨z, hz⟩ else 0

end defs

section eq

/- It is possible to express ψI, ψT, ψS in terms of `H`-functions directly. -/

/- We first prove some auxiliary results. -/

section aux

lemma z_plus_one_nonzero (z : ℍ) : (z + 1 : ℂ) ≠ 0 := by
  intro hz
  exact (lt_irrefl (0 : ℝ)) (by simpa [hz] using (by simpa using z.2 : 0 < (z + 1 : ℂ).im))

lemma slashS (z : ℍ) (F : ℍ → ℂ) : (F ∣[(2 : ℤ)] (S)) (z) =
    F (S • z) * (z : ℂ) ^ (-2 : ℤ) := by simp [SL_slash_apply, S, denom]

/-- Slash-action formula for `S` in weight `-2`.

The prime in `slashS'` indicates the `k = -2` specialization (compare `slashS`). -/
public lemma slashS' (z : ℍ) (F : ℍ → ℂ) : (F ∣[(-2 : ℤ)] (S)) (z) =
    F (S • z) * (z : ℂ) ^ (2 : ℕ) := by
  rw [SL_slash_apply, S, denom]
  simp [sl_moeb, zpow_two, pow_two]

lemma slashS'' (z : ℍ) (F : ℍ → ℂ) : F (S • z) =
    (F ∣[(2 : ℤ)] (S)) (z) * (z : ℂ) ^ (2 : ℕ) := by
  simpa [mul_assoc, zpow_neg, zpow_two, pow_two, UpperHalfPlane.ne_zero z] using
    congrArg (fun w => w * (z : ℂ) ^ (2 : ℕ)) (slashS z F).symm

lemma slashT (z : ℍ) (F : ℍ → ℂ) : ((F) ∣[(2 : ℤ)] (T)) (z) = (F) (T • z) := by
  simp [SL_slash_apply, T, denom]

lemma slashT' (z : ℍ) (F : ℍ → ℂ) : ((F) ∣[(-2 : ℤ)] (T)) (z) =  (F) (T • z) := by
  simp [SL_slash_apply, T, denom]
 -- no need for slashT'', as ← slashT already fulfils that role

private lemma S_mul_T : S * T = ⟨!![0, -1; 1, 1], by norm_num [det_fin_two_of]⟩ := by
  ext (i : Fin 2) (j : Fin 2)
  fin_cases i <;> fin_cases j <;> simp [S, T]

-- the following statements will be applied of F = H₂, H₃, H₄ or (H₃+H₄)/H₂^2
lemma slashST (z : ℍ) (F : ℍ → ℂ) : ((F) ∣[(2 : ℤ)] (S * T)) (z) =
    F ((S * T) • z ) * (z + 1 : ℂ) ^ (-2 : ℤ) := by
  simp [SL_slash_apply, ModularGroup.S_mul_T, denom]

/-- Slash-action formula for `S * T` in weight `-2`.

The prime in `slashST'` indicates the `k = -2` specialization (compare `slashST`). -/
public lemma slashST' (z : ℍ) (F : ℍ → ℂ) : ((F) ∣[(-2 : ℤ)] (S * T)) (z) =
    F ((S * T) • z ) * (z + 1 : ℂ) ^ (2 : ℕ) := by
  rw [SL_slash_apply, ModularGroup.S_mul_T, denom]
  simp
  simp [zpow_two, pow_two]

lemma slashST'' (z : ℍ) (F : ℍ → ℂ) : F ((S * T) • z) =
    (F ∣[(2 : ℤ)] (S * T)) (z) * (z + 1 : ℂ) ^ 2 := by
  simpa [mul_assoc, zpow_neg, zpow_two, pow_two, z_plus_one_nonzero z] using
    congrArg (fun w => w * (z + 1 : ℂ) ^ (2 : ℕ)) (slashST z F).symm

end aux

/- We can now prove the main results of this section. Namely Lemma 7.16 in the blueprint -/

/-- Explicit formula for `ψI` in terms of the Jacobi theta functions `H₂`, `H₃`, and `H₄`. -/
public lemma ψI_eq :
    ψI = 128 • ((H₃_MF + H₄_MF) / (H₂_MF ^ 2) + (H₄_MF - H₂_MF) / H₃_MF ^ 2) := by
  rw [ψI, h]
  conv_rhs => rw [smul_add]
  conv_lhs => rw [sub_eq_add_neg, smul_div_assoc 128 (⇑H₃_MF + ⇑H₄_MF) (⇑H₂_MF ^ 2)]
  simp only [Int.reduceNeg, add_right_inj]
  ext z
  rw [Pi.neg_apply, slashST']
  have rewriting (z : ℍ) (F2 F3 F4 : ℍ → ℂ) : (128 • ((F3 + F4) / (F2 ^ 2))) ((S * T) • z) =
      128 • ((F3 ((S * T) • z) + F4 ((S * T) • z)) / ((F2 ((S * T) • z)) ^ 2)) := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat, sl_moeb, map_mul, Pi.div_apply, Pi.add_apply,
      Pi.mul_apply, Pi.ofNat_apply, Pi.pow_apply]
  rw [rewriting, slashST'' z ⇑H₂_MF, slashST'' z ⇑H₃_MF, slashST'' z ⇑H₄_MF]
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

/-- Explicit formula for `ψT` in terms of the Jacobi theta functions `H₂`, `H₃`, and `H₄`. -/
public lemma ψT_eq :
    ψT = 128 * ((H₃_MF + H₄_MF) / (H₂_MF ^ 2) + (H₂_MF + H₃_MF) / H₄_MF ^ 2) := by
  rw [ψT, ψI_eq]
  ext z
  rw [slashT']
  simp only [Pi.smul_apply, Pi.add_apply, Pi.div_apply, Pi.pow_apply, Pi.sub_apply, smul_add,
    nsmul_eq_mul, Nat.cast_ofNat, Pi.mul_apply, Pi.ofNat_apply]
  rw [← slashT z ⇑H₂_MF, ← slashT z ⇑H₃_MF, ← slashT z ⇑H₄_MF]
  rw [show (H₂_MF : ℍ → ℂ) = H₂ from rfl, show (H₃_MF : ℍ → ℂ) = H₃ from rfl,
    show (H₄_MF : ℍ → ℂ) = H₄ from rfl, H₂_T_action, H₃_T_action, H₄_T_action]
  simp [← mul_add, add_comm (H₄ z) (H₃ z), add_comm (H₃ z) (H₂ z)]
-- proof of ψT_eq complete.

-- there was a typo in the blueprint, thats why we first formalized the following version of ψS_eq
-- here is the description that can be found in Maryna's paper.
/-- A first explicit formula for `ψS` in terms of `H₂`, `H₃`, and `H₄`.

The prime in `ψS_eq'` indicates that this is a variant expression for `ψS` (used for comparison
with external references). -/
public lemma ψS_eq' :
    ψS = 128 * ((H₄_MF - H₂_MF) / (H₃_MF ^ 2) - (H₂_MF + H₃_MF) / H₄_MF ^ 2) := by
  rw [ψS, ψI_eq]
  ext z
  rw [slashS']
  simp only [Pi.smul_apply, Pi.add_apply, Pi.div_apply, Pi.pow_apply,
    Pi.sub_apply, smul_add, nsmul_eq_mul, Nat.cast_ofNat, Pi.mul_apply, Pi.ofNat_apply]
  rw [slashS'' z ⇑H₂_MF, slashS'' z ⇑H₃_MF, slashS'' z ⇑H₄_MF]
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

/-- A rearranged explicit formula for `ψS`, derived from `ψS_eq'`. -/
public lemma ψS_eq :
    ψS = 128 * (- ((H₂_MF + H₃_MF) / H₄_MF ^ 2) - (H₂_MF - H₄_MF) / (H₃_MF ^ 2)) := by
  rw [ψS_eq', sub_eq_add_neg (H₄_MF : ℍ → ℂ), add_comm (H₄_MF : ℍ → ℂ) _,
    ← sub_neg_eq_add, ← neg_sub', neg_div, ← neg_add', add_comm, neg_add']

/-- Decomposition of `ψI` as the sum `ψT + ψS`. -/
public lemma ψI_eq_add_ψT_ψS : ψI = ψT + ψS := by
  ext z
  simp [ψI_eq, ψT_eq, ψS_eq, sub_eq_add_neg]
  ring

end eq

section rels

/-- Modular relation: `ψT ∣[-2] T = ψI`. -/
public lemma ψT_slash_T : ψT ∣[-2] T = ψI := by
  ext z
  rw [ψT_eq, ψI_eq, slashT']
  simp only [Pi.mul_apply, Pi.ofNat_apply, Pi.add_apply, Pi.div_apply, Pi.pow_apply, Pi.smul_apply,
    Pi.sub_apply, smul_add, nsmul_eq_mul, Nat.cast_ofNat]
  rw [← slashT z ⇑H₂_MF, ← slashT z ⇑H₃_MF, ← slashT z ⇑H₄_MF]
  rw [show (H₂_MF : ℍ → ℂ) = H₂ from rfl, show (H₃_MF : ℍ → ℂ) = H₃ from rfl,
    show (H₄_MF : ℍ → ℂ) = H₄ from rfl, H₂_T_action, H₃_T_action, H₄_T_action]
  simp [← mul_add, add_comm (H₄ z) (H₃ z), add_comm  (- (H₂ z)) (H₄ z), sub_eq_add_neg]
-- proof of ψT_slash_T complete.

/-- Modular relation: `ψS ∣[-2] S = ψI`. -/
public lemma ψS_slash_S : ψS ∣[-2] S = ψI := by
  have hk : Even (-2 : ℤ) := ⟨-1, by ring⟩
  rw [ψS, ← slash_mul, ModularGroup.modular_S_sq]
  norm_num

/-- Modular relation: `ψS ∣[-2] (S * T) = ψT`. -/
public lemma ψS_slash_ST : ψS ∣[-2] (S * T) = ψT := by
  have hk : Even (-2 : ℤ) := ⟨-1, by ring⟩
  rw [ψS, ψT, ← slash_mul, ← mul_assoc, ModularGroup.modular_S_sq]
  simp [hk]


-- In my thesis, the - sign before ψS is missing. Makes no difference because we bound integrals in
-- absolute value, but point is that this way the Js look even more similar to the Is!
/-- Modular relation: `ψS ∣[-2] T = -ψS`. -/
public lemma ψS_slash_T : ψS ∣[-2] T = -ψS := by
  ext z
  rw [ψS_eq', slashT']
  simp only [Pi.mul_apply, Pi.add_apply, Pi.div_apply, Pi.pow_apply, Pi.sub_apply]
  rw [← slashT z ⇑H₂_MF, ← slashT z ⇑H₃_MF, ← slashT z ⇑H₄_MF]
  rw [show (H₂_MF : ℍ → ℂ) = H₂ from rfl, show (H₃_MF : ℍ → ℂ) = H₃ from rfl,
    show (H₄_MF : ℍ → ℂ) = H₄ from rfl, H₂_T_action, H₃_T_action, H₄_T_action]
  simp [sub_eq_add_neg, add_comm]
  ring
-- proof of ψS_slash_T complete

/-- Modular relation: `ψT ∣[-2] S = -ψT`. -/
public lemma ψT_slash_S : ψT ∣[-2] S = -ψT := by
  ext z
  rw [ψT_eq, slashS']
  simp only [Pi.mul_apply, Pi.ofNat_apply, Pi.add_apply, Pi.div_apply,
    Pi.pow_apply, Pi.neg_apply]
  rw [slashS'' z ⇑H₂_MF, slashS'' z ⇑H₃_MF, slashS'' z ⇑H₄_MF]
  rw [show (H₂_MF : ℍ → ℂ) = H₂ from rfl, show (H₃_MF : ℍ → ℂ) = H₃ from rfl,
    show (H₄_MF : ℍ → ℂ) = H₄ from rfl, H₂_S_action, H₃_S_action, H₄_S_action]
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

/-- Modular relation: `ψI ∣[-2] (T * S) = -ψT`. -/
public lemma ψI_slash_TS : ψI ∣[-2] (T * S) = -ψT := by
  ext z
  simpa [ψT, ← slash_mul] using congrArg (fun f => f z) (ψT_slash_S : ψT ∣[-2] S = -ψT)

/-- Modular relation: `ψS ∣[-2] (S * T * S) = -ψT`. -/
public lemma ψS_slash_STS : ψS ∣[-2] (S * T * S) = -ψT := by
  ext z
  rw [slash_mul, slash_mul, ψS_slash_S]
  simpa [ψT] using congrArg (fun f => f z) (ψT_slash_S : ψT ∣[-2] S = -ψT)

/-- Modular relation: `ψS ∣[-2] (T * S * T * S) = ψT`. -/
public lemma ψS_slash_TSTS : ψS ∣[-2] (T * S * T * S) = ψT := by
  ext z
  rw [slash_mul, slash_mul, slash_mul, ψS_slash_T, neg_slash, ψS_slash_S, neg_slash, ← ψT,
    neg_slash, ψT_slash_S]
  simp

end rels

open MagicFunction.Parametrisations Set

example {t : ℝ} (ht : t ∈ Ioc 0 1) : t ∈ Icc 0 1 := mem_Icc_of_Ioc ht

section eq_of_mem

lemma ψI'_eq_ψI_of_mem {z : ℂ} (hz : 0 < z.im) : ψI' z = ψI ⟨z, hz⟩ := by simp [ψI', hz]

lemma ψS'_eq_ψS_of_mem {z : ℂ} (hz : 0 < z.im) : ψS' z = ψS ⟨z, hz⟩ := by simp [ψS', hz]

lemma ψT'_eq_ψT_of_mem {z : ℂ} (hz : 0 < z.im) : ψT' z = ψT ⟨z, hz⟩ := by simp [ψT', hz]

lemma ψT'_comp_z₁'_eq_ψT_comp_z₁'_of_mem {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψT' (z₁' t) = ψT ⟨z₁' t, im_z₁'_pos ht⟩ :=
  ψT'_eq_ψT_of_mem (im_z₁'_pos ht)

lemma ψS'_comp_z₁'_eq_ψS_comp_z₁'_of_mem {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψS' (z₁' t) = ψS ⟨z₁' t, im_z₁'_pos ht⟩ :=
  ψS'_eq_ψS_of_mem (im_z₁'_pos ht)

lemma ψI'_comp_z₁'_eq_ψI_comp_z₁'_of_mem {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψI' (z₁' t) = ψI ⟨z₁' t, im_z₁'_pos ht⟩ :=
  ψI'_eq_ψI_of_mem (im_z₁'_pos ht)

lemma ψT'_comp_z₂'_eq_ψT_comp_z₂'_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) :
  ψT' (z₂' t) = ψT ⟨z₂' t, im_z₂'_pos ht⟩ :=
  ψT'_eq_ψT_of_mem (im_z₂'_pos ht)

lemma ψS'_comp_z₂'_eq_ψS_comp_z₂'_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) :
  ψS' (z₂' t) = ψS ⟨z₂' t, im_z₂'_pos ht⟩ :=
  ψS'_eq_ψS_of_mem (im_z₂'_pos ht)

lemma ψI'_comp_z₂'_eq_ψI_comp_z₂'_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) :
  ψI' (z₂' t) = ψI ⟨z₂' t, im_z₂'_pos ht⟩ :=
  ψI'_eq_ψI_of_mem (im_z₂'_pos ht)

lemma ψT'_comp_z₃'_eq_ψT_comp_z₃'_of_mem {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψT' (z₃' t) = ψT ⟨z₃' t, im_z₃'_pos ht⟩ :=
  ψT'_eq_ψT_of_mem (im_z₃'_pos ht)

lemma ψS'_comp_z₃'_eq_ψS_comp_z₃'_of_mem {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψS' (z₃' t) = ψS ⟨z₃' t, im_z₃'_pos ht⟩ :=
  ψS'_eq_ψS_of_mem (im_z₃'_pos ht)

lemma ψI'_comp_z₃'_eq_ψI_comp_z₃'_of_mem {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψI' (z₃' t) = ψI ⟨z₃' t, im_z₃'_pos ht⟩ :=
  ψI'_eq_ψI_of_mem (im_z₃'_pos ht)

lemma ψT'_comp_z₄'_eq_ψT_comp_z₄'_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) :
  ψT' (z₄' t) = ψT ⟨z₄' t, im_z₄'_pos ht⟩ :=
  ψT'_eq_ψT_of_mem (im_z₄'_pos ht)

lemma ψS'_comp_z₄'_eq_ψS_comp_z₄'_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) :
  ψS' (z₄' t) = ψS ⟨z₄' t, im_z₄'_pos ht⟩ :=
  ψS'_eq_ψS_of_mem (im_z₄'_pos ht)

lemma ψI'_comp_z₄'_eq_ψI_comp_z₄'_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) :
  ψI' (z₄' t) = ψI ⟨z₄' t, im_z₄'_pos ht⟩ :=
  ψI'_eq_ψI_of_mem (im_z₄'_pos ht)

lemma ψT'_comp_z₅'_eq_ψT_comp_z₅'_of_mem {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψT' (z₅' t) = ψT ⟨z₅' t, im_z₅'_pos ht⟩ :=
  ψT'_eq_ψT_of_mem (im_z₅'_pos ht)

lemma ψS'_comp_z₅'_eq_ψS_comp_z₅'_of_mem {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψS' (z₅' t) = ψS ⟨z₅' t, im_z₅'_pos ht⟩ :=
  ψS'_eq_ψS_of_mem (im_z₅'_pos ht)

lemma ψI'_comp_z₅'_eq_ψI_comp_z₅'_of_mem {t : ℝ} (ht : t ∈ Ioc 0 1) :
  ψI' (z₅' t) = ψI ⟨z₅' t, im_z₅'_pos ht⟩ :=
  ψI'_eq_ψI_of_mem (im_z₅'_pos ht)

lemma ψT'_comp_z₆'_eq_ψT_comp_z₆'_of_mem {t : ℝ} (ht : t ∈ Ici 1) :
  ψT' (z₆' t) = ψT ⟨z₆' t, im_z₆'_pos ht⟩ :=
  ψT'_eq_ψT_of_mem (im_z₆'_pos ht)

lemma ψS'_comp_z₆'_eq_ψS_comp_z₆'_of_mem {t : ℝ} (ht : t ∈ Ici 1) :
  ψS' (z₆' t) = ψS ⟨z₆' t, im_z₆'_pos ht⟩ :=
  ψS'_eq_ψS_of_mem (im_z₆'_pos ht)

lemma ψI'_comp_z₆'_eq_ψI_comp_z₆'_of_mem {t : ℝ} (ht : t ∈ Ici 1) :
  ψI' (z₆' t) = ψI ⟨z₆' t, im_z₆'_pos ht⟩ :=
  ψI'_eq_ψI_of_mem (im_z₆'_pos ht)

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

lemma ψS_slash_S_apply (z : ℍ) : (ψS ∣[-2] S) z = ψS ⟨-1 / z, neg_inv_mem z⟩ * z ^ 2 := by
  rw [SL_slash_apply ψS S z, ← neg_inv_eq_S z]
  congr 1
  rw [denom, ModularGroup.S_eq']
  simp only [Int.reduceNeg, Fin.isValue, SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom, map_apply,
    of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one, Int.cast_one, ofReal_one,
    one_mul, Int.cast_zero, ofReal_zero, add_zero, neg_neg]
  norm_cast

lemma ψS_slash_S_apply' (z : ℍ) : (ψS ∣[-2] S) z = ψS' (-1 / z) * z ^ 2 := by
  rw [ψS_slash_S_apply, ← ψS'_eq_ψS_of_mem]

end slash_explicit

section rels_explicit

lemma ψS_slash_ST_explicit₁ {t : ℝ} (ht : t ∈ Ioc 0 1) :
    ψT' (z₁' t) = ψS' (-1 / (z₁' t + 1)) * (z₁' t + 1) ^ 2 := by
  rw [ψT'_comp_z₁'_eq_ψT_comp_z₁'_of_mem ht, ← ψS_slash_ST, ψS_slash_ST_apply' _]

lemma ψS_slash_ST_explicit₂ {t : ℝ} (ht : t ∈ Icc 0 1) :
    ψT' (z₂' t) = ψS' (-1 / (z₂' t + 1)) * (z₂' t + 1) ^ 2 := by
  rw [ψT'_comp_z₂'_eq_ψT_comp_z₂'_of_mem ht, ← ψS_slash_ST, ψS_slash_ST_apply' _]

lemma ψS_slash_ST_explicit₃ {t : ℝ} (ht : t ∈ Ioc 0 1) :
    ψT' (z₃' t) = ψS' (-1 / (z₃' t + 1)) * (z₃' t + 1) ^ 2 := by
  rw [ψT'_comp_z₃'_eq_ψT_comp_z₃'_of_mem ht, ← ψS_slash_ST, ψS_slash_ST_apply' _]

lemma ψS_slash_ST_explicit₄ {t : ℝ} (ht : t ∈ Icc 0 1) :
    ψT' (z₄' t) = ψS' (-1 / (z₄' t + 1)) * (z₄' t + 1) ^ 2 := by
  rw [ψT'_comp_z₄'_eq_ψT_comp_z₄'_of_mem ht, ← ψS_slash_ST, ψS_slash_ST_apply' _]

lemma ψS_slash_S_explicit₅ {t : ℝ} (ht : t ∈ Ioc 0 1) :
    ψI' (z₅' t) = ψS' (-1 / z₅' t) * (z₅' t) ^ 2 := by
  rw [ψI'_comp_z₅'_eq_ψI_comp_z₅'_of_mem ht, ← ψS_slash_S, ψS_slash_S_apply' _]

lemma ψS_slash_ST_explicit₆ {t : ℝ} (ht : t ∈ Ici 1) :
  ψT' (z₆' t) = ψS' (-1 / (z₆' t + 1)) * (z₆' t + 1) ^ 2 := by
  rw [ψT'_comp_z₆'_eq_ψT_comp_z₆'_of_mem ht, ← ψS_slash_ST, ψS_slash_ST_apply' _]

end rels_explicit
