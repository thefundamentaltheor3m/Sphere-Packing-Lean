/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Raphael Appenzeller, Seewoo Lee
-/
module

public import SpherePacking.ModularForms.FG
public import SpherePacking.ModularForms.JacobiTheta.MDifferentiable
public import SpherePacking.MagicFunction.IntegralParametrisations

/-!
# The ψ Functions

In this file, we define the functions `ψI`, `ψT` and `ψS` that are defined using the
Jacobi theta functions and are used in the definition of the -1-eigenfunction `b`.
-/

@[expose] public section

open UpperHalfPlane hiding I
open Complex Real Matrix ModularGroup ModularForm SlashAction MatrixGroups

noncomputable section defs

/-- The auxiliary function `h = 128 (H₃ + H₄) / H₂ ^ 2`, from which the `ψ` functions are obtained
via slash actions. -/
def h : ℍ → ℂ := 128 • (H₃ + H₄) / (H₂ ^ 2)

/-- `ψI = h - h ∣[-2] (S * T)`. -/
def ψI : ℍ → ℂ := h - h ∣[-2] (S * T)

/-- `ψT = ψI ∣[-2] T`. -/
def ψT : ℍ → ℂ := ψI ∣[-2] T

/-- `ψS = ψI ∣[-2] S`. -/
def ψS : ℍ → ℂ := ψI ∣[-2] S

/-- `ψI`, extended by zero to a function on `ℂ`. -/
def ψI' (z : ℂ) : ℂ := if hz : 0 < z.im then ψI ⟨z, hz⟩ else 0

/-- `ψS`, extended by zero to a function on `ℂ`. -/
def ψS' (z : ℂ) : ℂ := if hz : 0 < z.im then ψS ⟨z, hz⟩ else 0

/-- `ψT`, extended by zero to a function on `ℂ`. -/
def ψT' (z : ℂ) : ℂ := if hz : 0 < z.im then ψT ⟨z, hz⟩ else 0

lemma ψI'_def {z : ℂ} (hz : 0 < z.im) : ψI' z = ψI ⟨z, hz⟩ := by simp [ψI', hz]
lemma ψS'_def {z : ℂ} (hz : 0 < z.im) : ψS' z = ψS ⟨z, hz⟩ := by simp [ψS', hz]
lemma ψT'_def {z : ℂ} (hz : 0 < z.im) : ψT' z = ψT ⟨z, hz⟩ := by simp [ψT', hz]

end defs

section eq

/- We express `ψI`, `ψT`, `ψS` in terms of the `H`-functions directly (Lemma 7.16 in the blueprint).
The proofs distribute the slash action over `•`, `+`, `-`, `/` and `^ 2` at the level of functions,
so that only the `S`- and `T`-actions on `H₂`, `H₃`, `H₄` remain; the resulting identity of
functions is then checked pointwise by `ring`. -/

/-- The weight `-2` slash action of a quotient `F / G ^ 2` of two weight `2` functions, with the
weight in the form `simp` can match. -/
private lemma div_sq_slash (γ : SL(2, ℤ)) (F G : ℍ → ℂ) :
    (F / G ^ 2) ∣[(-2 : ℤ)] γ = F ∣[(2 : ℤ)] γ / (G ∣[(2 : ℤ)] γ) ^ 2 := by
  rw [show (-2 : ℤ) = 2 - (2 : ℕ) * 2 by norm_num, div_slash_SL2, pow_slash_SL2]

lemma ψI_eq : ψI = 128 • ((H₃ + H₄) / (H₂ ^ 2) + (H₄ - H₂) / H₃ ^ 2) := by
  rw [ψI, h]
  simp only [div_sq_slash, SL_smul_slash, add_slash, slash_mul, neg_slash, neg_neg, H₂_S_action,
    H₃_S_action, H₄_S_action, H₂_T_action, H₃_T_action, H₄_T_action]
  ext z
  simp only [Pi.smul_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply,
    Pi.neg_apply, Pi.ofNat_apply, nsmul_eq_mul, Nat.cast_ofNat]
  ring

lemma ψT_eq : ψT = 128 * ((H₃ + H₄) / (H₂ ^ 2) + (H₂ + H₃) / H₄ ^ 2) := by
  rw [ψT, ψI_eq]
  simp only [SL_smul_slash, add_slash, sub_slash, div_sq_slash, H₂_T_action, H₃_T_action,
    H₄_T_action]
  ext z
  simp only [Pi.smul_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply,
    Pi.neg_apply, Pi.ofNat_apply, nsmul_eq_mul, Nat.cast_ofNat]
  ring

lemma ψS_eq : ψS = 128 * ((H₄ - H₂) / (H₃ ^ 2) - (H₂ + H₃) / H₄ ^ 2) := by
  rw [ψS, ψI_eq]
  simp only [SL_smul_slash, add_slash, sub_slash, div_sq_slash, H₂_S_action, H₃_S_action,
    H₄_S_action]
  ext z
  simp only [Pi.smul_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply,
    Pi.neg_apply, Pi.ofNat_apply, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- `ψS` in terms of the weight-10 form `G` and the discriminant: `ψS = -G / (2Δ)`.
This follows from `ψS_eq`, the Jacobi identity `H₂ + H₄ = H₃`, and `Δ = (H₂H₃H₄)² / 256`. -/
theorem ψS_eq_neg_one_half_smul_G_div_disc : ψS = (-1 / 2 : ℂ) • G / Δ := by
  ext z
  have hΔ := Δ_eq_H₂_H₃_H₄ z
  obtain ⟨⟨h₂, h₃⟩, h₄⟩ : (H₂ z ≠ 0 ∧ H₃ z ≠ 0) ∧ H₄ z ≠ 0 := by
    simpa [hΔ, not_or] using ModularForm.discriminant_ne_zero z
  have hJ : H₃ z = H₂ z + H₄ z := (congrFun jacobi_identity z).symm
  rw [hJ] at h₃ hΔ
  rw [ψS_eq, G_eq]
  simp only [Pi.mul_apply, Pi.ofNat_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, hJ, hΔ]
  field

end eq

section rels

lemma ψS_slash_S : ψS ∣[-2] S = ψI := by
  rw [ψS, ← slash_mul, modular_S_sq, slash_neg' _ _ (by decide), slash_one]

lemma ψS_slash_ST : ψS ∣[-2] (S * T) = ψT := by
  rw [slash_mul, ψS_slash_S, ψT]

lemma ψT_slash_T : ψT ∣[-2] T = ψI := by
  rw [ψT, ← slash_mul, ψI_eq]
  simp only [SL_smul_slash, add_slash, sub_slash, div_sq_slash, slash_mul, neg_slash, neg_neg,
    H₂_T_action, H₃_T_action, H₄_T_action]

-- In my thesis, the - sign before ψS is missing. Makes no difference because we bound integrals in
-- absolute value, but point is that this way the Js look even more similar to the Is!
lemma ψS_slash_T : ψS ∣[-2] T = -ψS := by
  rw [ψS, ← slash_mul, ψI_eq]
  simp only [SL_smul_slash, add_slash, sub_slash, div_sq_slash, slash_mul, neg_slash, neg_neg,
    H₂_S_action, H₃_S_action, H₄_S_action, H₂_T_action, H₃_T_action, H₄_T_action]
  ext z
  simp only [Pi.smul_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply,
    Pi.neg_apply, Pi.ofNat_apply, nsmul_eq_mul, Nat.cast_ofNat]
  ring

lemma ψT_slash_S : ψT ∣[-2] S = -ψT := by
  rw [ψT, ← slash_mul, ψI_eq]
  simp only [SL_smul_slash, add_slash, sub_slash, div_sq_slash, slash_mul, neg_slash, neg_neg,
    H₂_S_action, H₃_S_action, H₄_S_action, H₂_T_action, H₃_T_action, H₄_T_action]
  ext z
  simp only [Pi.smul_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply,
    Pi.neg_apply, Pi.ofNat_apply, nsmul_eq_mul, Nat.cast_ofNat]
  ring

lemma ψI_slash_TS : ψI ∣[-2] (T * S) = -ψT := by
  rw [slash_mul, ← ψT, ψT_slash_S]

lemma ψS_slash_STS : ψS ∣[-2] (S * T * S) = -ψT := by
  rw [slash_mul, ψS_slash_ST, ψT_slash_S]

lemma ψS_slash_TSTS : ψS ∣[-2] (T * S * T * S) = ψT := by
  rw [slash_mul, slash_mul, slash_mul, ψS_slash_T, neg_slash, ψS_slash_S, neg_slash, ← ψT,
    neg_slash, ψT_slash_S, neg_neg]

end rels

open MagicFunction.Parametrisations Set

section eq_of_mem

lemma ψI'_eq_ψI_of_mem {z : ℂ} (hz : 0 < z.im) : ψI' z = ψI ⟨z, hz⟩ := by simp [ψI', hz]

lemma ψS'_eq_ψS_of_mem {z : ℂ} (hz : 0 < z.im) : ψS' z = ψS ⟨z, hz⟩ := by simp [ψS', hz]

lemma ψT'_eq_ψT_of_mem {z : ℂ} (hz : 0 < z.im) : ψT' z = ψT ⟨z, hz⟩ := by simp [ψT', hz]

end eq_of_mem

section slash_explicit

lemma ψS_slash_ST_apply (z : ℍ) : (ψS ∣[-2] (S * T)) z = ψS' (-1 / (z + 1)) * (z + 1) ^ 2 := by
  rw [SL_slash_apply ψS (S * T) z, ← neg_inv_one_add_eq_ST z, ← ψS'_eq_ψS_of_mem]
  congr 1
  rw [denom]
  simp [SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two]

lemma ψS_slash_S_apply (z : ℍ) : (ψS ∣[-2] S) z = ψS' (-1 / z) * z ^ 2 := by
  rw [SL_slash_apply ψS S z, ← neg_inv_eq_S z, ← ψS'_eq_ψS_of_mem]
  congr 1
  rw [denom]
  simp [SpecialLinearGroup.map_apply_coe]

/-- `ψT` in terms of `ψS`, on `ℂ`: `ψT z = ψS (-1 / (z + 1)) (z + 1) ^ 2` for `z ∈ ℍ`. -/
lemma ψS_slash_ST_explicit {z : ℂ} (hz : 0 < z.im) :
    ψT' z = ψS' (-1 / (z + 1)) * (z + 1) ^ 2 := by
  rw [ψT'_eq_ψT_of_mem hz, ← ψS_slash_ST, ψS_slash_ST_apply]

/-- `ψI` in terms of `ψS`, on `ℂ`: `ψI z = ψS (-1 / z) z ^ 2` for `z ∈ ℍ`. -/
lemma ψS_slash_S_explicit {z : ℂ} (hz : 0 < z.im) : ψI' z = ψS' (-1 / z) * z ^ 2 := by
  rw [ψI'_eq_ψI_of_mem hz, ← ψS_slash_S, ψS_slash_S_apply]

end slash_explicit

section rels_explicit

/- The instances of the two previous lemmas along the contours `zᵢ'` used to define `b`. -/

lemma ψS_slash_ST_explicit₁ {t : ℝ} (ht : t ∈ Ioc 0 1) :
    ψT' (z₁' t) = ψS' (-1 / (z₁' t + 1)) * (z₁' t + 1) ^ 2 :=
  ψS_slash_ST_explicit (im_z₁'_pos ht)

lemma ψS_slash_ST_explicit₂ {t : ℝ} (ht : t ∈ Icc 0 1) :
    ψT' (z₂' t) = ψS' (-1 / (z₂' t + 1)) * (z₂' t + 1) ^ 2 :=
  ψS_slash_ST_explicit (im_z₂'_pos ht)

lemma ψS_slash_ST_explicit₃ {t : ℝ} (ht : t ∈ Ioc 0 1) :
    ψT' (z₃' t) = ψS' (-1 / (z₃' t + 1)) * (z₃' t + 1) ^ 2 :=
  ψS_slash_ST_explicit (im_z₃'_pos ht)

lemma ψS_slash_ST_explicit₄ {t : ℝ} (ht : t ∈ Icc 0 1) :
    ψT' (z₄' t) = ψS' (-1 / (z₄' t + 1)) * (z₄' t + 1) ^ 2 :=
  ψS_slash_ST_explicit (im_z₄'_pos ht)

lemma ψS_slash_S_explicit₅ {t : ℝ} (ht : t ∈ Ioc 0 1) :
    ψI' (z₅' t) = ψS' (-1 / z₅' t) * (z₅' t) ^ 2 :=
  ψS_slash_S_explicit (im_z₅'_pos ht)

end rels_explicit
