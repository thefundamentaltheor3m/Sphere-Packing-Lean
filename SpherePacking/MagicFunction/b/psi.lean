/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import Mathlib

import SpherePacking.ModularForms.JacobiTheta
import SpherePacking.Tactic.NormNumI

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

noncomputable section eq

/- It is possible to express ψI, ψT, ψS in terms of `H`-functions directly. -/

/- We first prove some auxiliary results. -/

section aux

private lemma slash_aux (z : ℍ) : (z ^ 2 : ℂ) = (z ^ (-2 : ℤ)) / ((z ^ (-2 : ℤ)) ^ 2) := by
  have h₁ : 0 < (z : ℂ).im := z.2
  have h₂ : (z : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ext_iff]
    push_neg
    exact fun _ ↦ ne_of_gt h₁
  symm; calc
  _ = ((z : ℂ) ^ (-2 : ℤ)) / (z ^ (-4 : ℤ)) := by
      congr 1
      simp only [Int.reduceNeg, _root_.zpow_neg, inv_pow, _root_.inv_inj]
      change ((z : ℂ) ^ 2) ^ 2 = z ^ (2 * 2)
      exact (pow_mul (z : ℂ) 2 2).symm
  _ = _ := by
      conv_rhs => change (z : ℂ) ^ ((-2 : ℤ) - (-4))
      sorry

end aux

/- We can now prove the main results of this section. -/

lemma ψI_eq : ψI = 128 • ((H₃_MF + H₄_MF) / (H₂_MF ^ 2) + (H₄_MF - H₂_MF) / H₃_MF ^ 2) := by
  rw [ψI, h]
  conv_rhs => rw [smul_add]
  conv_lhs => rw [sub_eq_add_neg, smul_div_assoc 128 (⇑H₃_MF + ⇑H₄_MF) (⇑H₂_MF ^ 2)]
  simp only [nsmul_eq_mul, Nat.cast_ofNat, Int.reduceNeg, add_right_inj]
  calc
  _ = -(128 : ℍ → ℂ) * (H₃_MF + H₄_MF) / (H₂_MF ^ 2) := sorry
  _ = _ := sorry

lemma ψS_eq : ψS = 128 * ((H₃_MF + H₄_MF) / (H₂_MF ^ 2) + (H₂_MF + H₃_MF) / H₄_MF ^ 2) := by
  sorry

lemma ψT_eq : ψT = 128 * ((H₄_MF - H₂_MF) / (H₃_MF ^ 2) - (H₂_MF + H₃_MF) / H₄_MF ^ 2 + (H₂_MF + H₃_MF) / H₄_MF ^ 2) := by
  sorry

end eq
