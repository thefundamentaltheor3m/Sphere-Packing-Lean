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

namespace MagicFunction.b.psi

noncomputable section matrices

def S_Matrix : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]
def T_Matrix : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]
def I_Matrix : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 1]

def S : SL(2, ℤ) := ⟨S_Matrix, by decide⟩
def T : SL(2, ℤ) := ⟨T_Matrix, by decide⟩
def I : SL(2, ℤ) := ⟨I_Matrix, by decide⟩

end matrices

noncomputable section defs

/- We begin by defining the `h` function. The `ψ` functions are defined in terms of `h`
via slash actions. -/

def h : ℍ → ℂ := 128 * (H₃_MF + H₄_MF) / (H₂_MF ^ 2)

def ψI : ℍ → ℂ := h - h ∣[-2] (S * T)
def ψT : ℍ → ℂ := ψI ∣[-2] T
def ψS : ℍ → ℂ := ψI ∣[-2] S

end defs

noncomputable section eq

/- It is possible to express ψI, ψT, ψS in terms of `H`-functions directly. -/

lemma ψI_eq : ψI = 128 * ((H₃_MF + H₄_MF) / (H₂_MF ^ 2) + (H₄_MF - H₂_MF) / H₃_MF ^ 2) := by
  sorry

end eq
