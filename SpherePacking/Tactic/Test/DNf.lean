/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import SpherePacking.Tactic.DNf
public import SpherePacking.ModularForms.RamanujanIdentities

/-!
# Tests for the `d_nf` tactic
-/

@[expose] public section

open UpperHalfPlane hiding I

-- Linearity of `D`, with `MDiff` side conditions discharged by `fun_prop`
example : D (E₄.toFun + E₆.toFun) = D E₄.toFun + D E₆.toFun := by d_nf
example : D ((3 : ℂ) • E₄.toFun) = (3 : ℂ) • D E₄.toFun := by d_nf
example : D (E₄.toFun - E₆.toFun) = D E₄.toFun - D E₆.toFun := by d_nf

-- Leibniz rule plus the Ramanujan base derivatives
example : D (E₄.toFun * E₆.toFun) =
    3⁻¹ * (E₂ * E₄.toFun - E₆.toFun) * E₆.toFun +
      E₄.toFun * (2⁻¹ * (E₂ * E₆.toFun - E₄.toFun * E₄.toFun)) := by d_nf

-- `serre_D` unfolds to `D`-level and weights recombine arithmetically
example : serre_D 10 E₄.toFun = D E₄.toFun - 5 * 6⁻¹ * E₂ * E₄.toFun := by d_nf

-- Squares and cubes
example : D (E₄.toFun ^ 2) = 2 * E₄.toFun * D E₄.toFun := by
  d_nf

-- Extra simp lemmas: unfold a local definition
noncomputable def twoE₄ : ℍ → ℂ := (2 : ℂ) • E₄.toFun

example : D twoE₄ = (2 : ℂ) • D E₄.toFun := by d_nf [twoE₄]
