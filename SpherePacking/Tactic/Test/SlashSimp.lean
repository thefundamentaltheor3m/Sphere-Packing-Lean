/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import SpherePacking.Tactic.SlashSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Tests for the `slash_simp` tactic
-/

@[expose] public section

open UpperHalfPlane ModularForm ModularGroup
open scoped MatrixGroups

section unfolding

-- Slash by `T` has trivial denominator
example (f : ℍ → ℂ) (k : ℤ) (z : ℍ) : (f ∣[k] T) z = f (T • z) := by slash_simp

-- Slash by `S`: denominator is `z` and gets cleared by `field_simp`
example (f : ℍ → ℂ) (z : ℍ) (h : (f ∣[(4 : ℤ)] S) z = f z) :
    f (S • z) = (z : ℂ) ^ (4 : ℕ) * f z := by
  slash_simp at h
  linear_combination h

end unfolding

section ne_zero

example (γ : SL(2, ℤ)) (z : ℍ) : denom γ z ≠ 0 := by slash_ne_zero
example (z : ℍ) : (z : ℂ) ≠ 0 := by slash_ne_zero
example : (Real.pi : ℂ) ≠ 0 := by slash_ne_zero
example (z : ℍ) : Real.pi * Complex.I * z ≠ 0 := by slash_ne_zero
example (γ : SL(2, ℤ)) (z : ℍ) (k : ℕ) : denom γ z ^ k ≠ 0 := by slash_ne_zero

end ne_zero
