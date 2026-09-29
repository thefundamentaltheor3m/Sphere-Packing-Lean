/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module


public import SpherePacking.MagicFunction.a.Schwartz

/-!
# The Fourier Eigenfunction Property of `a`

This file establishes that the function `a` is a `+1`-eigenfunction of the Fourier transform.
-/

@[expose] public section

open MagicFunction.a.RadialSchwartzIntegrals MagicFunction.FourierEigenfunctions RadialSchwartzMap

open scoped FourierTransform

namespace MagicFunction.a.Fourier

section Integral_Permutations

theorem perm_I₁_I₂ : 𝓕 (I₁ + I₂) = I₃ + I₄ := by sorry

theorem perm_I₅ : 𝓕 I₅ = I₆ := by sorry

theorem perm_I₃_I₄ : 𝓕 (I₃ + I₄) = I₁ + I₂ := by simp [← perm_I₁_I₂]

theorem perm_I₆ : 𝓕 I₆ = I₅ := by simp [← perm_I₅]

end Integral_Permutations

section Eigenfunction

theorem eig_a : 𝓕 a = a := calc
  _ = 𝓕 (I₁ + I₂ + I₃ + I₄ + I₅ + I₆) := by rw [a_eq_sum_RadialSchwartzIntegrals]
  _ = 𝓕 (I₁ + I₂) + 𝓕 (I₃ + I₄) + 𝓕 I₅ + 𝓕 I₆ := by simp only [FourierAdd.fourier_add]; ac_rfl
  _ = (I₃ + I₄) + (I₁ + I₂) + I₆ + I₅ := by rw [perm_I₁_I₂, perm_I₃_I₄, perm_I₅, perm_I₆]
  _ = _ := by rw [a_eq_sum_RadialSchwartzIntegrals]; ac_rfl

end Eigenfunction
end MagicFunction.a.Fourier
