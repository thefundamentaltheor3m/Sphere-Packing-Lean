/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module


public import SpherePacking.MagicFunction.b.Schwartz

/-!
# The Fourier Eigenfunction Property of `b`

This file establishes that the function `b` is a `-1`-eigenfunction of the Fourier transform.
-/

@[expose] public section

open MagicFunction.b.RadialSchwartzIntegrals MagicFunction.FourierEigenfunctions RadialSchwartzMap

open scoped FourierTransform

namespace MagicFunction.b.Fourier

section Integral_Permutations

theorem perm_J₁_J₂ : 𝓕 (J₁ + J₂) = -(J₃ + J₄) := by sorry

theorem perm_J₅ : 𝓕 J₅ = -J₆ := by sorry

theorem perm_J₃_J₄ : 𝓕 (J₃ + J₄) = -(J₁ + J₂) := by
  rw [← neg_neg (J₃ + J₄), ← perm_J₁_J₂, FourierTransform.fourier_neg, fourier_apply_apply]

theorem perm_J₆ : 𝓕 J₆ = -J₅ := by
  rw [← neg_neg J₆, ← perm_J₅, FourierTransform.fourier_neg, fourier_apply_apply]

end Integral_Permutations

section Eigenfunction

theorem eig_b : 𝓕 b = -b := calc
  _ = 𝓕 (J₁ + J₂ + J₃ + J₄ + J₅ + J₆) := by rw [b_eq_sum_RadialSchwartzIntegrals]
  _ = 𝓕 (J₁ + J₂) + 𝓕 (J₃ + J₄) + 𝓕 J₅ + 𝓕 J₆ := by simp only [FourierAdd.fourier_add]; ac_rfl
  _ = -(J₃ + J₄) + -(J₁ + J₂) + -J₆ + -J₅ := by
      rw [perm_J₁_J₂, perm_J₃_J₄, perm_J₅, perm_J₆]
  _ = _ := by rw [b_eq_sum_RadialSchwartzIntegrals]; abel

end Eigenfunction

end MagicFunction.b.Fourier
