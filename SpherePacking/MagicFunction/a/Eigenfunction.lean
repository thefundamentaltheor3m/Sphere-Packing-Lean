/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import SpherePacking.MagicFunction.a.Schwartz

open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap

open scoped FourierTransform

namespace MagicFunction.a.Fourier

section Integral_Permutations

theorem perm_I₁_I₂ : fourierTransformCLE ℝ (I₁ + I₂) = I₃ + I₄ := by sorry

theorem perm_I₅ : fourierTransformCLE ℝ (I₅) = I₆ := by sorry

-- Should use results from `RadialSchwartz.Radial` to prove the reverse.

theorem perm_₃_I₄ : fourierTransformCLE ℝ (I₃ + I₄) = I₁ + I₂ := by sorry

theorem perm_I₆ : fourierTransformCLE ℝ (I₆) = I₅ := by sorry

end Integral_Permutations

section Eigenfunction

theorem eig_a : fourierTransformCLE ℝ a = a := by
  rw [a_eq_sum_integrals_SchwartzIntegrals]
  have hrw : I₁ + I₂ + I₃ + I₄ + I₅ + I₆ = (I₁ + I₂) + (I₃ + I₄) + I₅ + I₆ := by ac_rfl
  rw [hrw, map_add, map_add, map_add, perm_I₁_I₂, perm_I₅, perm_₃_I₄, perm_I₆]
  ac_rfl

end Eigenfunction
