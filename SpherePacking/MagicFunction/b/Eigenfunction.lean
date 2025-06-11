/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LJCENSE.
Authors: Sidharth Hariharan
-/

import SpherePacking.MagicFunction.b.Schwartz

open MagicFunction.b.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap

open scoped FourierTransform

namespace MagicFunction.b.Fourier

section Integral_Permutations

theorem perm_J₁_J₂ : fourierTransformCLE ℝ (J₁ + J₂) = -(J₃ + J₄) := by sorry

theorem perm_J₅ : fourierTransformCLE ℝ (J₅) = -J₆ := by sorry

-- Should use results from `RadialSchwartz.Radial` and linearity to prove the reverse.

theorem perm_₃_J₄ : fourierTransformCLE ℝ (J₃ + J₄) = -(J₁ + J₂) := by sorry

theorem perm_J₆ : fourierTransformCLE ℝ (J₆) = -J₅ := by sorry

end Integral_Permutations

section Eigenfunction

theorem eig_b : fourierTransformCLE ℝ b = -b := by
  rw [b_eq_sum_integrals_SchwartzIntegrals]
  have hrw : J₁ + J₂ + J₃ + J₄ + J₅ + J₆ = (J₁ + J₂) + (J₃ + J₄) + J₅ + J₆ := by ac_rfl
  rw [hrw, map_add, map_add, map_add, perm_J₁_J₂, perm_J₅, perm_₃_J₄, perm_J₆]
  abel

end Eigenfunction
