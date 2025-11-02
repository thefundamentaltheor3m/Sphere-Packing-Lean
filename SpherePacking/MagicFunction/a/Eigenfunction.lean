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

theorem perm_I₁_I₂ : fourierTransformCLE ℂ (I₁ + I₂) = I₃ + I₄ := by sorry

theorem perm_I₅ : fourierTransformCLE ℂ (I₅) = I₆ := by sorry

-- Should use results from `RadialSchwartz.Radial` to prove the reverse.

theorem perm_₃_I₄ : fourierTransformCLE ℂ (I₃ + I₄) = I₁ + I₂ := by sorry

theorem perm_I₆ : fourierTransformCLE ℂ (I₆) = I₅ :=
by
  calc
    fourierTransformCLE ℂ I₆
        = (SchwartzMap.fourierTransformCLE ℂ).symm I₆ := by
          ext x
          have h := congrArg (fun f => f x)
            (Real.fourierIntegralInv_eq_fourierIntegral_comp_neg
              (I₆ : EuclideanSpace ℝ (Fin 8) → ℂ))
          simpa [SchwartzMap.fourierTransformCLE_symm_apply,
            SchwartzMap.fourierTransformCLE_apply, I₆,
            schwartzMap_multidimensional_of_schwartzMap_real,
            SchwartzMap.compCLM_apply] using h.symm
    _ = I₅ := by
          simpa [ContinuousLinearEquiv.symm_apply_apply] using
            (congrArg ((SchwartzMap.fourierTransformCLE ℂ).symm) perm_I₅).symm

end Integral_Permutations

section Eigenfunction

theorem eig_a : fourierTransformCLE ℂ a = a := by
  rw [a_eq_sum_integrals_SchwartzIntegrals]
  have hrw : I₁ + I₂ + I₃ + I₄ + I₅ + I₆ = (I₁ + I₂) + (I₃ + I₄) + I₅ + I₆ := by ac_rfl
  rw [hrw, map_add, map_add, map_add, perm_I₁_I₂, perm_I₅, perm_₃_I₄, perm_I₆]
  ac_rfl

end Eigenfunction
end MagicFunction.a.Fourier
