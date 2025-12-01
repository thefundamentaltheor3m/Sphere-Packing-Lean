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

theorem perm_J₁_J₂ : fourierTransformCLE ℂ (J₁ + J₂) = -(J₃ + J₄) := by sorry

theorem perm_J₅ : fourierTransformCLE ℂ (J₅) = -J₆ := by sorry

-- Should use results from `RadialSchwartz.Radial` and linearity to prove the reverse.

theorem perm_₃_J₄ : fourierTransformCLE ℂ (J₃ + J₄) = -(J₁ + J₂) := by
  have h₁ : fourierTransformCLE ℂ (fourierTransformCLE ℂ J₁) = J₁ := by
    ext x
    simpa [J₁, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply,
      Real.fourierIntegralInv_eq_fourierIntegral_neg] using
        congrArg (· (-x)) (J₁.continuous.fourier_inversion J₁.integrable
          (fourierTransformCLE ℂ J₁).integrable)
  have h₂ : fourierTransformCLE ℂ (fourierTransformCLE ℂ J₂) = J₂ := by
    ext x
    simpa [J₂, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply,
      Real.fourierIntegralInv_eq_fourierIntegral_neg] using
        congrArg (· (-x)) (J₂.continuous.fourier_inversion J₂.integrable
          (fourierTransformCLE ℂ J₂).integrable)
  simpa [map_add, map_neg, h₁, h₂, add_comm] using
    congrArg (-fourierTransformCLE ℂ ·) perm_J₁_J₂ |>.symm

theorem perm_J₆ : fourierTransformCLE ℂ (J₆) = -J₅ := by
  have h : (fourierTransformCLE ℂ).symm J₆ = fourierTransformCLE ℂ J₆ := by
    ext; simp [fourierTransformCLE_symm_apply, fourierTransformCLE_apply,
      Real.fourierIntegralInv_eq_fourierIntegral_comp_neg]
    congr 1; ext; simp [J₆, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply]
  simpa [← h, neg_eq_iff_eq_neg] using (congrArg (fourierTransformCLE ℂ).symm perm_J₅).symm

end Integral_Permutations

section Eigenfunction

theorem eig_b : fourierTransformCLE ℂ b = -b := by
  rw [b_eq_sum_integrals_SchwartzIntegrals]
  have hrw : J₁ + J₂ + J₃ + J₄ + J₅ + J₆ = (J₁ + J₂) + (J₃ + J₄) + J₅ + J₆ := by ac_rfl
  rw [hrw, map_add, map_add, map_add, perm_J₁_J₂, perm_J₅, perm_₃_J₄, perm_J₆]
  abel

end Eigenfunction

end MagicFunction.b.Fourier
