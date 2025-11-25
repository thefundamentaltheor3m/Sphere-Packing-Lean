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
  have h_symm' : (fourierTransformCLE ℂ).symm (fourierTransformCLE ℂ (J₁ + J₂))
      = (fourierTransformCLE ℂ).symm (-(J₃ + J₄)) :=
    congrArg ((fourierTransformCLE ℂ).symm) perm_J₁_J₂
  have hL : J₁ + J₂
      = (fourierTransformCLE ℂ).symm (-(J₃ + J₄)) := by
    simpa [ContinuousLinearEquiv.symm_apply_apply]
      using h_symm'
  have h_inv_eq₃ : (fourierTransformCLE ℂ).symm J₃ = fourierTransformCLE ℂ J₃ := by
    ext x
    have hfun : 𝓕⁻ (J₃ : EuclideanSpace ℝ (Fin 8) → ℂ)
        = 𝓕 (fun y : EuclideanSpace ℝ (Fin 8) => J₃ (-y)) :=
      Real.fourierIntegralInv_eq_fourierIntegral_comp_neg (J₃ : EuclideanSpace ℝ (Fin 8) → ℂ)
    have heven : (fun y : EuclideanSpace ℝ (Fin 8) => J₃ (-y))
        = (J₃ : EuclideanSpace ℝ (Fin 8) → ℂ) := by
      ext y; simp [J₃, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply]
    have hpoint := congrArg (fun f => f x) hfun
    simpa [fourierTransformCLE_symm_apply, fourierTransformCLE_apply, heven]
      using hpoint
  have h_inv_eq₄ : (fourierTransformCLE ℂ).symm J₄ = fourierTransformCLE ℂ J₄ := by
    ext x
    have hfun : 𝓕⁻ (J₄ : EuclideanSpace ℝ (Fin 8) → ℂ)
        = 𝓕 (fun y : EuclideanSpace ℝ (Fin 8) => J₄ (-y)) :=
      Real.fourierIntegralInv_eq_fourierIntegral_comp_neg (J₄ : EuclideanSpace ℝ (Fin 8) → ℂ)
    have heven : (fun y : EuclideanSpace ℝ (Fin 8) => J₄ (-y))
        = (J₄ : EuclideanSpace ℝ (Fin 8) → ℂ) := by
      ext y; simp [J₄, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply]
    have hpoint := congrArg (fun f => f x) hfun
    simpa [fourierTransformCLE_symm_apply, fourierTransformCLE_apply, heven]
      using hpoint
  have h_inv_eq : (fourierTransformCLE ℂ).symm (J₃ + J₄)
      = fourierTransformCLE ℂ (J₃ + J₄) := by
    simp [map_add, h_inv_eq₃, h_inv_eq₄]
  have hL'' : J₁ + J₂ = - (fourierTransformCLE ℂ).symm (J₃ + J₄) := by
    simpa [ContinuousLinearEquiv.map_neg] using hL
  have hL' : J₁ + J₂ = -fourierTransformCLE ℂ (J₃ + J₄) := by
    simpa [h_inv_eq] using hL''
  have hfinal : -(J₁ + J₂) = fourierTransformCLE ℂ (J₃ + J₄) := by
    simpa using congrArg Neg.neg hL'
  simpa [eq_comm] using hfinal

theorem perm_J₆ : fourierTransformCLE ℂ (J₆) = -J₅ := by
  have h_symm' : J₅ = (fourierTransformCLE ℂ).symm (-J₆) := by
    simpa [ContinuousLinearEquiv.symm_apply_apply]
      using congrArg ((fourierTransformCLE ℂ).symm) perm_J₅
  have h_symm : (fourierTransformCLE ℂ).symm J₆ = -J₅ := by
    have hneg := congrArg Neg.neg h_symm'
    simpa [map_neg] using hneg.symm
  have h_inv_eq : (fourierTransformCLE ℂ).symm J₆ = fourierTransformCLE ℂ J₆ := by
    ext x
    have hfun : 𝓕⁻ (J₆ : EuclideanSpace ℝ (Fin 8) → ℂ)
        = 𝓕 (fun y : EuclideanSpace ℝ (Fin 8) => J₆ (-y)) :=
      Real.fourierIntegralInv_eq_fourierIntegral_comp_neg (J₆ : EuclideanSpace ℝ (Fin 8) → ℂ)
    have heven : (fun y : EuclideanSpace ℝ (Fin 8) => J₆ (-y))
        = (J₆ : EuclideanSpace ℝ (Fin 8) → ℂ) := by
      ext y
      simp [J₆, schwartzMap_multidimensional_of_schwartzMap_real,
        compCLM_apply]
    have hpoint := congrArg (fun f => f x) hfun
    simpa [fourierTransformCLE_symm_apply, fourierTransformCLE_apply,
      heven] using hpoint
  simpa [h_inv_eq] using h_symm

end Integral_Permutations

section Eigenfunction

theorem eig_b : fourierTransformCLE ℂ b = -b := by
  rw [b_eq_sum_integrals_SchwartzIntegrals]
  have hrw : J₁ + J₂ + J₃ + J₄ + J₅ + J₆ = (J₁ + J₂) + (J₃ + J₄) + J₅ + J₆ := by ac_rfl
  rw [hrw, map_add, map_add, map_add, perm_J₁_J₂, perm_J₅, perm_₃_J₄, perm_J₆]
  abel

end Eigenfunction

end MagicFunction.b.Fourier
