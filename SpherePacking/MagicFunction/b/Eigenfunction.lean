/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module


public import SpherePacking.MagicFunction.b.Schwartz

@[expose] public section

open MagicFunction.b.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap

open scoped FourierTransform

namespace MagicFunction.b.Fourier

section Integral_Permutations

theorem perm_J₁_J₂ : (FourierTransform.fourierCLE ℂ _) (J₁ + J₂) = -(J₃ + J₄) := by sorry

theorem perm_J₅ : (FourierTransform.fourierCLE ℂ _) (J₅) = -J₆ := by sorry

-- Should use results from `RadialSchwartz.Radial` and linearity to prove the reverse.

theorem perm_₃_J₄ : (FourierTransform.fourierCLE ℂ _) (J₃ + J₄) = -(J₁ + J₂) := by
  have h₁ : (FourierTransform.fourierCLE ℂ _) ((FourierTransform.fourierCLE ℂ _) J₁) = J₁ := by
    ext x
    simpa [J₁, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply,
      Real.fourierInv_eq_fourier_neg] using
        congrArg (· (-x)) (J₁.continuous.fourierInv_fourier_eq J₁.integrable
          ((FourierTransform.fourierCLE ℂ _) J₁).integrable)
  have h₂ : (FourierTransform.fourierCLE ℂ _) ((FourierTransform.fourierCLE ℂ _) J₂) = J₂ := by
    ext x
    simpa [J₂, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply,
      Real.fourierInv_eq_fourier_neg] using
        congrArg (· (-x)) (J₂.continuous.fourierInv_fourier_eq J₂.integrable
          ((FourierTransform.fourierCLE ℂ _) J₂).integrable)
  simpa only [neg_add_rev, add_comm, map_add, map_neg, neg_neg, h₁, h₂] using
    congrArg (-(FourierTransform.fourierCLE ℂ _) ·) perm_J₁_J₂ |>.symm

theorem perm_J₆ : (FourierTransform.fourierCLE ℂ _) (J₆) = -J₅ := by
  have h : ((FourierTransform.fourierCLE ℂ _)).symm J₆ = (FourierTransform.fourierCLE ℂ _) J₆ := by
    ext x
    simp only [FourierTransform.fourierCLE_symm_apply, FourierTransform.fourierCLE_apply,
      fourier_coe, fourierInv_coe, Real.fourierInv_eq_fourier_comp_neg]
    suffices (fun x ↦ J₆ (-x)) = ⇑J₆ by exact congr(𝓕 $this x)
    ext
    simp [J₆, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply]
  have := (congrArg ((FourierTransform.fourierCLE ℂ _)).symm perm_J₅).symm
  simp only [map_neg, ContinuousLinearEquiv.symm_apply_apply, ← h] at this ⊢
  rw [← this, neg_neg]

end Integral_Permutations

section Eigenfunction

theorem eig_b : (FourierTransform.fourierCLE ℂ _) b = -b := by
  rw [b_eq_sum_integrals_SchwartzIntegrals]
  have hrw : J₁ + J₂ + J₃ + J₄ + J₅ + J₆ = (J₁ + J₂) + (J₃ + J₄) + J₅ + J₆ := by ac_rfl
  rw [hrw, map_add, map_add, map_add, perm_J₁_J₂, perm_J₅, perm_₃_J₄, perm_J₆]
  abel

end Eigenfunction

end MagicFunction.b.Fourier
