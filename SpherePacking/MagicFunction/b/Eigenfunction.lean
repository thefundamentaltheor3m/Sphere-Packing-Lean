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

lemma fourier_involution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (f : 𝓢(V, E)) :
    (FourierTransform.fourierCLE ℂ _) ((FourierTransform.fourierCLE ℂ _) f) = fun x => f (-x) :=
by
  ext x; change 𝓕 (𝓕 ⇑f) x = f (-x)
  simpa [Real.fourierInv_eq_fourier_neg, neg_neg] using
    congrArg (fun g : V → E => g (-x))
      (f.continuous.fourierInv_fourier_eq
        f.integrable ((FourierTransform.fourierCLE ℂ _) f).integrable)

lemma radial_inversion {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (f : 𝓢(V, E))
    (hf : Function.Even f) :
    (FourierTransform.fourierCLE ℂ _) ((FourierTransform.fourierCLE ℂ _) f) = f :=
by
  ext x; simpa [hf x] using congrArg (fun g => g x) (fourier_involution (V:=V) (E:=E) f)

theorem perm_J₁_J₂ : (FourierTransform.fourierCLE ℂ _) (J₁ + J₂) = -(J₃ + J₄) := by sorry

theorem perm_J₅ : (FourierTransform.fourierCLE ℂ _) (J₅) = -J₆ := by sorry

-- Should use results from `RadialSchwartz.Radial` and linearity to prove the reverse.

theorem perm_₃_J₄ : (FourierTransform.fourierCLE ℂ _) (J₃ + J₄) = -(J₁ + J₂) := by
  have h₁ : (FourierTransform.fourierCLE ℂ _) ((FourierTransform.fourierCLE ℂ _) J₁) = J₁ := by
    exact radial_inversion J₁ (fun _ => by
      simp [J₁, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply])
  have h₂ : (FourierTransform.fourierCLE ℂ _) ((FourierTransform.fourierCLE ℂ _) J₂) = J₂ := by
    exact radial_inversion J₂ (fun _ => by
      simp [J₂, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply])
  simpa only [neg_add_rev, add_comm, map_add, map_neg, neg_neg, h₁, h₂] using
    congrArg (-(FourierTransform.fourierCLE ℂ _) ·) perm_J₁_J₂ |>.symm

theorem perm_J₆ : (FourierTransform.fourierCLE ℂ _) (J₆) = -J₅ := by
  let F := FourierTransform.fourierCLE ℂ 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)
  have h : F.symm J₆ = F J₆ := by
    ext x
    simp only [F, FourierTransform.fourierCLE_symm_apply, FourierTransform.fourierCLE_apply,
      fourier_coe, fourierInv_coe, Real.fourierInv_eq_fourier_comp_neg]
    suffices (fun x ↦ J₆ (-x)) = ⇑J₆ by exact congr(𝓕 $this x)
    ext
    simp [J₆, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply]
  have := (congrArg F.symm perm_J₅).symm
  simp only [F, map_neg, ContinuousLinearEquiv.symm_apply_apply, ← h] at this ⊢
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
