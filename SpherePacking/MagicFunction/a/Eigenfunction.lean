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

lemma fourier_involution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : 𝓢(V, E)) :
    fourierTransformCLE ℂ (fourierTransformCLE ℂ f) = fun x => f (-x) :=
by
  ext x; change 𝓕 (𝓕 f) x = f (-x)
  simpa [Real.fourierInv_eq_fourier_neg, neg_neg] using
    congrArg (fun g : V → E => g (-x))
      (f.continuous.fourierInv_fourier_eq f.integrable ((fourierTransformCLE ℂ) f).integrable)

lemma radial_inversion {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : 𝓢(V, E)) (hf : Function.Even f) :
    fourierTransformCLE ℂ (fourierTransformCLE ℂ f) = f :=
by
  ext x; simpa [hf x] using congrArg (fun g => g x) (fourier_involution (V:=V) (E:=E) f)

theorem perm_I₁_I₂ : fourierTransformCLE ℂ (I₁ + I₂) = I₃ + I₄ := by sorry

theorem perm_I₅ : fourierTransformCLE ℂ (I₅) = I₆ := by sorry

-- Should use results from `RadialSchwartz.Radial` to prove the reverse.

theorem perm_₃_I₄ : fourierTransformCLE ℂ (I₃ + I₄) = I₁ + I₂ := by
  exact perm_I₁_I₂ ▸
    radial_inversion (I₁ + I₂) (fun _ => by
      simp [I₁, I₂, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply])

-- should use fourier_involution and the radial symmetry of I₅
theorem perm_I₆ : fourierTransformCLE ℂ (I₆) = I₅ :=
by
  simpa [← perm_I₅] using
    radial_inversion I₅ (fun _ => by
      simp [I₅, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply])

end Integral_Permutations

section Eigenfunction

theorem eig_a : fourierTransformCLE ℂ a = a := by
  rw [a_eq_sum_integrals_SchwartzIntegrals]
  have hrw : I₁ + I₂ + I₃ + I₄ + I₅ + I₆ = (I₁ + I₂) + (I₃ + I₄) + I₅ + I₆ := by ac_rfl
  rw [hrw, map_add, map_add, map_add, perm_I₁_I₂, perm_I₅, perm_₃_I₄, perm_I₆]
  ac_rfl

end Eigenfunction
end MagicFunction.a.Fourier
