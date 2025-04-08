/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

import Mathlib

import SpherePacking.ForMathlib.RadialSchwartz

import SpherePacking.MagicFunction.a.IntegralEstimates.I1

/-! # `a` is a Schwartz Function

The purpose of this file is to prove that `a` is a Schwartz function. We follow the proof of
Proposition 7.8 in the blueprint.
-/

open MagicFunction MagicFunction.a MagicFunction.a.RadialFunctions MagicFunction.a.RealIntegrals
  MagicFunction.a.Parametrisations

open Set Complex Real SchwartzMap

namespace MagicFunction.a.SchwartzProperties

section Smooth

/-! # `a` is smooth.

There is no reference for this in the blueprint. The idea is to use integrability to differentiate
inside the integrals.
-/

theorem I₁'_smooth' : ContDiff ℝ (@WithTop.some ℕ∞ ⊤) MagicFunction.a.RealIntegrals.I₁' := by
  sorry

theorem I₂'_smooth' : ContDiff ℝ (@WithTop.some ℕ∞ ⊤) MagicFunction.a.RealIntegrals.I₂' := by
  sorry

theorem I₃'_smooth' : ContDiff ℝ (@WithTop.some ℕ∞ ⊤) MagicFunction.a.RealIntegrals.I₃' := by
  sorry

theorem I₄'_smooth' : ContDiff ℝ (@WithTop.some ℕ∞ ⊤) MagicFunction.a.RealIntegrals.I₄' := by
  sorry

theorem smooth' :  ContDiff ℝ (@WithTop.some ℕ∞ ⊤) MagicFunction.a.RealIntegrals.a' :=
  ((I₁'_smooth'.add I₂'_smooth').add I₃'_smooth').add I₄'_smooth'

end Smooth

section Decay

/-! # `a` decays faster than any inverse power of the norm squared.

We follow the proof of Proposition 7.8 in the blueprint.
-/

theorem I₁'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
  ‖x‖ ^ k * ‖iteratedFDeriv ℝ n MagicFunction.a.RealIntegrals.I₁' x‖ ≤ C := by
  sorry

theorem I₂'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
  ‖x‖ ^ k * ‖iteratedFDeriv ℝ n MagicFunction.a.RealIntegrals.I₂' x‖ ≤ C := by
  sorry

theorem I₃'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
  ‖x‖ ^ k * ‖iteratedFDeriv ℝ n MagicFunction.a.RealIntegrals.I₃' x‖ ≤ C := by
  sorry

theorem I₄'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
  ‖x‖ ^ k * ‖iteratedFDeriv ℝ n MagicFunction.a.RealIntegrals.I₄' x‖ ≤ C := by
  sorry

theorem decay' :  ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n MagicFunction.a.RealIntegrals.a' x‖ ≤ C := by
  intro k n
  obtain ⟨C₁, h₁⟩ := I₁'_decay' k n
  obtain ⟨C₂, h₂⟩ := I₂'_decay' k n
  obtain ⟨C₃, h₃⟩ := I₃'_decay' k n
  obtain ⟨C₄, h₄⟩ := I₄'_decay' k n
  use C₁ + C₂ + C₃ + C₄
  intro x
  specialize h₁ x
  specialize h₂ x
  specialize h₃ x
  specialize h₄ x
  have hdiff₁ : ContDiff ℝ n I₁' := (contDiff_iff_forall_nat_le.mp I₁'_smooth') n le_top
  have hdiff₂ : ContDiff ℝ n I₂' := (contDiff_iff_forall_nat_le.mp I₂'_smooth') n le_top
  have hdiff₃ : ContDiff ℝ n I₃' := (contDiff_iff_forall_nat_le.mp I₃'_smooth') n le_top
  have hdiff₄ : ContDiff ℝ n I₄' := (contDiff_iff_forall_nat_le.mp I₄'_smooth') n le_top
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n a' x‖
  _ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (I₁' + I₂' + I₃' + I₄') x‖ := rfl
  _ = ‖x‖ ^ k * ‖(iteratedFDeriv ℝ n (I₁' + I₂' + I₃') x) + (iteratedFDeriv ℝ n I₄' x)‖ := by
    congr
    exact iteratedFDeriv_add_apply ((hdiff₁.add hdiff₂).add hdiff₃) hdiff₄
  _ ≤ ‖x‖ ^ k * (‖iteratedFDeriv ℝ n (I₁' + I₂' + I₃') x‖ + ‖iteratedFDeriv ℝ n I₄' x‖) := by
    gcongr
    exact ContinuousMultilinearMap.opNorm_add_le (iteratedFDeriv ℝ n (I₁' + I₂' + I₃') x)
        (iteratedFDeriv ℝ n I₄' x)
  _ ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (I₁' + I₂' + I₃') x‖ + C₄ := by
    rw [mul_add]
    gcongr
  _ = ‖x‖ ^ k * ‖(iteratedFDeriv ℝ n (I₁' + I₂') x) + (iteratedFDeriv ℝ n I₃' x)‖ + C₄ := by
    congr
    exact iteratedFDeriv_add_apply (hdiff₁.add hdiff₂) hdiff₃
  _ ≤ ‖x‖ ^ k * (‖iteratedFDeriv ℝ n (I₁' + I₂') x‖ + ‖iteratedFDeriv ℝ n I₃' x‖) + C₄ := by
    gcongr
    exact ContinuousMultilinearMap.opNorm_add_le (iteratedFDeriv ℝ n (I₁' + I₂') x)
        (iteratedFDeriv ℝ n I₃' x)
  _ ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (I₁' + I₂') x‖ + C₃ + C₄ := by
    rw [mul_add]
    gcongr
  _ = ‖x‖ ^ k * ‖(iteratedFDeriv ℝ n I₁' x) + (iteratedFDeriv ℝ n I₂' x)‖ + C₃ + C₄ := by
    congr
    exact iteratedFDeriv_add_apply hdiff₁ hdiff₂
  _ ≤ ‖x‖ ^ k * (‖iteratedFDeriv ℝ n I₁' x‖ + ‖iteratedFDeriv ℝ n I₂' x‖) + C₃ + C₄ := by
    gcongr
    exact ContinuousMultilinearMap.opNorm_add_le (iteratedFDeriv ℝ n I₁' x)
        (iteratedFDeriv ℝ n I₂' x)
  _ ≤ C₁ + C₂ + C₃ + C₄ := by
    rw [mul_add]
    gcongr

end Decay

end MagicFunction.a.SchwartzProperties

noncomputable section SchwartzMap

namespace MagicFunction

/-- The radial component of the +1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[simps!]
def a' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.a.RealIntegrals.a'
  smooth' := MagicFunction.a.SchwartzProperties.smooth'
  decay' := MagicFunction.a.SchwartzProperties.decay'

/-- The +1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[simps!]
def a : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) := schwartzMap_multidimensional_of_schwartzMap_real
  (EuclideanSpace ℝ (Fin 8)) a'

end MagicFunction

end SchwartzMap
