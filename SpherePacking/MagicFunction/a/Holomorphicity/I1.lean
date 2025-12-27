/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import SpherePacking.MagicFunction.a.IntegralEstimates.I1

import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-! # Φ₁' : ℂ → ℂ is Holomorphic on the Upper Half-Plane

In this file, we prove that the integrand of `I₁` is holomorphic on the upper half-plane. This
relies on the properties of φ₀ that it inherits from the modular forms in terms of which it is
defined.
-/

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound MagicFunction.a.IntegralEstimates.I₁
  MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands

open Complex Real Set Filter intervalIntegral ContDiff UpperHalfPlane

open scoped Function Manifold

namespace MagicFunction.a.ComplexIntegrands

variable {r : ℝ} (hr : r ≥ 0)

include hr

local notation "ℍ₀" => upperHalfPlaneSet

local notation "Holo(" f ")" => DifferentiableOn ℂ f ℍ₀

local notation "MDiff(" f ")" => MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f ℍ₀

section Halfplane_API

end Halfplane_API

section Holo_Lemmas

/-! # Complex Differentiability -/

omit hr in
theorem φ₀''_holo : Holo(φ₀'') := by
  sorry

omit hr in
theorem Φ₁'_holo : Holo(Φ₁' r) := by
  refine DifferentiableOn.mul ?_ ((Complex.differentiable_exp.comp <| (differentiable_const _).mul
      differentiable_fun_id).differentiableOn)
  refine DifferentiableOn.mul ?_ <| (differentiable_fun_id.differentiableOn.add_const 1).pow 2
  apply φ₀''_holo.comp
  · apply (differentiableOn_const (-1)).div
    · rw [differentiableOn_add_const_iff]
      exact differentiableOn_id
    · intro z hz hcontra
      obtain ⟨hre, him⟩ := Complex.ext_iff.mp hcontra
      simp only [add_im, one_im, add_zero, zero_im] at him
      have : z.im > 0 := hz
      linarith
  · let g : GL (Fin 2) ℝ := Units.mk (!![0, -1; 1, 1]) (!![1, 1; -1, 0])
      (by simp [Matrix.one_fin_two]) (by simp [Matrix.one_fin_two])
    have : ∀ z ∈ ℍ₀, UpperHalfPlane.smulAux' g z = -1 / (z + 1) := fun _ _ ↦ by
      simp [smulAux', g, num, denom, σ]
    refine MapsTo.congr ?_ this
    intro _ hz
    rw [mem_setOf_eq, smulAux'_im]
    exact div_pos (mul_pos (abs_pos.mpr g.det.ne_zero) hz) (normSq_denom_pos _ (ne_of_gt hz))

omit hr in
theorem Φ₁'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₁' r) ℍ₀ := Φ₁'_holo.contDiffOn isOpen_upperHalfPlaneSet

end Holo_Lemmas

section ContDiffOn_Real

/-! # Real Differentiability -/

theorem Φ₁'_contDiffOn : ContDiffOn ℝ ∞ (Φ₁' r) ℍ₀ := by
  sorry

end ContDiffOn_Real

section MDiff_Lemmas

end MDiff_Lemmas

end MagicFunction.a.ComplexIntegrands
