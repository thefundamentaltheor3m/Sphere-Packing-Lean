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

local notation "ℍ₀" => upperHalfPlaneSet

local notation "Holo(" f ")" => DifferentiableOn ℂ f ℍ₀

local notation "MDiff(" f ")" => MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f ℍ₀

section Helpers

namespace UpperHalfPlane

theorem range_upperHalfPlane_coe : range UpperHalfPlane.coe = ℍ₀ := by
  ext z
  rw [mem_range]
  constructor <;> intro hz
  · obtain ⟨y, hy⟩ := hz
    rw [← hy]
    exact y.2
  · use ⟨z, hz⟩
    exact coe_mk_subtype hz

theorem zero_not_mem_upperHalfPlaneSet : (0 : ℂ) ∉ ℍ₀ := by simp

end UpperHalfPlane

end Helpers

namespace MagicFunction.a.ComplexIntegrands

variable {r : ℝ} (hr : r ≥ 0)
section Halfplane_API

end Halfplane_API

section Holo_Lemmas

/-! # Complex Differentiability -/

theorem φ₀''_holo : Holo(φ₀'') := by
  sorry

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

theorem Φ₁'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₁' r) ℍ₀ := Φ₁'_holo.contDiffOn isOpen_upperHalfPlaneSet

theorem Φ₂'_holo : Holo(Φ₂' r) := Φ₁'_holo

theorem Φ₂'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₂' r) ℍ₀ := Φ₁'_contDiffOn_ℂ

theorem Φ₃'_holo : Holo(Φ₃' r) := by
  refine DifferentiableOn.mul ?_ ((Complex.differentiable_exp.comp <| (differentiable_const _).mul
      differentiable_fun_id).differentiableOn)
  refine DifferentiableOn.mul ?_ <| (differentiable_fun_id.differentiableOn.sub_const 1).pow 2
  apply φ₀''_holo.comp
  · apply (differentiableOn_const (-1)).div
    · simp only [sub_eq_add_neg, differentiableOn_add_const_iff]
      exact differentiableOn_id
    · intro z hz hcontra
      obtain ⟨hre, him⟩ := Complex.ext_iff.mp hcontra
      simp only [sub_im, one_im, sub_zero, zero_im] at him
      have : z.im > 0 := hz
      linarith
  · let g : GL (Fin 2) ℝ := Units.mk (!![0, -1; 1, -1]) (!![-1, 1; -1, 0])
      (by simp [Matrix.one_fin_two]) (by simp [Matrix.one_fin_two])
    have : ∀ z ∈ ℍ₀, UpperHalfPlane.smulAux' g z = -1 / (z - 1) := fun _ _ ↦ by
      simp [smulAux', g, num, denom, σ, ← sub_eq_add_neg]
    refine MapsTo.congr ?_ this
    intro _ hz
    rw [mem_setOf_eq, smulAux'_im]
    exact div_pos (mul_pos (abs_pos.mpr g.det.ne_zero) hz) (normSq_denom_pos _ (ne_of_gt hz))

theorem Φ₃'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₃' r) ℍ₀ := Φ₃'_holo.contDiffOn isOpen_upperHalfPlaneSet

theorem Φ₄'_holo : Holo(Φ₄' r) := Φ₃'_holo

theorem Φ₄'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₄' r) ℍ₀ := Φ₃'_contDiffOn_ℂ

theorem Φ₅'_holo : Holo(Φ₅' r) := by
  refine DifferentiableOn.mul ?_ ((Complex.differentiable_exp.comp <| (differentiable_const _).mul
      differentiable_fun_id).differentiableOn)
  refine DifferentiableOn.mul ?_ <| differentiableOn_pow 2
  apply φ₀''_holo.comp
  · apply (differentiableOn_const (-1)).div differentiableOn_id
    intro _ hz
    exact ne_of_mem_of_not_mem hz <| zero_not_mem_upperHalfPlaneSet
  · let g : GL (Fin 2) ℝ := Units.mk (!![0, -1; 1, 0]) (!![0, 1; -1, 0])
      (by simp [Matrix.one_fin_two]) (by simp [Matrix.one_fin_two])
    have : ∀ z ∈ ℍ₀, UpperHalfPlane.smulAux' g z = -1 / z := fun _ _ ↦ by
      simp [smulAux', g, num, denom, σ, ← sub_eq_add_neg]
    refine MapsTo.congr ?_ this
    intro _ hz
    rw [mem_setOf_eq, smulAux'_im]
    exact div_pos (mul_pos (abs_pos.mpr g.det.ne_zero) hz) (normSq_denom_pos _ (ne_of_gt hz))

theorem Φ₅'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₅' r) ℍ₀ := Φ₅'_holo.contDiffOn isOpen_upperHalfPlaneSet

theorem Φ₆'_holo : Holo(Φ₆' r) := (φ₀''_holo.comp differentiableOn_id <| fun _ a ↦ a).mul
  (Complex.differentiable_exp.comp <| (differentiable_const _).mul
    differentiable_fun_id).differentiableOn

theorem Φ₆'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₆' r) ℍ₀ := Φ₆'_holo.contDiffOn isOpen_upperHalfPlaneSet

end Holo_Lemmas

section ContDiffOn_Real

/-! # Real Differentiability -/

theorem Φ₁'_contDiffOn : ContDiffOn ℝ ∞ (Φ₁' r) ℍ₀ := by sorry

theorem Φ₂'_contDiffOn : ContDiffOn ℝ ∞ (Φ₂' r) ℍ₀ := by sorry

theorem Φ₃'_contDiffOn : ContDiffOn ℝ ∞ (Φ₃' r) ℍ₀ := by sorry

theorem Φ₄'_contDiffOn : ContDiffOn ℝ ∞ (Φ₄' r) ℍ₀ := by sorry

theorem Φ₅'_contDiffOn : ContDiffOn ℝ ∞ (Φ₅' r) ℍ₀ := by sorry

theorem Φ₆'_contDiffOn : ContDiffOn ℝ ∞ (Φ₆' r) ℍ₀ := by sorry

end ContDiffOn_Real

end MagicFunction.a.ComplexIntegrands
