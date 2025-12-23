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

section Holo

/-! # Complex Differentiability -/

theorem Φ₁'_holo : Holo(Φ₁' r) := by
  sorry

theorem Φ₁'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₁' r) ℍ₀ :=
  (Φ₁'_holo hr).contDiffOn isOpen_upperHalfPlaneSet

end Holo

section ContDiffOn_Real

/-! # Real Differentiability -/

noncomputable example (n : ℕ) : ContinuousMultilinearMap (ι := Fin n) ℂ (fun i ↦ ℂ) ℂ → ContinuousMultilinearMap (ι := Fin n) ℝ (fun i ↦ ℂ) ℂ :=
  -- fun p ↦ FormalMultilinearSeries.ofScalars ℂ <| Complex.re ∘ p
  fun f ↦
  by
  sorry

lemma Real_differentiable_of_Complex_differentiable (f : ℂ → ℂ) : Differentiable ℂ f → Differentiable ℝ f := by
  simp only [Differentiable.eq_def]
  intro h x
  specialize h x
  obtain ⟨f', hf'⟩ := h
  have : ∃ k : ℂ, f'.toFun = (fun z ↦ k • z) := by
    sorry
  obtain ⟨k, hk⟩ := this
  let f'_re : ℂ →L[ℝ] ℂ := sorry
  sorry

lemma Real_contDiff_of_Complex_contDiff (f : ℂ → ℂ) : ContDiff ℂ ∞ f → ContDiff ℝ ∞ f := by
  intro h
  simp only [ContDiff.eq_def] at h ⊢
  obtain ⟨p, hp⟩ := h
  sorry

theorem Φ₁'_contDiffOn : ContDiffOn ℝ ∞ (Φ₁' r) ℍ₀ := by
  sorry

end ContDiffOn_Real

section MDiff

end MDiff

end MagicFunction.a.ComplexIntegrands
