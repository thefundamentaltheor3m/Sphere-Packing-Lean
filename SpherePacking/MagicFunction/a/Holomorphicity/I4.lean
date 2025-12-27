/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import SpherePacking.MagicFunction.a.IntegralEstimates.I4

import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-! # Φ₄' : ℂ → ℂ is Holomorphic on the Upper Half-Plane

In this file, we prove that the integrand of `I₄` is holomorphic on the upper half-plane. This
relies on the properties of φ₀ that it inherits from the modular forms in terms of which it is
defined.
-/

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound MagicFunction.a.IntegralEstimates.I₄
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

theorem Φ₄'_holo : Holo(Φ₄' r) := by
  sorry

end Holo

section ContDiffOn

/-! # Real Differentiability -/

theorem Φ₄'_contDiffOn : ContDiffOn ℝ ∞ (Φ₄' r) ℍ₀ := by

  sorry

end ContDiffOn

section MDiff

end MDiff

end MagicFunction.a.ComplexIntegrands
