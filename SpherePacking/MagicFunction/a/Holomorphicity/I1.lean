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

open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral

open scoped Function UpperHalfPlane Manifold

namespace MagicFunction.a.ComplexIntegrands

variable {r : ℝ} (hr : r ≥ 0)

local notation "Holo" => MDifferentiable 𝓘(ℂ) 𝓘(ℂ)

theorem Φ₁_Holo : Holo (Φ₁' r) := by
  sorry

end MagicFunction.a.ComplexIntegrands
