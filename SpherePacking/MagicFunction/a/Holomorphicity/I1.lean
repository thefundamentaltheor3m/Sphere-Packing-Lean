/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import SpherePacking.MagicFunction.a.IntegralEstimates.I1

/-! # Φ₁' : ℂ → ℂ is Holomorphic on the Upper Half-Plane

In this file, we prove that the integrand of `I₁` is holomorphic on the upper half-plane.

The proof we have in mind involves differentiating under the integral sign..
-/

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound MagicFunction.a.IntegralEstimates.I₁
  MagicFunction.a.ComplexIntegrands
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open scoped Function UpperHalfPlane

namespace MagicFunction.a.Holomorphicity

variable {r : ℝ} (hr : r ≥ 0)



end MagicFunction.a.Holomorphicity
