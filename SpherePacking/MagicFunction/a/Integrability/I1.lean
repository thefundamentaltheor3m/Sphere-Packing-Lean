/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import SpherePacking.MagicFunction.a.IntegralEstimates.I1
import SpherePacking.MagicFunction.a.Holomorphicity.I1

/-! # Integrability

In this file, we prove that the integrand of `I₁` is integrable.

I'm no quite sure what the best way is to prove intgerability. One way is to prove that `g` is
`AEStronglyMeasurable` and then use `IntegralEstimates` to prove `HasFiniteIntegral`. Unfortunately,
maybe the most direct way to prove `AEStronglyMeasurable` is via holomorphicity, but the way we want
to prove holomorphicity is to differentiate under the integral sign, which requires integrability.

One possible approach is to show that the _double intgeral_ exists. 
-/

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound MagicFunction.a.IntegralEstimates.I₁
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open scoped Function UpperHalfPlane

namespace MagicFunction.a.Integrability

theorem I₁'_g {r : ℝ} (hr : r ≥ 0) : IntegrableOn (fun t ↦ ‖g r t‖) (Ici (1 : ℝ)) volume := by
  sorry

theorem I₁_orig {r : ℝ} (hr : r ≥ 0) : IntegrableOn (fun t ↦
    I * φ₀'' (-1 / ((z₁' t) + (1 : ℂ))) * ((z₁' t) + (1 : ℂ)) ^ 2 * cexp (π * I * r * (z₁' t)))
    (Ioc (0 : ℝ) 1) volume := by
  sorry

end MagicFunction.a.Integrability
