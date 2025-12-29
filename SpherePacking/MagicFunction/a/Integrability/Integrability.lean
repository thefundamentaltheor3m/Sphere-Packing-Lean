/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import SpherePacking.MagicFunction.a.IntegralEstimates.I1
import SpherePacking.MagicFunction.a.IntegralEstimates.I2
import SpherePacking.MagicFunction.a.IntegralEstimates.I3
import SpherePacking.MagicFunction.a.IntegralEstimates.I4
import SpherePacking.MagicFunction.a.IntegralEstimates.I5
import SpherePacking.MagicFunction.a.IntegralEstimates.I6
import SpherePacking.MagicFunction.a.Integrability.RealIntegrands

/-! # Integrability

In this file, we prove that the integrands `Φᵢ` are integrable.
-/

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound MagicFunction.a.RealIntegrands
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open scoped Function UpperHalfPlane

namespace MagicFunction.a.Integrability

theorem Φ₁_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₁ r)
    (Ioc (0 : ℝ) 1) volume := by
  refine ⟨ContinuousOn.aestronglyMeasurable Φ₁_contDiffOn.continuousOn measurableSet_Ioc, ?_⟩
  sorry

theorem Φ₂_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₂ r)
    (Icc (0 : ℝ) 1) volume := by
  refine ⟨ContinuousOn.aestronglyMeasurable Φ₂_contDiffOn.continuousOn measurableSet_Icc, ?_⟩
  sorry

theorem Φ₃_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₃ r)
    (Ioc (0 : ℝ) 1) volume := by
  refine ⟨ContinuousOn.aestronglyMeasurable Φ₃_contDiffOn.continuousOn measurableSet_Ioc, ?_⟩
  sorry

theorem Φ₄_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₄ r)
    (Icc (0 : ℝ) 1) volume := by
  refine ⟨ContinuousOn.aestronglyMeasurable Φ₄_contDiffOn.continuousOn measurableSet_Icc, ?_⟩
  sorry

theorem Φ₅_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₅ r)
    (Ioc (0 : ℝ) 1) volume := by
  refine ⟨ContinuousOn.aestronglyMeasurable Φ₅_contDiffOn.continuousOn measurableSet_Ioc, ?_⟩
  sorry

theorem Φ₆_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₆ r)
    (Ici (1 : ℝ)) volume := by
  refine ⟨ContinuousOn.aestronglyMeasurable Φ₆_contDiffOn.continuousOn measurableSet_Ici, ?_⟩
  sorry

end MagicFunction.a.Integrability
