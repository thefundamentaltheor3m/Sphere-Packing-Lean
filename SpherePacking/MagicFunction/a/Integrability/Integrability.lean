/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.a.Integrability.RealIntegrands

/-!
# Integrability

In this file, we prove that the integrands `Φⱼ` are integrable.
-/

@[expose] public section

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound MagicFunction.a.RealIntegrands
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open scoped Function UpperHalfPlane

namespace MagicFunction.a.Integrability

theorem Φ₁_integrableOn {s : ℝ} (hs : s ≥ 0) : IntegrableOn (Φ₁ s)
    (Ioc (0 : ℝ) 1) volume := by
  refine ⟨ContinuousOn.aestronglyMeasurable Φ₁_contDiffOn.continuousOn measurableSet_Ioc, ?_⟩
  sorry

theorem Φ₂_integrableOn {s : ℝ} (hs : s ≥ 0) : IntegrableOn (Φ₂ s)
    (Icc (0 : ℝ) 1) volume := by
  refine ⟨ContinuousOn.aestronglyMeasurable Φ₂_contDiffOn.continuousOn measurableSet_Icc, ?_⟩
  sorry

theorem Φ₃_integrableOn {s : ℝ} (hs : s ≥ 0) : IntegrableOn (Φ₃ s)
    (Ioc (0 : ℝ) 1) volume := by
  refine ⟨ContinuousOn.aestronglyMeasurable Φ₃_contDiffOn.continuousOn measurableSet_Ioc, ?_⟩
  sorry

theorem Φ₄_integrableOn {s : ℝ} (hs : s ≥ 0) : IntegrableOn (Φ₄ s)
    (Icc (0 : ℝ) 1) volume := by
  refine ⟨ContinuousOn.aestronglyMeasurable Φ₄_contDiffOn.continuousOn measurableSet_Icc, ?_⟩
  sorry

theorem Φ₅_integrableOn {s : ℝ} (hs : s ≥ 0) : IntegrableOn (Φ₅ s)
    (Ioc (0 : ℝ) 1) volume := by
  refine ⟨ContinuousOn.aestronglyMeasurable Φ₅_contDiffOn.continuousOn measurableSet_Ioc, ?_⟩
  sorry

theorem Φ₆_integrableOn {s : ℝ} (hs : s ≥ 0) : IntegrableOn (Φ₆ s)
    (Ici (1 : ℝ)) volume := by
  refine ⟨ContinuousOn.aestronglyMeasurable Φ₆_contDiffOn.continuousOn measurableSet_Ici, ?_⟩
  sorry

end MagicFunction.a.Integrability
