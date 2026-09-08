/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module


public import SpherePacking.MagicFunction.a.IntegralEstimates.I1
public import SpherePacking.MagicFunction.a.IntegralEstimates.I2
public import SpherePacking.MagicFunction.a.IntegralEstimates.I3
public import SpherePacking.MagicFunction.a.IntegralEstimates.I4
public import SpherePacking.MagicFunction.a.IntegralEstimates.I5
public import SpherePacking.MagicFunction.a.IntegralEstimates.I6
public import SpherePacking.MagicFunction.a.Integrability.RealIntegrands
public import SpherePacking.MagicFunction.a.IntegralEstimates.Majorants

/-!
# Integrability

In this file, we prove that the integrands `Φⱼ` are integrable on their respective segments.

The proofs are organised by contour class, using the shared estimates from
`MagicFunction.a.IntegralEstimates.Majorants`:

* the cusp-touching segments `Φ₁`, `Φ₃`, `Φ₅` on `(0, 1]` are uniformly bounded, since the
  super-exponential decay `exp (-2π/t)` at the cusp swallows the quadratic factor;
* the compact top-edge segments `Φ₂`, `Φ₄` on `[0, 1]` are continuous on a compact set;
* the vertical tail `Φ₆` on `[1, ∞)` is dominated by `C₀ * exp (-2πt) * exp (-πrt)`.
-/

@[expose] public section

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound MagicFunction.a.RealIntegrands MagicFunction.a.Majorants
  MagicFunction.a.ComplexIntegrands
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open scoped Function UpperHalfPlane

namespace MagicFunction.a.Integrability

/-! ### Cusp-touching segments -/

/-- `Φ₁` is integrable on `(0, 1]`: it is uniformly bounded there by `norm_Φ₁_le`. -/
theorem Φ₁_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₁ r) (Ioc (0 : ℝ) 1) volume := by
  obtain ⟨_, _, hb⟩ := norm_Φ₁_le hr
  exact integrableOn_of_norm_le_const measurableSet_Ioc measure_Ioc_lt_top.ne
    Φ₁_contDiffOn.continuousOn hb

/-- `Φ₃` is integrable on `(0, 1]`: it is uniformly bounded there by `norm_Φ₃_le`. -/
theorem Φ₃_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₃ r) (Ioc (0 : ℝ) 1) volume := by
  obtain ⟨_, _, hb⟩ := norm_Φ₃_le hr
  exact integrableOn_of_norm_le_const measurableSet_Ioc measure_Ioc_lt_top.ne
    Φ₃_contDiffOn.continuousOn hb

/-- `Φ₅` is integrable on `(0, 1]`: it is uniformly bounded there by `norm_Φ₅_le`. -/
theorem Φ₅_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₅ r) (Ioc (0 : ℝ) 1) volume := by
  obtain ⟨_, _, hb⟩ := norm_Φ₅_le hr
  exact integrableOn_of_norm_le_const measurableSet_Ioc measure_Ioc_lt_top.ne
    Φ₅_contDiffOn.continuousOn hb

/-! ### Compact top-edge segments -/

/-- `Φ₂` is integrable on `[0, 1]`: it is continuous on a compact set. -/
theorem Φ₂_integrableOn {r : ℝ} (_hr : r ≥ 0) : IntegrableOn (Φ₂ r)
    (Icc (0 : ℝ) 1) volume :=
  Φ₂_contDiffOn.continuousOn.integrableOn_Icc

/-- `Φ₄` is integrable on `[0, 1]`: it is continuous on a compact set. -/
theorem Φ₄_integrableOn {r : ℝ} (_hr : r ≥ 0) : IntegrableOn (Φ₄ r)
    (Icc (0 : ℝ) 1) volume :=
  Φ₄_contDiffOn.continuousOn.integrableOn_Icc

/-! ### Vertical tail -/

/-- On `[1, ∞)` the real integrand `Φ₆` coincides with the integrand `g` of `I₆`. -/
lemma Φ₆_eq_I₆_g (r t : ℝ) (ht : t ∈ Ici (1 : ℝ)) : Φ₆ r t = IntegralEstimates.I₆.g r t := by
  simp only [Φ₆, Φ₆', IntegralEstimates.I₆.g, z₆'_eq_of_mem ht, cexp_pi_I_mul_I]
  ring_nf

/-- `Φ₆` is integrable on `[1, ∞)`, dominated by the vertical-class majorant. -/
theorem Φ₆_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₆ r) (Ici (1 : ℝ)) volume := by
  obtain ⟨C₀, _, hb⟩ := IntegralEstimates.I₆.I₆'_bounding_aux_2 r
  exact Integrable.mono' (integrableOn_majorant_vertical r C₀ hr)
    (Φ₆_contDiffOn.continuousOn.aestronglyMeasurable measurableSet_Ici)
    (ae_restrict_of_forall_mem measurableSet_Ici fun t ht ↦ (Φ₆_eq_I₆_g r t ht).symm ▸ hb t ht)

end MagicFunction.a.Integrability
