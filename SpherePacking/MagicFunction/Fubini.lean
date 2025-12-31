/-
Copyright (c) 2025 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/

import SpherePacking.MagicFunction.Segments

/-!
# Fubini Swap Lemmas for Contour Integrals

This file uses the integrability results from `Segments.lean` to prove Fubini-type
swap lemmas: ∫_{ℝ⁸} ∫_{contour} = ∫_{contour} ∫_{ℝ⁸}.

## Main results

### Fubini swap lemmas
- `I₁_integral_swap` through `I₆_integral_swap`: Swap ∫_{ℝ⁸} and ∫_{contour}

### Basic integrability (corollaries)
- `I₁_integrable` through `I₆_integrable`: Each Iⱼ is integrable on ℝ⁸
- `a_integrable`: The magic function `a` is integrable on ℝ⁸
-/

open MeasureTheory Complex Real Set intervalIntegral

local notation "V" => EuclideanSpace ℝ (Fin 8)

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions

noncomputable section

/-! ## Fubini Swap Lemmas

Once we have product integrability, Fubini's theorem allows swapping
the order of integration: ∫_{ℝ⁸} ∫_{contour} = ∫_{contour} ∫_{ℝ⁸}.
-/

section FubiniSwap

/-- Connection: I₁ x = ∫ t, I₁_integrand (x, t) -/
lemma I₁_eq_integral (x : V) :
    I₁ x = ∫ t in Ioc (0 : ℝ) 1, I₁_integrand (x, t) := by
  -- I₁ x = I₁' (‖x‖²) by definition
  -- I₁'_eq_Ioc gives the integral form with r = ‖x‖²
  rw [I₁, I₁'_eq_Ioc]
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Ioc
  refine ae_of_all _ fun t _ => ?_
  simp only [I₁_integrand, ofReal_pow]

/-- Connection: I₂ x = ∫ t, I₂_integrand (x, t) over [0,1].
Note: Uses Icc because the integrand is continuous (no singularity at 0). -/
lemma I₂_eq_integral (x : V) :
    I₂ x = ∫ t in Icc (0 : ℝ) 1, I₂_integrand (x, t) := by
  rw [I₂, I₂'_eq]
  -- Convert interval integral to Ioc, then Ioc to Icc (NoAtoms)
  rw [intervalIntegral_eq_integral_uIoc, if_pos (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), one_smul]
  rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Icc
  refine ae_of_all _ fun t _ => ?_
  simp only [I₂_integrand, ofReal_pow]

/-- Connection: I₃ x = ∫ t, I₃_integrand (x, t) -/
lemma I₃_eq_integral (x : V) :
    I₃ x = ∫ t in Ioc (0 : ℝ) 1, I₃_integrand (x, t) := by
  rw [I₃, I₃'_eq_Ioc]
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Ioc
  refine ae_of_all _ fun t _ => ?_
  simp only [I₃_integrand, ofReal_pow]

/-- Connection: I₄ x = ∫ t, I₄_integrand (x, t) over [0,1].
Note: Uses Icc because the integrand is continuous (no singularity at 0). -/
lemma I₄_eq_integral (x : V) :
    I₄ x = ∫ t in Icc (0 : ℝ) 1, I₄_integrand (x, t) := by
  rw [I₄, I₄'_eq]
  rw [intervalIntegral_eq_integral_uIoc, if_pos (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), one_smul]
  rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Icc
  refine ae_of_all _ fun t _ => ?_
  simp only [I₄_integrand, ofReal_pow]

/-- Connection: I₅ x = -2 * ∫ t, I₅_integrand (x, t) -/
lemma I₅_eq_integral (x : V) :
    I₅ x = -2 * ∫ t in Ioc (0 : ℝ) 1, I₅_integrand (x, t) := by
  rw [I₅, I₅'_eq_Ioc]
  congr 1
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Ioc
  refine ae_of_all _ fun t _ => ?_
  simp only [I₅_integrand, ofReal_pow]

/-- Connection: I₆ x = 2 * ∫ t, I₆_integrand (x, t) -/
lemma I₆_eq_integral (x : V) :
    I₆ x = 2 * ∫ t in Ici (1 : ℝ), I₆_integrand (x, t) := by
  rw [I₆, I₆'_eq]
  congr 1
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Ici
  refine ae_of_all _ fun t _ => ?_
  simp only [I₆_integrand, ofReal_pow]

/-- Fubini for I₁: swap ∫_{ℝ⁸} and ∫_{(0,1]} -/
theorem I₁_integral_swap :
    ∫ x : V, I₁ x = ∫ t in Ioc (0 : ℝ) 1, ∫ x : V, I₁_integrand (x, t) := by
  simp_rw [I₁_eq_integral]
  exact MeasureTheory.integral_integral_swap I₁_integrand_integrable

/-- Fubini for I₂: swap ∫_{ℝ⁸} and ∫_{[0,1]} -/
theorem I₂_integral_swap :
    ∫ x : V, I₂ x = ∫ t in Icc (0 : ℝ) 1, ∫ x : V, I₂_integrand (x, t) := by
  simp_rw [I₂_eq_integral]
  exact MeasureTheory.integral_integral_swap I₂_integrand_integrable

/-- Fubini for I₃: swap ∫_{ℝ⁸} and ∫_{(0,1]} -/
theorem I₃_integral_swap :
    ∫ x : V, I₃ x = ∫ t in Ioc (0 : ℝ) 1, ∫ x : V, I₃_integrand (x, t) := by
  simp_rw [I₃_eq_integral]
  exact MeasureTheory.integral_integral_swap I₃_integrand_integrable

/-- Fubini for I₄: swap ∫_{ℝ⁸} and ∫_{[0,1]} -/
theorem I₄_integral_swap :
    ∫ x : V, I₄ x = ∫ t in Icc (0 : ℝ) 1, ∫ x : V, I₄_integrand (x, t) := by
  simp_rw [I₄_eq_integral]
  exact MeasureTheory.integral_integral_swap I₄_integrand_integrable

/-- Fubini for I₅: swap ∫_{ℝ⁸} and ∫_{(0,1]}
Note: includes factor of -2 from I₅ definition. -/
theorem I₅_integral_swap :
    ∫ x : V, I₅ x = -2 * ∫ t in Ioc (0 : ℝ) 1, ∫ x : V, I₅_integrand (x, t) := by
  simp_rw [I₅_eq_integral]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact MeasureTheory.integral_integral_swap I₅_integrand_integrable

/-- Fubini for I₆: swap ∫_{ℝ⁸} and ∫_{[1,∞)}
Note: includes factor of 2 from I₆ definition. -/
theorem I₆_integral_swap :
    ∫ x : V, I₆ x = 2 * ∫ t in Ici (1 : ℝ), ∫ x : V, I₆_integrand (x, t) := by
  simp_rw [I₆_eq_integral]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact MeasureTheory.integral_integral_swap I₆_integrand_integrable

end FubiniSwap

/-! ## Basic Integrability

Each Iⱼ is integrable over ℝ⁸ (from Schwartz structure).
-/

section BasicIntegrability

/-- I₁ is integrable over ℝ⁸ (from Schwartz structure). -/
theorem I₁_integrable : Integrable (I₁ : V → ℂ) :=
  MagicFunction.a.SchwartzIntegrals.I₁.integrable

/-- I₂ is integrable over ℝ⁸ (from Schwartz structure). -/
theorem I₂_integrable : Integrable (I₂ : V → ℂ) :=
  MagicFunction.a.SchwartzIntegrals.I₂.integrable

/-- I₃ is integrable over ℝ⁸ (from Schwartz structure). -/
theorem I₃_integrable : Integrable (I₃ : V → ℂ) :=
  MagicFunction.a.SchwartzIntegrals.I₃.integrable

/-- I₄ is integrable over ℝ⁸ (from Schwartz structure). -/
theorem I₄_integrable : Integrable (I₄ : V → ℂ) :=
  MagicFunction.a.SchwartzIntegrals.I₄.integrable

/-- I₅ is integrable over ℝ⁸ (from Schwartz structure). -/
theorem I₅_integrable : Integrable (I₅ : V → ℂ) :=
  MagicFunction.a.SchwartzIntegrals.I₅.integrable

/-- I₆ is integrable over ℝ⁸ (from Schwartz structure). -/
theorem I₆_integrable : Integrable (I₆ : V → ℂ) :=
  MagicFunction.a.SchwartzIntegrals.I₆.integrable

/-- The magic function `a` is integrable over ℝ⁸. -/
theorem a_integrable : Integrable (a : V → ℂ) := by
  have h : a = I₁ + I₂ + I₃ + I₄ + I₅ + I₆ := by
    ext x
    simp only [Pi.add_apply]
    exact a_eq x
  rw [h]
  exact ((((I₁_integrable.add I₂_integrable).add I₃_integrable).add I₄_integrable).add
    I₅_integrable).add I₆_integrable

end BasicIntegrability

end

