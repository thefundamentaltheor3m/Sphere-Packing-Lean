/-
Copyright (c) 2026 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Fourier transform of the Gaussian `x ↦ e^{πi‖x‖²z}`

Blueprint `lemma:Gaussian-Fourier`: for `z ∈ ℍ`, the Fourier transform on `ℝ⁸` of
`x ↦ e^{πi‖x‖²z}` is `y ↦ z⁻⁴ e^{πi‖y‖²(-1/z)}`. More generally, on a finite-dimensional real inner
product space `V` the factor is `(i / z) ^ (dim V / 2)`. This is the special case `b = -πiz` of
mathlib's `fourier_gaussian_innerProductSpace`.
-/

@[expose] public section

open Complex Real
open scoped FourierTransform UpperHalfPlane

/-- The Fourier transform of the Gaussian `x ↦ e^{πi‖x‖²z}` on a finite-dimensional real inner
product space `V`, for `z` in the upper half plane:
`𝓕 (e^{πi‖·‖²z}) y = (i / z) ^ (dim V / 2) e^{πi‖y‖²(-1/z)}`. -/
theorem fourier_gaussian_upperHalfPlane {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (z : ℍ) (y : V) :
    𝓕 (fun x : V ↦ cexp (π * I * ‖x‖ ^ 2 * z)) y =
      (I / z) ^ (Module.finrank ℝ V / 2 : ℂ) * cexp (π * I * ‖y‖ ^ 2 * (-1 / z)) := by
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hb : 0 < (-(π * I * z) : ℂ).re := by
    simpa using mul_pos Real.pi_pos z.im_pos
  convert fourier_gaussian_innerProductSpace hb y using 2
  · ext x
    ring_nf
  · congr 1
    field_simp
    simp
  · congr 1
    field_simp
    ring_nf
    simp

/-- The Fourier transform of the Gaussian `x ↦ e^{πi‖x‖²z}` on `ℝ⁸`, for `z` in the upper half
plane: `𝓕 (e^{πi‖·‖²z}) y = z⁻⁴ e^{πi‖y‖²(-1/z)}` (Blueprint `lemma:Gaussian-Fourier`). -/
theorem fourier_gaussian_upperHalfPlane_eight (z : ℍ) (y : EuclideanSpace ℝ (Fin 8)) :
    𝓕 (fun x : EuclideanSpace ℝ (Fin 8) ↦ cexp (π * I * ‖x‖ ^ 2 * z)) y =
      (z : ℂ) ^ (-4 : ℤ) * cexp (π * I * ‖y‖ ^ 2 * (-1 / z)) := by
  rw [fourier_gaussian_upperHalfPlane]
  have h : ((Module.finrank ℝ (EuclideanSpace ℝ (Fin 8)) : ℂ) / 2) = ((4 : ℕ) : ℂ) := by
    simp
    norm_num
  rw [h, cpow_natCast, div_pow, I_pow_four, zpow_neg, one_div]
  norm_cast
