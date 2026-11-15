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
`x ↦ e^{πi‖x‖²z}` is `y ↦ z⁻⁴ e^{πi‖y‖²(-1/z)}`. This is the special case `b = -πiz` of mathlib's
`fourier_gaussian_innerProductSpace`, using `(π / b) ^ 4 = (i / z) ^ 4 = z⁻⁴` and
`-π² ‖y‖² / b = πi ‖y‖² (-1 / z)`.
-/

@[expose] public section

open Complex Real
open scoped FourierTransform UpperHalfPlane

/-- The Fourier transform of the Gaussian `x ↦ e^{πi‖x‖²z}` on `ℝ⁸`, for `z` in the upper half
plane: `𝓕 (e^{πi‖·‖²z}) y = z⁻⁴ e^{πi‖y‖²(-1/z)}`. -/
theorem fourier_gaussian_upperHalfPlane (z : ℍ) (y : EuclideanSpace ℝ (Fin 8)) :
    𝓕 (fun x : EuclideanSpace ℝ (Fin 8) ↦ cexp (π * I * ‖x‖ ^ 2 * z)) y =
      (z : ℂ) ^ (-4 : ℤ) * cexp (π * I * ‖y‖ ^ 2 * (-1 / z)) := by
  sorry
