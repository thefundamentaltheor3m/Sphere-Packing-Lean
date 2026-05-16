/-
Copyright (c) 2024 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
module

public import SpherePacking.ModularForms.Delta
public import SpherePacking.ModularForms.E2
public import SpherePacking.ModularForms.Eisenstein

/-!
# Transformation Rules for φ₀

This file proves the basic translation and `S`-transformation rules for the auxiliary function
`φ₀` used in the modular forms part of the sphere packing argument.

## Main statements
* `φ₀_periodic`
* `φ₀_S_transform`

## References
Blueprint Lemma 7.2.
-/

open scoped Real

open UpperHalfPlane

noncomputable section

/-- `φ₀` is 1-periodic: `φ₀ ((1 : ℝ) +ᵥ z) = φ₀ z`. -/
public theorem φ₀_periodic (z : ℍ) : φ₀ ((1 : ℝ) +ᵥ z) = φ₀ z := by
  simp only [φ₀, E₂_periodic, E₄_periodic, E₆_periodic, Δ_periodic]

/-- The `S`-transformation formula for `φ₀` (Blueprint Lemma 7.2).

Here `φ₂'` and `φ₄'` are the auxiliary functions appearing in the definition of `φ₀`.
-/
public theorem φ₀_S_transform (z : ℍ) :
    φ₀ (ModularGroup.S • z) = φ₀ z - (12 * Complex.I) / (π * z) * φ₂' z
                             - 36 / (π ^ 2 * z ^ 2) * φ₄' z := by
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΔ : Δ z ≠ 0 := Δ_ne_zero z
  unfold φ₀ φ₂' φ₄'
  rw [E₂_S_transform, E₄_S_transform, E₆_S_transform, Δ_S_transform]
  field_simp
  linear_combination 12 * E₄ z *
    (3 * E₄ z + (z : ℂ) * (π : ℂ) * Complex.I * (E₂ z * E₄ z - E₆ z)) * Complex.I_sq

end
