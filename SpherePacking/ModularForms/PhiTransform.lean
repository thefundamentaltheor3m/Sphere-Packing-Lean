/-
Copyright (c) 2024 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
module
public import SpherePacking.ModularForms.Eisenstein
public import SpherePacking.ModularForms.E2
public import SpherePacking.ModularForms.Delta

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

open ModularForm EisensteinSeries UpperHalfPlane

noncomputable section

/-- `φ₀` is 1-periodic: `φ₀ ((1 : ℝ) +ᵥ z) = φ₀ z`. -/
public theorem φ₀_periodic (z : ℍ) : φ₀ ((1 : ℝ) +ᵥ z) = φ₀ z := by
  simp [φ₀, E₂_periodic, E₄_periodic, E₆_periodic, Δ_periodic, -E4_apply, -E6_apply]

/-- The `S`-transformation formula for `φ₀` (Blueprint Lemma 7.2).

Here `φ₂'` and `φ₄'` are the auxiliary functions appearing in the definition of `φ₀`.
-/
public theorem φ₀_S_transform (z : ℍ) :
    φ₀ (ModularGroup.S • z) = φ₀ z - (12 * Complex.I) / (π * z) * φ₂' z
                             - 36 / (π ^ 2 * z ^ 2) * φ₄' z := by
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  unfold φ₀ φ₂' φ₄'
  rw [E₂_S_transform, E₄_S_transform, E₆_S_transform, Δ_S_transform]
  set A := A_E z with hA
  have h_numer : (z : ℂ) ^ 2 * (E₂ z + 6 / (π * Complex.I * z)) * (z ^ 4 * E₄ z) -
                 z ^ 6 * E₆ z = z ^ 6 * (A + 6 * E₄ z / (π * Complex.I * z)) := by
    simp [div_eq_mul_inv, hA, A_E]
    ring
  rw [h_numer]
  have h_sq : (z ^ 6 * (A + 6 * E₄ z / (π * Complex.I * z))) ^ 2 =
              z ^ 12 * (A + 6 * E₄ z / (π * Complex.I * z)) ^ 2 := by
    rw [mul_pow, sq (z ^ 6 : ℂ), ← pow_add]
  rw [h_sq]
  have h_div : z ^ 12 * (A + 6 * E₄ z / (π * Complex.I * z)) ^ 2 / (z ^ 12 * Δ z) =
               (A + 6 * E₄ z / (π * Complex.I * z)) ^ 2 / Δ z := by
    rw [mul_comm (z ^ 12 : ℂ) (Δ z)]; field_simp
  rw [h_div]
  have h_expand : (A + 6 * E₄ z / (π * Complex.I * z)) ^ 2 / Δ z =
                  A ^ 2 / Δ z + 12 * A * E₄ z / (π * Complex.I * z * Δ z) +
                  36 * (E₄ z) ^ 2 / (π ^ 2 * Complex.I ^ 2 * z ^ 2 * Δ z) := by
    have hπIz : π * Complex.I * z ≠ 0 := mul_ne_zero (mul_ne_zero hπ hI) hz
    field_simp; ring
  rw [h_expand, Complex.I_sq]
  have h_I_factor : (12 : ℂ) / (π * Complex.I * z) = -12 * Complex.I / (π * z) := by
    field_simp [Complex.inv_I]; simp [Complex.I_sq]
  have h_final : A ^ 2 / Δ z + 12 * A * E₄ z / (π * Complex.I * z * Δ z) +
       36 * (E₄ z) ^ 2 / (π ^ 2 * (-1) * z ^ 2 * Δ z) =
       A ^ 2 / Δ z - 12 * Complex.I / (π * z) * (E₄ z * A / Δ z) -
       36 / (π ^ 2 * z ^ 2) * ((E₄ z) ^ 2 / Δ z) := by
    have h1 : 12 * A * E₄ z / (π * Complex.I * z * Δ z) =
              12 / (π * Complex.I * z) * (E₄ z * A / Δ z) := by field_simp
    rw [h1, h_I_factor]; ring
  rw [h_final]
  simp [hA, A_E]

end
