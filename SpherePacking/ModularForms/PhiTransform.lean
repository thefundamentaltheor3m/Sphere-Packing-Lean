/-
Copyright (c) 2024 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
import SpherePacking.ModularForms.Eisenstein
import SpherePacking.ModularForms.E2
import SpherePacking.ModularForms.Delta

/-!
# Transformation Rules for φ₀

This file proves the transformation properties of φ₀ under the modular group action,
as stated in Blueprint Lemma 7.2:

1. **T-periodicity**: `φ₀(z + 1) = φ₀(z)`
2. **S-transformation**: `φ₀(-1/z) = φ₀(z) - (12i/π)(1/z)φ₋₂(z) - (36/π²)(1/z²)φ₋₄(z)`

Note: The blueprint uses φ₋₂, φ₋₄ but Lean uses φ₂', φ₄' since negative subscripts
are not valid identifiers.

## Main Results

- `E₂_periodic`: E₂ is 1-periodic, i.e., `E₂(z + 1) = E₂(z)`
- `E₄_periodic`: E₄ is 1-periodic
- `E₆_periodic`: E₆ is 1-periodic
- `Δ_periodic`: Δ is 1-periodic
- `φ₀_periodic`: φ₀ is 1-periodic
- `φ₀_S_transform`: S-transformation formula for φ₀

-/

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

noncomputable section

/-! ## T-periodicity Lemmas -/

/-- E₂ is 1-periodic: E₂(z + 1) = E₂(z) -/
lemma E₂_periodic (z : ℍ) : E₂ ((1 : ℝ) +ᵥ z) = E₂ z := by
  have h := G2_periodic
  simp only [funext_iff] at h
  specialize h z
  rw [modular_slash_T_apply] at h
  unfold E₂
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h]

/-- E₄ is 1-periodic: E₄(z + 1) = E₄(z). This follows from E₄ being a modular form for Γ(1). -/
lemma E₄_periodic (z : ℍ) : E₄ ((1 : ℝ) +ᵥ z) = E₄ z := by
  have h : (E₄.toFun ∣[(4 : ℤ)] ModularGroup.T) z = E₄.toFun z := by
    apply congrFun
    apply E₄.slash_action_eq'
    simp only [Subgroup.mem_map, CongruenceSubgroup.mem_Gamma_one]
    use ModularGroup.T
  rw [modular_slash_T_apply] at h
  exact h

/-- E₆ is 1-periodic: E₆(z + 1) = E₆(z). This follows from E₆ being a modular form for Γ(1). -/
lemma E₆_periodic (z : ℍ) : E₆ ((1 : ℝ) +ᵥ z) = E₆ z := by
  have h : (E₆.toFun ∣[(6 : ℤ)] ModularGroup.T) z = E₆.toFun z := by
    apply congrFun
    apply E₆.slash_action_eq'
    simp only [Subgroup.mem_map, CongruenceSubgroup.mem_Gamma_one]
    use ModularGroup.T
  rw [modular_slash_T_apply] at h
  exact h

/-- Δ is 1-periodic: Δ(z + 1) = Δ(z) -/
lemma Δ_periodic (z : ℍ) : Δ ((1 : ℝ) +ᵥ z) = Δ z := by
  have h := Discriminant_T_invariant
  simp only [funext_iff] at h
  specialize h z
  rw [modular_slash_T_apply] at h
  exact h

/-! ## Main Theorem: T-periodicity of φ₀ -/

/-- φ₀ is 1-periodic: φ₀(z + 1) = φ₀(z) -/
theorem φ₀_periodic (z : ℍ) : φ₀ ((1 : ℝ) +ᵥ z) = φ₀ z := by
  unfold φ₀
  rw [E₂_periodic, E₄_periodic, E₆_periodic, Δ_periodic]

/-! ## S-transformation Lemmas -/

/-- E₂ transforms under S as: E₂(-1/z) = z² · (E₂(z) + 6/(πIz)).
    This is derived from E₂_transform by relating the slash action to the direct value. -/
lemma E₂_S_transform (z : ℍ) :
    E₂ (ModularGroup.S • z) = z ^ 2 * (E₂ z + 6 / (π * Complex.I * z)) := by
  have h := E₂_transform z
  -- E₂_transform says: (E₂ ∣[2] S) z = E₂ z + 6 / (π * I * z)
  -- The slash action (f ∣[k] γ) z = f(γ • z) * (denom γ z)^(-k)
  -- For S, denom S z = 1*z + 0 = z, so (E₂ ∣[2] S) z = E₂(S • z) / z²
  rw [SL_slash_apply] at h
  simp only [ModularGroup.denom_S, zpow_neg, zpow_two] at h
  -- h : E₂ (S • z) * (z * z)⁻¹ = E₂ z + 6 / (π * I * z)
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  have hz2 : (z : ℂ) * (z : ℂ) ≠ 0 := mul_ne_zero hz hz
  have h2 : E₂ (ModularGroup.S • z) = (E₂ z + 6 / (π * Complex.I * z)) * ((z : ℂ) * (z : ℂ)) := by
    have := congrArg (· * ((z : ℂ) * (z : ℂ))) h
    simp only at this
    rw [mul_assoc, inv_mul_cancel₀ hz2, mul_one] at this
    exact this
  rw [h2, sq, mul_comm]

/-- E₄ transforms under S as: E₄(-1/z) = z⁴ · E₄(z) -/
lemma E₄_S_transform (z : ℍ) : E₄ (ModularGroup.S • z) = z ^ (4 : ℕ) * E₄ z := by
  have h : (E₄.toFun ∣[(4 : ℤ)] ModularGroup.S) z = E₄.toFun z := by
    apply congrFun
    apply E₄.slash_action_eq'
    simp only [Subgroup.mem_map, CongruenceSubgroup.mem_Gamma_one]
    use ModularGroup.S
  rw [ModularForm.slash_action_eq'_iff] at h
  -- S = [[0, -1], [1, 0]], so (S 1 0) = 1 and (S 1 1) = 0
  -- Hence factor is (1 * z + 0)^4 = z^4
  simp only [ModularGroup.S, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Int.cast_one, one_mul, Int.cast_zero, add_zero] at h
  exact h

/-- E₆ transforms under S as: E₆(-1/z) = z⁶ · E₆(z) -/
lemma E₆_S_transform (z : ℍ) : E₆ (ModularGroup.S • z) = z ^ (6 : ℕ) * E₆ z := by
  have h : (E₆.toFun ∣[(6 : ℤ)] ModularGroup.S) z = E₆.toFun z := by
    apply congrFun
    apply E₆.slash_action_eq'
    simp only [Subgroup.mem_map, CongruenceSubgroup.mem_Gamma_one]
    use ModularGroup.S
  rw [ModularForm.slash_action_eq'_iff] at h
  simp only [ModularGroup.S, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Int.cast_one, one_mul, Int.cast_zero, add_zero] at h
  exact h

/-- Δ transforms under S as: Δ(-1/z) = z¹² · Δ(z) -/
lemma Δ_S_transform (z : ℍ) : Δ (ModularGroup.S • z) = z ^ (12 : ℕ) * Δ z := by
  have h := Discriminant_S_invariant
  simp only [funext_iff] at h
  specialize h z
  rw [ModularForm.slash_action_eq'_iff] at h
  simp only [ModularGroup.S, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Int.cast_one, one_mul, Int.cast_zero, add_zero] at h
  exact h

/-! ## Main Theorem: S-transformation of φ₀ -/

/-- The S-transformation formula for φ₀:
    φ₀(-1/z) = φ₀(z) - (12i/π)(1/z)φ₋₂(z) - (36/π²)(1/z²)φ₋₄(z)

    This is Blueprint Lemma 7.2.
-/
theorem φ₀_S_transform (z : ℍ) :
    φ₀ (ModularGroup.S • z) = φ₀ z - (12 * Complex.I) / (π * z) * φ₂' z
                             - 36 / (π ^ 2 * z ^ 2) * φ₄' z := by
  -- Set up key non-zero hypotheses
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hΔ : Δ z ≠ 0 := Δ_ne_zero z
  have hz2 : (z : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have hz12 : (z : ℂ) ^ 12 ≠ 0 := pow_ne_zero 12 hz
  -- Substitute transformation rules
  unfold φ₀ φ₂' φ₄'
  rw [E₂_S_transform, E₄_S_transform, E₆_S_transform, Δ_S_transform]
  -- Let A = E₂ z * E₄ z - E₆ z (the key expression)
  set A := E₂ z * E₄ z - E₆ z with hA
  -- The numerator E₂(S•z) * E₄(S•z) - E₆(S•z) simplifies to z⁶ * (A + 6E₄/(πIz))
  have h_numer : (z : ℂ) ^ 2 * (E₂ z + 6 / (π * Complex.I * z)) * (z ^ 4 * E₄ z) -
                 z ^ 6 * E₆ z = z ^ 6 * (A + 6 * E₄ z / (π * Complex.I * z)) := by
    ring_nf; rw [hA]; ring
  -- The main algebraic simplification
  rw [h_numer]
  -- Now we have: (z⁶ * (A + 6E₄/(πIz)))² / (z¹² * Δ z)
  -- = z¹² * (A + 6E₄/(πIz))² / (z¹² * Δ z) = (A + 6E₄/(πIz))² / Δ z
  have h_sq : (z ^ 6 * (A + 6 * E₄ z / (π * Complex.I * z))) ^ 2 =
              z ^ 12 * (A + 6 * E₄ z / (π * Complex.I * z)) ^ 2 := by
    rw [mul_pow, sq (z ^ 6 : ℂ), ← pow_add]
  rw [h_sq]
  -- Simplify z¹² * X / (z¹² * Δ z) = X / Δ z
  have h_div : z ^ 12 * (A + 6 * E₄ z / (π * Complex.I * z)) ^ 2 / (z ^ 12 * Δ z) =
               (A + 6 * E₄ z / (π * Complex.I * z)) ^ 2 / Δ z := by
    rw [mul_comm (z ^ 12 : ℂ) (Δ z)]; field_simp
  rw [h_div]
  -- Expand (A + 6E₄/(πIz))² = A² + 12AE₄/(πIz) + 36E₄²/(π²I²z²)
  -- Since I² = -1, we get: A² + 12AE₄/(πIz) - 36E₄²/(π²z²)
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have h_inv_I : (Complex.I)⁻¹ = -Complex.I := Complex.inv_I  -- Key: 1/I = -I
  -- Expand the square and simplify
  have h_expand : (A + 6 * E₄ z / (π * Complex.I * z)) ^ 2 / Δ z =
                  A ^ 2 / Δ z + 12 * A * E₄ z / (π * Complex.I * z * Δ z) +
                  36 * (E₄ z) ^ 2 / (π ^ 2 * Complex.I ^ 2 * z ^ 2 * Δ z) := by
    have hπIz : π * Complex.I * z ≠ 0 := mul_ne_zero (mul_ne_zero hπ hI) hz
    field_simp; ring
  rw [h_expand, hI2]
  -- Now: A²/Δ + 12AE₄/(πIzΔ) + 36E₄²/(π²(-1)z²Δ)
  --    = A²/Δ + 12AE₄/(πIzΔ) - 36E₄²/(π²z²Δ)
  --    = φ₀ + (12/(πIz))φ₂' - (36/(π²z²))φ₄'
  -- And 12/(πIz) = 12 * (1/I) / (πz) = 12 * (-I) / (πz) = -12I/(πz)
  -- Relate back to φ₀, φ₂', φ₄'
  have hφ₀ : A ^ 2 / Δ z = φ₀ z := by rfl
  have hφ₂' : E₄ z * A / Δ z = φ₂' z := by rfl
  have hφ₄' : (E₄ z) ^ 2 / Δ z = φ₄' z := by rfl
  -- Transform 12/(πIz) to -12I/(πz) using I⁻¹ = -I
  have h_I_factor : (12 : ℂ) / (π * Complex.I * z) = -12 * Complex.I / (π * z) := by
    have hπz : (π : ℂ) * z ≠ 0 := mul_ne_zero hπ hz
    rw [mul_comm (π : ℂ) Complex.I, mul_assoc, div_mul_eq_div_div, div_eq_mul_inv,
        div_eq_mul_inv, h_inv_I]; ring
  -- The main algebraic manipulation using h_I_factor
  -- LHS = A²/Δ + 12AE₄/(πIzΔ) + 36E₄²/(π²(-1)z²Δ)
  -- RHS = φ₀ - (12I/(πz))φ₂' - (36/(π²z²))φ₄'
  --     = A²/Δ - (12I/(πz))(E₄A/Δ) - (36/(π²z²))(E₄²/Δ)
  -- Key: 12/(πIz) = -12I/(πz) by h_I_factor
  have h_final : A ^ 2 / Δ z + 12 * A * E₄ z / (π * Complex.I * z * Δ z) +
       36 * (E₄ z) ^ 2 / (π ^ 2 * (-1) * z ^ 2 * Δ z) =
       A ^ 2 / Δ z - 12 * Complex.I / (π * z) * (E₄ z * A / Δ z) -
       36 / (π ^ 2 * z ^ 2) * ((E₄ z) ^ 2 / Δ z) := by
    have hπIzΔ : π * Complex.I * z * Δ z ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero hπ hI) hz) hΔ
    -- Use the h_I_factor to transform 12/(πIz) to -12I/(πz)
    have h1 : 12 * A * E₄ z / (π * Complex.I * z * Δ z) =
              12 / (π * Complex.I * z) * (E₄ z * A / Δ z) := by field_simp
    rw [h1, h_I_factor]; ring
  -- The goal now matches h_final applied to the expanded expression
  rw [h_final]

end

