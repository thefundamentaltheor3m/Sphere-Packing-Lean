/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import SpherePacking.MagicFunction.a.FourierExpansions

/-!
# PhiBounds Structure

Bundles Corollary 7.5-7.7 bounds on φ₀, φ₂', φ₄' as hypotheses.

## Blueprint references

- **Corollary 7.5**: φ₀ bound with exp(-2πt) decay
- **Corollary 7.6**: φ₂' bounded (constant)
- **Corollary 7.7**: φ₄' bound with exp(2πt) growth
-/

open Real UpperHalfPlane

noncomputable section

namespace MagicFunction.a

/-- Bundle of Corollary 7.5-7.7 bounds as hypotheses.
    Blueprint states these for Im(z) > 1/2, which is the condition we use. -/
structure PhiBounds where
  C₀ : ℝ
  C₂ : ℝ
  C₄ : ℝ
  hC₀_pos : 0 < C₀
  hC₂_pos : 0 < C₂
  hC₄_pos : 0 < C₄
  hφ₀ : ∀ z : ℍ, 1/2 < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im)
  hφ₂ : ∀ z : ℍ, 1/2 < z.im → ‖φ₂' z‖ ≤ C₂
  hφ₄ : ∀ z : ℍ, 1/2 < z.im → ‖φ₄' z‖ ≤ C₄ * Real.exp (2 * π * z.im)

open scoped ArithmeticFunction.sigma
open ArithmeticFunction
open MagicFunction.PolyFourierCoeffBound
open MagicFunction.a.FourierExpansions

/-- PhiBounds instance from modular forms theory using explicit DivDiscBound constants.
    This avoids the axiom of choice by using computable bounds directly.
    The bounds follow from Corollaries 7.5-7.7 which use Ramanujan identities.
    See FourierExpansions.lean for the q-expansion lemmas. -/
def phiBounds : PhiBounds where
  C₀ := DivDiscBound c_E₂E₄E₆ 4
  C₂ := DivDiscBound c_E₂E₄E₆ 2
  C₄ := DivDiscBound c_E₄_sq 0
  hC₀_pos := by
    refine DivDiscBound_pos c_E₂E₄E₆ 4 ?_ 5 c_E₂E₄E₆_poly
    simp only [c_E₂E₄E₆, ne_eq, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, Int.cast_eq_zero, false_or]
    norm_cast
  hC₂_pos := by
    refine DivDiscBound_pos c_E₂E₄E₆ 2 ?_ 5 c_E₂E₄E₆_poly
    simp only [c_E₂E₄E₆, ne_eq, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, Int.cast_eq_zero, false_or]
    norm_cast
  hC₄_pos := by
    refine DivDiscBound_pos c_E₄_sq 0 ?_ 5 c_E₄_sq_poly
    simp only [c_E₄_sq, le_refl, ↓reduceIte, ne_eq, one_ne_zero, not_false_eq_true]
  hφ₀ := fun z hz => by
    have h := DivDiscBoundOfPolyFourierCoeff z hz c_E₂E₄E₆ 4 (summable_E₂E₄E₆_sq z)
        5 c_E₂E₄E₆_poly (fun z ↦ ((E₂ z) * (E₄ z) - (E₆ z)) ^ 2) E₂E₄E₆_sq_fourier
    simp only [φ₀]
    convert h using 2
    ring_nf
  hφ₂ := fun z hz => by
    have h := DivDiscBoundOfPolyFourierCoeff z hz c_E₂E₄E₆ 2 (summable_E₄_E₂E₄E₆ z)
        5 c_E₂E₄E₆_poly (fun z ↦ E₄ z * (E₂ z * E₄ z - E₆ z)) E₄_E₂E₄E₆_fourier
    simp only [φ₂']
    calc ‖(E₄ z * (E₂ z * E₄ z - E₆ z)) / Δ z‖
        ≤ DivDiscBound c_E₂E₄E₆ 2 * Real.exp (-π * (2 - 2) * z.im) := h
      _ = DivDiscBound c_E₂E₄E₆ 2 * Real.exp 0 := by ring_nf
      _ = DivDiscBound c_E₂E₄E₆ 2 := by simp
  hφ₄ := fun z hz => by
    have h := DivDiscBoundOfPolyFourierCoeff z hz c_E₄_sq 0 (summable_E₄_sq z)
        5 c_E₄_sq_poly (fun z ↦ E₄ z ^ 2) E₄_sq_fourier
    simp only [φ₄']
    convert h using 2
    ring_nf

end MagicFunction.a

end
