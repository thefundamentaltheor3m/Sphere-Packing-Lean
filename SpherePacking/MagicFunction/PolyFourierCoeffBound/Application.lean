/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.PolyFourierCoeffBound.Basic
public import SpherePacking.MagicFunction.PolyFourierCoeffBound.AECoefficients


/-!
# Application: exponential decay bounds for `φ₀`

This file specializes the general bound `DivDiscBoundOfPolyFourierCoeff` together
with the Fourier data for `(A_E)^2` (from `AECoefficients.lean`) to produce the
concrete exponential decay estimates on the magic function `φ₀`.

## Main statements
* `MagicFunction.PolyFourierCoeffBound.norm_φ₀_le`
* `MagicFunction.PolyFourierCoeffBound.norm_φ₀''_le_mul_exp_neg_pi_of_one_half_lt_im`
-/

namespace MagicFunction.PolyFourierCoeffBound

noncomputable section

open scoped UpperHalfPlane ArithmeticFunction.sigma BigOperators

open Filter Complex Real Asymptotics ArithmeticFunction

/-- Exponential decay for the magic function `φ₀` in the upper half-plane.

This produces a constant `C₀` such that `‖φ₀ z‖ ≤ C₀ * exp (-2 * π * Im z)` for `Im z > 1/2`.
-/
public theorem norm_φ₀_le : ∃ C₀ > 0, ∀ z : ℍ, 1 / 2 < z.im →
    norm (φ₀ z) ≤ C₀ * rexp (-2 * π * z.im) := by
  refine ⟨DivDiscBound A_E_sq_fourierCoeff 4, ?_, ?_⟩
  · simpa [gt_iff_lt] using
      DivDiscBound_pos (c := A_E_sq_fourierCoeff) (n₀ := (4 : ℤ))
        (hcn₀ := A_E_sq_fourierCoeff_four_ne_zero) (k := 11) (hpoly := A_E_sq_fourierCoeff_isBigO)
  · intro z hz
    have hmain :
        norm (((A_E z) ^ 2) / (Δ z)) ≤
          (DivDiscBound A_E_sq_fourierCoeff 4) * rexp (-π * ((4 : ℤ) - 2) * z.im) :=
      DivDiscBoundOfPolyFourierCoeff (z := z) (hz := hz) (c := A_E_sq_fourierCoeff)
        (n₀ := (4 : ℤ)) (hcsum := by simpa using A_E_sq_fourierCoeff_summable (z := z) hz)
        (k := 11) (hpoly := A_E_sq_fourierCoeff_isBigO) (f := fun z ↦ (A_E z) ^ 2)
        (hf := fun x => by simpa using A_E_sq_fourierCoeff_hf (x := x))
    have hrexp : rexp (-(π * (4 - 2) * z.im)) = rexp (-(2 * π * z.im)) := by
      congr 1; ring
    simpa [φ₀, A_E, hrexp] using hmain

/-- A derived uniform bound for `φ₀''` on the region `Im z > 1/2`.

This is the specialization of `norm_φ₀_le` to a fixed point `z` with `Im z > 1/2`, after bounding
`exp (-2 * π * Im z)` by `exp (-π)`.
-/
public lemma norm_φ₀''_le_mul_exp_neg_pi_of_one_half_lt_im {C₀ : ℝ} (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, 1 / 2 < z.im → ‖φ₀ z‖ ≤ C₀ * rexp (-2 * π * z.im)) (z : ℍ)
    (hz : 1 / 2 < z.im) : ‖φ₀'' (z : ℂ)‖ ≤ C₀ * rexp (-π) := by
  have hzpos : 0 < (z : ℂ).im := by simpa using lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hz
  have hexp : rexp (-2 * π * z.im) ≤ rexp (-π) := by
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_pos, hz]
  calc
    ‖φ₀'' (z : ℂ)‖ = ‖φ₀ z‖ := by
      simp [φ₀''_def (z := (z : ℂ)) hzpos, show (⟨(z : ℂ), hzpos⟩ : ℍ) = z from by ext; rfl]
    _ ≤ C₀ * rexp (-2 * π * z.im) := hC₀ z hz
    _ ≤ C₀ * rexp (-π) := mul_le_mul_of_nonneg_left hexp hC₀_pos.le

end

end MagicFunction.PolyFourierCoeffBound
