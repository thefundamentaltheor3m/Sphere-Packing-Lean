/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds

public import SpherePacking.MagicFunction.a.Eigenfunction
public import SpherePacking.MagicFunction.a.SpecialValues
public import SpherePacking.MagicFunction.b.Eigenfunction
public import SpherePacking.MagicFunction.b.SpecialValues
public import SpherePacking.Tactic.NormNumI

/-! # Viazovska's Magic Function

In this file, we define Viazovska's magic funtction `g`.

## Sign conventions

With `b` defined as in the blueprint (`def:b-definition`, i.e. with `J₆ = -2 ∫_i^{i∞} ψS`), the
integral representations `a_eq_integral` and `b_eq_integral` read
`a = 4i sin²(π‖x‖²/2) ∫₀^∞ t² φ₀(i/t) e^{-π‖x‖²t} dt` and
`b = -4i sin²(π‖x‖²/2) ∫₀^∞ ψI(it) e^{-π‖x‖²t} dt` for `‖x‖ > √2`. The combination whose
integrand is `A(t) = -t² φ₀(i/t) - 36 π⁻² ψI(it)` (which is negative, giving `g ≤ 0` outside the
ball of radius `√2`) is therefore `g = (πi/8640) a - (i/(240π)) b`; see `g_eq_integral_A`.
-/

@[expose] public section
local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open SchwartzMap Complex Real MagicFunction.FourierEigenfunctions MagicFunction.a.Fourier
  MagicFunction.b.Fourier MagicFunction.a.SpecialValues MagicFunction.b.SpecialValues
open scoped FourierTransform

/-- The Magic Function, `g`. -/
noncomputable def g : 𝓢(ℝ⁸, ℂ) := ((π * I) / 8640) • a - (I / (240 * π)) • b

-- Note that in the proof, we need `g` to be Real-valued. We need to decide how we want to state
-- this: either `g ∘ Complex.im = 0` or we actually construct an element of `𝓢(ℝ⁸, ℝ)`...

section Zero

theorem g_zero : g 0 = 1 := by
  simp only [g, sub_apply, smul_apply, a_zero, neg_mul, smul_eq_mul, b_zero, mul_zero, sub_zero]
  ring_nf
  simp only [I_sq, mul_neg, mul_one, neg_mul, neg_neg]
  apply Complex.mul_inv_cancel
  norm_cast
  exact pi_ne_zero

theorem fourier_g_zero : 𝓕 g 0 = 1 := by
  have hb : 𝓕 (-b) = b := by rw [FourierTransform.fourier_neg, eig_b, neg_neg]
  have h : 𝓕 g = ((π * I) / 8640) • a + (I / (240 * π)) • b := by
    rw [g, sub_eq_add_neg, ← smul_neg, FourierAdd.fourier_add, FourierSMul.fourier_smul,
      FourierSMul.fourier_smul, eig_a, hb]
  rw [h, add_apply, smul_apply, smul_apply, a_zero, b_zero, smul_eq_mul, smul_eq_mul, mul_zero,
    add_zero]
  ring_nf
  simp only [I_sq, mul_neg, mul_one, neg_mul, neg_neg]
  apply Complex.mul_inv_cancel
  norm_cast
  exact pi_ne_zero

theorem g_zero_eq_fourier_g_zero : g 0 = 𝓕 g 0 := by
  rw [g_zero, fourier_g_zero]

end Zero

/-- `A(t) = -t² φ₀(i/t) - 36 π⁻² ψI(it)`, the integrand in the representation of `g` outside the
ball of radius `√2` (Blueprint `prop:ineqA`). -/
noncomputable def A (t : ℝ) :=
  - t ^ 2 * φ₀'' (I / t) - 36 * π ^ (-2 : ℤ) * ψI' (Complex.I * t)

/-- `B(t) = -t² φ₀(i/t) + 36 π⁻² ψI(it)`, the integrand in the representation of `𝓕 g`
(Blueprint `prop:ineqB`). -/
noncomputable def B (t : ℝ) :=
  - t ^ 2 * φ₀'' (I / t) + 36 * π ^ (-2 : ℤ) * ψI' (Complex.I * t)

lemma A_eq {t : ℝ} (ht : 0 < t) :
    A t =
      - t ^ 2 * φ₀ ⟨I / t, by simp [ht]⟩
        - 36 * π ^ (-2 : ℤ) * ψI ⟨I * t, by simp [ht]⟩ := by rw [A, φ₀''_def, ψI'_def]

lemma B_eq {t : ℝ} (ht : 0 < t) :
    B t =
      - t ^ 2 * φ₀ ⟨I / t, by simp [ht]⟩
        + 36 * π ^ (-2 : ℤ) * ψI ⟨I * t, by simp [ht]⟩ := by rw [B, φ₀''_def, ψI'_def]

/-- `A` in terms of `F` and `G`: for `t > 0`,
`A t = -t² / Δ(i/t) * (F(i/t) + 18 π⁻² G(i/t))`. This follows from `φ₀ = F / Δ`
(`φ₀_eq_F_div_disc`), `ψS = -G / (2Δ)` (`ψS_eq_neg_one_half_smul_G_div_disc`) and
`ψI(it) = -t² ψS(i/t)` (`ψI'_I_mul_eq`). Blueprint `lemma:ineqABnew-equiv`. -/
lemma A_eq_FG {t : ℝ} (ht : 0 < t) :
    A t = -t ^ 2 / Δ ⟨I / t, by simp [ht]⟩
      * (F ⟨I / t, by simp [ht]⟩ + 18 * π ^ (-2 : ℤ) * G ⟨I / t, by simp [ht]⟩) := by
  sorry

/-- `B` in terms of `F` and `G`: for `t > 0`,
`B t = -t² / Δ(i/t) * (F(i/t) - 18 π⁻² G(i/t))`. Blueprint `lemma:ineqABnew-equiv`. -/
lemma B_eq_FG {t : ℝ} (ht : 0 < t) :
    B t = -t ^ 2 / Δ ⟨I / t, by simp [ht]⟩
      * (F ⟨I / t, by simp [ht]⟩ - 18 * π ^ (-2 : ℤ) * G ⟨I / t, by simp [ht]⟩) := by
  sorry

/-- Integral representation of `g` in terms of `A`. -/
theorem g_eq_integral_A {x : ℝ⁸} (hx : √2 < ‖x‖) :
    g x =
      π / 2160 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2
        * ∫ (t : ℝ) in Set.Ioi 0, A t * rexp (- π * ‖x‖ ^ 2 * t) := by
  sorry

/-- Integral representation of Fourier transform of `g` in terms of `B`. -/
theorem g_Fourier_eq_integral_B {x : ℝ⁸} (hx : 0 < ‖x‖) :
    𝓕 g x =
      π / 2160 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2
        * ∫ (t : ℝ) in Set.Ioi 0, B t * rexp (- π * ‖x‖ ^ 2 * t) := by
  sorry

/-- `A` is negative on `(0, ∞)`: by `A_eq_FG`, this is `FG_inequality_1` at `1 / t` together with
the positivity of `Δ` on the imaginary axis (`Δ_imag_axis_pos`). Blueprint `prop:ineqA`. -/
theorem A_neg {t : ℝ} (ht : 0 < t) : (A t).re < 0 := by sorry

/-- `B` is positive on `(0, ∞)`: by `B_eq_FG`, this is `FG_inequality_2` at `1 / t` together with
the positivity of `Δ` on the imaginary axis (`Δ_imag_axis_pos`). Blueprint `prop:ineqB`. -/
theorem B_pos {t : ℝ} (ht : 0 < t) : 0 < (B t).re := by sorry

/-- `g` is nonpositive outside of the ball of radius `√2`. -/
theorem g_nonpos {x : ℝ⁸} (hx : √2 ≤ ‖x‖) : (g x).re ≤ 0 := by sorry

/-- Fourier transform of `g` is nonnegative everywhere. -/
theorem g_Fourier_nonneg (x : ℝ⁸) : 0 ≤ (𝓕 g x).re := by sorry
