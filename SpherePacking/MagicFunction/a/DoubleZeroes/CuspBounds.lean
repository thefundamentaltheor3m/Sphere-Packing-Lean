/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module


public import SpherePacking.ModularForms.PhiTransform
public import SpherePacking.MagicFunction.a.PhiBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Cusp Bounds for `φ₀` along the Imaginary Axis

The alternate integral representation of `a` used in the double-zeroes argument integrates
`φ₀(i/t)` along the positive imaginary axis. Its convergence rests on two estimates with
different characters, and this file proves both.

* **Small `t`** (`norm_φ₀_I_div_t_small`, thesis Lemma 4.4.3). For `t ∈ (0, 2)` the point
  `i/t` has imaginary part `1/t > 1/2`, so `φ₀_bound` applies directly and gives
  super-exponential decay `C_φ₀ * exp (-2π/t)`.
* **Large `t`** (`norm_φ₀_I_div_t_large`, thesis Lemma 4.4.4 = blueprint Corollary 7.13).
  For `t ≥ 2` the point `i/t` approaches the *real* axis, where `φ₀` blows up. The
  S-transformation formula `φ₀_S_transform` rewrites `φ₀(i/t)` in terms of `φ₀`, `φ₂'` and
  `φ₄'` at `it`, whose bounds (`PhiBounds`) then give `O(t⁻² e^{2πt})`.

The intermediate `norm_φ₀_S_smul_le` states the S-transform bound for an arbitrary `z : ℍ`
with `Im z ≥ 1`; `norm_φ₀''_I_div_t_le` is its specialisation to `z = it`.

## References

- Sid's M4R thesis, Section 4.4.1 (Lemmas 4.4.3, 4.4.4)
- Blueprint, Corollaries 7.5–7.7 and 7.13
-/

@[expose] public section

open MeasureTheory Set Filter Real UpperHalfPlane TopologicalSpace
open MagicFunction.a

open scoped Interval Real Topology

noncomputable section

namespace MagicFunction.a.DoubleZeroes

/-! ## The S-transform bound (blueprint Corollary 7.13) -/

/-- The point it as an element of ℍ for t > 0. -/
def mkI_mul_t (t : ℝ) (ht : 0 < t) : ℍ :=
  ⟨Complex.I * t, by simpa using ht⟩

/-- S action on it gives i/t. -/
lemma S_smul_I_mul_t (t : ℝ) (ht : 0 < t) :
    (↑(ModularGroup.S • mkI_mul_t t ht) : ℂ) = Complex.I / t := by
  rw [modular_S_smul]
  simp [mkI_mul_t, div_eq_mul_inv, mul_comm]

/-- im(it) = t when viewed as element of ℍ. -/
lemma mkI_mul_t_im (t : ℝ) (ht : 0 < t) : (mkI_mul_t t ht).im = t := by
  simp [mkI_mul_t]

/-- φ₀''(I/t) equals φ₀ applied to S•(I*t). -/
lemma φ₀''_I_div_t_eq (t : ℝ) (ht : 0 < t) :
    φ₀'' (Complex.I / t) = φ₀ (ModularGroup.S • mkI_mul_t t ht) := by
  rw [φ₀''_def (by simpa [Complex.div_ofReal_im] using ht)]
  simpa using congrArg φ₀ (UpperHalfPlane.ext (S_smul_I_mul_t t ht).symm)

/-- Norm of I*t equals t for t > 0. -/
lemma norm_I_mul_t (t : ℝ) (ht : 0 < t) : ‖(Complex.I * t : ℂ)‖ = t := by
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]

/-- The coefficient (12I)/(πz) has norm 12/(π|z|). -/
lemma norm_coeff_12I_div (z : ℂ) :
    ‖(12 * Complex.I) / (↑π * z)‖ = 12 / (π * ‖z‖) := by
  rw [norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat]
  simp only [mul_one, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- The coefficient 36/(π²z²) has norm 36/(π²|z|²). -/
lemma norm_coeff_36_div_sq (z : ℂ) :
    ‖36 / (↑π ^ 2 * z ^ 2)‖ = 36 / (π^2 * ‖z‖^2) := by
  rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real]
  simp only [Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat]

/-- General S-transform bound for any z with im(z) ≥ 1.
    This is the generalized Corollary 7.13. -/
lemma norm_φ₀_S_smul_le (z : ℍ) (hz : 1 ≤ z.im) :
    ‖φ₀ (ModularGroup.S • z)‖ ≤ C_φ₀ * Real.exp (-2 * π * z.im)
        + (12 / (π * ‖(z : ℂ)‖)) * C_φ₂'
        + (36 / (π^2 * ‖(z : ℂ)‖^2)) * C_φ₄'
            * Real.exp (2 * π * z.im) := by
  have hz' : 1 / 2 < z.im := by linarith
  have h₀ := φ₀_bound z hz'
  have h₂ := φ₂'_bound z hz'
  have h₄ := φ₄'_bound z hz'
  rw [φ₀_S_transform]
  refine (norm_sub_le _ _).trans ((add_le_add_left (norm_sub_le _ _) _).trans ?_)
  simp only [norm_mul, norm_coeff_12I_div, norm_coeff_36_div_sq]
  rw [mul_assoc (36 / (π ^ 2 * ‖(z : ℂ)‖ ^ 2))]
  gcongr

/-- Corollary 7.13: S-transform bound for φ₀(i/t) at large t.
    Specializes norm_φ₀_S_smul_le to z = I*t where z.im = ‖z‖ = t. -/
lemma norm_φ₀''_I_div_t_le (t : ℝ) (ht : 1 ≤ t) :
    ‖φ₀'' (Complex.I / t)‖ ≤ C_φ₀ * Real.exp (-2 * π * t)
                    + (12 / (π * t)) * C_φ₂'
                    + (36 / (π^2 * t^2)) * C_φ₄' * Real.exp (2 * π * t) := by
  have ht_pos : 0 < t := by linarith
  rw [φ₀''_I_div_t_eq t ht_pos]
  have h := norm_φ₀_S_smul_le (mkI_mul_t t ht_pos) (by simpa [mkI_mul_t_im] using ht)
  simp only [mkI_mul_t_im] at h
  rwa [show ‖(↑(mkI_mul_t t ht_pos) : ℂ)‖ = t from norm_I_mul_t t ht_pos] at h


/-! ## The two thesis bounds

Together these give convergence of the alternate integral in thesis Definition 4.4.2. -/

/-- Lemma 4.4.3: For small t ∈ (0, 2), φ₀(i/t) has super-exponential decay.
    This follows from the cusp bound (4.2.1) with z = i/t. -/
lemma norm_φ₀_I_div_t_small :
    ∀ t ∈ Ioo (0 : ℝ) 2, ‖φ₀'' (Complex.I / t)‖ ≤ C_φ₀ * Real.exp (-2 * π / t) := by
  intro t ⟨ht_pos, ht_lt⟩
  -- i/t has imaginary part 1/t > 1/2 for t < 2
  have hI_div_pos : 0 < (Complex.I / t).im := by simpa [Complex.div_ofReal_im] using ht_pos
  have hI_div_gt : 1 / 2 < (Complex.I / t).im := by
    simpa [Complex.div_ofReal_im] using one_div_lt_one_div_of_lt ht_pos ht_lt
  -- φ₀'' equals φ₀ on the upper half-plane, so the Corollary 7.5 bound applies
  rw [φ₀''_def hI_div_pos]
  have h := φ₀_bound ⟨Complex.I / t, hI_div_pos⟩ hI_div_gt
  have him : UpperHalfPlane.im ⟨Complex.I / t, hI_div_pos⟩ = 1 / t := by simp [UpperHalfPlane.im]
  rwa [him, show -2 * π * (1 / t) = -2 * π / t from by ring] at h

/-- For `t ≥ 2`, the exponential `exp (4πt)` bounds `t²`, as needed in thesis Lemma 4.4.4. -/
lemma sq_le_exp_4pi_t (t : ℝ) (ht : 2 ≤ t) : t^2 ≤ Real.exp (4 * π * t) := by
  -- exp(4πt) ≥ 1 + 4πt + (4πt)²/2 = 1 + 4πt + 8π²t² ≥ t², uniformly (8π² > 1 since π > 3)
  have h4πt_pos : 0 ≤ 4 * π * t := by positivity
  have hquad := Real.quadratic_le_exp_of_nonneg h4πt_pos
  have h8π2 : 8 * π ^ 2 > 1 := by nlinarith [Real.pi_gt_three]
  nlinarith [hquad, h8π2, sq_nonneg t, h4πt_pos]

/-- Helper: exp(-2πt) ≤ (1/t²) * exp(2πt) for t ≥ 2. Used in Thesis Lemma 4.4.4. -/
lemma exp_neg_le_inv_sq_exp (t : ℝ) (ht : 2 ≤ t) :
    Real.exp (-2 * π * t) ≤ (1 / t^2) * Real.exp (2 * π * t) := by
  have ht_pos : 0 < t := by linarith
  calc Real.exp (-2 * π * t) = Real.exp (2 * π * t) / Real.exp (4 * π * t) := by
          rw [← Real.exp_sub, show 2 * π * t - 4 * π * t = -2 * π * t from by ring]
    _ ≤ Real.exp (2 * π * t) / t^2 :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) (sq_le_exp_4pi_t t ht)
    _ = (1 / t^2) * Real.exp (2 * π * t) := by rw [one_div, div_eq_mul_inv, mul_comm]

/-- Helper: t ≤ exp(2πt) for t ≥ 0. Used for 1/t ≤ (1/t²) * exp(2πt). -/
lemma t_le_exp_two_pi_t (t : ℝ) (ht : 0 ≤ t) : t ≤ Real.exp (2 * π * t) := by
  nlinarith [Real.add_one_le_exp (2 * π * t), Real.pi_gt_three]

/-- Thesis Lemma 4.4.4 (Blueprint Cor 7.13): For large t ≥ 2, φ₀(i/t) grows at most
    like t⁻² e^{2πt}. Uses the S-transform formula (4.1.5) and bounds from Cor 7.5-7.7.

    Strategy: The three-term bound from norm_φ₀''_I_div_t_le can each be bounded by
    (constant) * t^(-2) * exp(2πt), which gives an overall bound of this form. -/
lemma norm_φ₀_I_div_t_large :
    ∀ t : ℝ, 2 ≤ t → ‖φ₀'' (Complex.I / t)‖ ≤
      (C_φ₀ + 12 * C_φ₂' / π + 36 * C_φ₄' / π ^ 2) *
        t ^ (-2 : ℤ) * Real.exp (2 * π * t) := by
  intro t ht
  have ht_pos : 0 < t := by linarith
  have ht_ge_1 : 1 ≤ t := by linarith
  -- Use the S-transform bound (blueprint Corollary 7.13) proved above
  have h := norm_φ₀''_I_div_t_le t ht_ge_1
  -- Each of the three terms can be bounded by its coefficient * t^(-2) * exp(2πt)
  -- Key inequalities:
  -- (1) exp(-2πt) ≤ t^(-2) * exp(2πt)  [since t² ≤ exp(4πt) for t ≥ 2]
  -- (2) 1/t ≤ t^(-2) * exp(2πt)  [since t ≤ exp(2πt)]
  -- (3) 1/t² * exp(2πt) = t^(-2) * exp(2πt)  [exact equality]
  have hπ := Real.pi_pos
  -- Rewrite t^(-2 : ℤ) as 1/t²
  rw [show t ^ (-2 : ℤ) = 1 / t^2 from by field_simp]
  -- Bound term 1: C₀ * exp(-2πt) ≤ C₀ * (1/t²) * exp(2πt)
  have h1 : C_φ₀ * Real.exp (-2 * π * t) ≤ C_φ₀ * (1 / t^2) * Real.exp (2 * π * t) := by
    rw [mul_assoc C_φ₀]
    exact mul_le_mul_of_nonneg_left (exp_neg_le_inv_sq_exp t ht) C_φ₀_pos.le
  -- Bound term 2: (12/(πt)) * C₂ ≤ (12*C₂/π) * (1/t²) * exp(2πt)
  -- Need: 1/t ≤ (1/t²) * exp(2πt), i.e., t ≤ exp(2πt)
  have h2 : (12 / (π * t)) * C_φ₂' ≤
      (12 * C_φ₂' / π) * (1 / t^2) * Real.exp (2 * π * t) := by
    -- 1/t ≤ (1/t²) * exp(2πt) is equivalent to t ≤ exp(2πt) (after multiplying by t² and dividing)
    have h_t_inv : 1 / t ≤ (1 / t^2) * Real.exp (2 * π * t) := by
      calc 1 / t = t / t^2 := by field_simp
        _ ≤ Real.exp (2 * π * t) / t^2 :=
            div_le_div_of_nonneg_right (t_le_exp_two_pi_t t ht_pos.le) (by positivity)
        _ = (1 / t^2) * Real.exp (2 * π * t) := by ring
    rw [show 12 / (π * t) * C_φ₂' = 12 * C_φ₂' / π * (1 / t) from by field_simp, mul_assoc]
    exact mul_le_mul_of_nonneg_left h_t_inv (div_nonneg (by nlinarith [C_φ₂'_pos.le]) hπ.le)
  -- Bound term 3: (36/(π²*t²)) * C₄ * exp(2πt) = (36*C₄/π²) * (1/t²) * exp(2πt)  [exact]
  have h3 : (36 / (π^2 * t^2)) * C_φ₄' * Real.exp (2 * π * t) =
            (36 * C_φ₄' / π^2) * (1 / t^2) * Real.exp (2 * π * t) := by
    field_simp
  -- Combine the bounds
  calc ‖φ₀'' (Complex.I / t)‖
      ≤ C_φ₀ * Real.exp (-2 * π * t) + (12 / (π * t)) * C_φ₂' +
        (36 / (π^2 * t^2)) * C_φ₄' * Real.exp (2 * π * t) := h
    _ ≤ C_φ₀ * (1 / t^2) * Real.exp (2 * π * t) +
        (12 * C_φ₂' / π) * (1 / t^2) * Real.exp (2 * π * t) +
        (36 * C_φ₄' / π^2) * (1 / t^2) * Real.exp (2 * π * t) := by linarith [h1, h2, h3.le]
    _ = (C_φ₀ + 12 * C_φ₂' / π + 36 * C_φ₄' / π^2) *
        (1 / t^2) * Real.exp (2 * π * t) := by ring

end MagicFunction.a.DoubleZeroes

end
