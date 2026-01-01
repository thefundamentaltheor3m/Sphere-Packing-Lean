/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import SpherePacking.ModularForms.PhiTransform
import SpherePacking.MagicFunction.RealDecay
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Contour Endpoint Bounds for Vertical Rays

This file provides endpoint bounds and integrability lemmas for vertical contour rays,
as needed for the Cauchy-Goursat applications in the double zeroes proof (#229).

## Blueprint references

- **Corollary 7.5-7.7**: Bounds on φ₀, φ₋₂, φ₋₄ for Im(z) > 1/2
- **Corollary 7.13**: φ₀(i/t) = O(t⁻² e^{2πt}) as t → ∞
- **Proposition 7.14**: Vertical integrand → 0 as Im(z) → ∞ for r > 2

## Main results

- `PhiBounds`: Structure bundling Cor 7.5-7.7 bounds as hypotheses
- `norm_φ₀''_I_div_t_le`: Corollary 7.13 (3-term S-transform bound)
- `verticalIntegrandX`: Integrand for vertical edges at any x position
- `integrableOn_verticalIntegrandX`: Integrability for r > 2
- `tendsto_verticalIntegrandX_atTop`: Integrand → 0 as t → ∞

## Notes

We use `Im(z) ≥ 1` (stronger than the blueprint's `Im(z) > 1/2`) as a convenient
safe strip that covers all rectangle contour points.
-/

open MeasureTheory Set Filter Real UpperHalfPlane TopologicalSpace

open scoped Interval Real NNReal ENNReal Topology BigOperators

noncomputable section

namespace MagicFunction.ContourEndpoints

/-! ## PhiBounds structure (Corollaries 7.5-7.7 as hypotheses) -/

/-- Bundle of Corollary 7.5-7.7 bounds as hypotheses.
    Blueprint states these for Im(z) > 1/2; we use Im(z) ≥ 1 as a convenient
    safe strip that covers all rectangle contour points. -/
structure PhiBounds where
  C₀ : ℝ
  C₂ : ℝ
  C₄ : ℝ
  hC₀_pos : 0 < C₀
  hC₂_pos : 0 < C₂
  hC₄_pos : 0 < C₄
  hφ₀ : ∀ z : ℍ, 1 ≤ z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im)
  hφ₂ : ∀ z : ℍ, 1 ≤ z.im → ‖φ₂' z‖ ≤ C₂
  hφ₄ : ∀ z : ℍ, 1 ≤ z.im → ‖φ₄' z‖ ≤ C₄ * Real.exp (2 * π * z.im)

/-! ## Corollary 7.13 - S-transform bound for φ₀''(I/t) -/

/-- Helper: im(it) = t for real t. -/
lemma im_I_mul (t : ℝ) : (Complex.I * t).im = t := by simp

/-- Helper: im(i/t) = 1/t for real t ≠ 0. -/
lemma im_I_div (t : ℝ) (_ht : t ≠ 0) : (Complex.I / t).im = 1 / t := by
  simp only [Complex.div_ofReal_im, Complex.I_im]

/-- For t ≥ 1, the point it is in the upper half-plane with im ≥ 1. -/
lemma I_mul_t_in_UHP (t : ℝ) (ht : 1 ≤ t) : 0 < (Complex.I * t).im := by
  rw [im_I_mul]; linarith

/-- For t ≥ 1, the point i/t is in the upper half-plane. -/
lemma I_div_t_in_UHP (t : ℝ) (ht : 1 ≤ t) : 0 < (Complex.I / t).im := by
  have ht_pos : 0 < t := by linarith
  rw [im_I_div t (ne_of_gt ht_pos)]
  positivity

/-- The point it as an element of ℍ for t > 0. -/
def mkI_mul_t (t : ℝ) (ht : 0 < t) : ℍ :=
  ⟨Complex.I * t, by simp; exact ht⟩

/-- S action on it gives i/t. -/
lemma S_smul_I_mul_t (t : ℝ) (ht : 0 < t) :
    (↑(ModularGroup.S • mkI_mul_t t ht) : ℂ) = Complex.I / t := by
  rw [modular_S_smul]
  simp only [mkI_mul_t, coe_mk]
  have h : (-(Complex.I * t))⁻¹ = Complex.I / t := by field_simp; rw [Complex.I_sq]; ring
  exact h

/-- im(it) = t when viewed as element of ℍ. -/
lemma mkI_mul_t_im (t : ℝ) (ht : 0 < t) : (mkI_mul_t t ht).im = t := by
  simp only [mkI_mul_t, UpperHalfPlane.im]
  simp

/-- φ₀''(I/t) equals φ₀ applied to S•(I*t). -/
lemma φ₀''_I_div_t_eq (t : ℝ) (ht : 0 < t) :
    φ₀'' (Complex.I / t) = φ₀ (ModularGroup.S • mkI_mul_t t ht) := by
  have hI_div : 0 < (Complex.I / t).im := by
    rw [Complex.div_ofReal_im, Complex.I_im]
    positivity
  simp only [φ₀'']
  rw [dif_pos hI_div]
  congr 1
  apply Subtype.ext
  exact (S_smul_I_mul_t t ht).symm

/-- Norm of I*t equals t for t > 0. -/
lemma norm_I_mul_t (t : ℝ) (ht : 0 < t) : ‖(Complex.I * t : ℂ)‖ = t := by
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]

/-- The coefficient (12I)/(πz) has norm 12/(π|z|). -/
lemma norm_coeff_12I_div (z : ℂ) (hz : z ≠ 0) :
    ‖(12 * Complex.I) / (↑π * z)‖ = 12 / (π * ‖z‖) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hπz : (↑π : ℂ) * z ≠ 0 := mul_ne_zero hπ hz
  rw [norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat]
  simp only [mul_one, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- The coefficient 36/(π²z²) has norm 36/(π²|z|²). -/
lemma norm_coeff_36_div_sq (z : ℂ) (hz : z ≠ 0) :
    ‖36 / (↑π ^ 2 * z ^ 2)‖ = 36 / (π^2 * ‖z‖^2) := by
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hπ2 : (↑π : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hπ
  rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real]
  simp only [Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat]

/-- General S-transform bound for any z with im(z) ≥ 1.
    This is the generalized Corollary 7.13. -/
lemma norm_φ₀_S_smul_le (hb : PhiBounds) (z : ℍ) (hz : 1 ≤ z.im) :
    ‖φ₀ (ModularGroup.S • z)‖ ≤ hb.C₀ * Real.exp (-2 * π * z.im)
                              + (12 / (π * ‖(z : ℂ)‖)) * hb.C₂
                              + (36 / (π^2 * ‖(z : ℂ)‖^2)) * hb.C₄ * Real.exp (2 * π * z.im) := by
  -- Step 1: Use the S-transform formula
  rw [φ₀_S_transform]
  -- Step 2: Apply triangle inequality twice for a - b - c
  have h_tri : ‖φ₀ z - (12 * Complex.I) / (↑π * z) * φ₂' z - 36 / (↑π ^ 2 * ↑z ^ 2) * φ₄' z‖
      ≤ ‖φ₀ z‖ + ‖(12 * Complex.I) / (↑π * z) * φ₂' z‖
          + ‖36 / (↑π ^ 2 * ↑z ^ 2) * φ₄' z‖ := by
    have h1 : ‖φ₀ z - (12 * Complex.I) / (↑π * z) * φ₂' z - 36 / (↑π ^ 2 * ↑z ^ 2) * φ₄' z‖
        ≤ ‖φ₀ z - (12 * Complex.I) / (↑π * z) * φ₂' z‖
            + ‖36 / (↑π ^ 2 * ↑z ^ 2) * φ₄' z‖ := norm_sub_le _ _
    have h2 : ‖φ₀ z - (12 * Complex.I) / (↑π * z) * φ₂' z‖
        ≤ ‖φ₀ z‖ + ‖(12 * Complex.I) / (↑π * z) * φ₂' z‖ := norm_sub_le _ _
    linarith
  refine h_tri.trans ?_
  -- Step 3: Bound each of the three terms
  have hz_ne : (z : ℂ) ≠ 0 := ne_zero z
  -- Bound (i): ‖φ₀ z‖ ≤ C₀ * exp(-2πt)  [from hb.hφ₀]
  have hbound1 : ‖φ₀ z‖ ≤ hb.C₀ * exp (-2 * π * z.im) := hb.hφ₀ z hz
  -- Bound (ii): ‖(12I)/(πz) * φ₂' z‖ ≤ (12/(π‖z‖)) * C₂
  have hbound2 : ‖(12 * Complex.I) / (↑π * z) * φ₂' z‖ ≤ (12 / (π * ‖(z : ℂ)‖)) * hb.C₂ := by
    rw [norm_mul, norm_coeff_12I_div (z : ℂ) hz_ne]
    exact mul_le_mul_of_nonneg_left (hb.hφ₂ z hz) (by positivity)
  -- Bound (iii): ‖36/(π²z²) * φ₄' z‖ ≤ (36/(π²‖z‖²)) * C₄ * exp(2πt)
  have hbound3 : ‖36 / (↑π ^ 2 * ↑z ^ 2) * φ₄' z‖ ≤
      (36 / (π^2 * ‖(z : ℂ)‖^2)) * hb.C₄ * exp (2 * π * z.im) := by
    rw [norm_mul, norm_coeff_36_div_sq (z : ℂ) hz_ne]
    have h := hb.hφ₄ z hz
    calc 36 / (π ^ 2 * ‖(z : ℂ)‖ ^ 2) * ‖φ₄' z‖
        ≤ 36 / (π ^ 2 * ‖(z : ℂ)‖ ^ 2) * (hb.C₄ * exp (2 * π * z.im)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 36 / (π ^ 2 * ‖(z : ℂ)‖ ^ 2) * hb.C₄ * exp (2 * π * z.im) := by ring
  -- Combine bounds
  linarith

/-- Corollary 7.13: S-transform bound for φ₀(i/t) at large t.
    Uses φ₀_S_transform: φ₀(-1/z) = φ₀(z) - 12i/(πz)·φ₂'(z) - 36/(π²z²)·φ₄'(z)
    with z = it, so S•(it) = i/t.

    This gives the 3-term explicit bound without compressing to a single O(t⁻²e^{2πt}). -/
lemma norm_φ₀''_I_div_t_le (hb : PhiBounds) (t : ℝ) (ht : 1 ≤ t) :
    ‖φ₀'' (Complex.I / t)‖ ≤ hb.C₀ * Real.exp (-2 * π * t)
                    + (12 / (π * t)) * hb.C₂
                    + (36 / (π^2 * t^2)) * hb.C₄ * Real.exp (2 * π * t) := by
  have ht_pos : 0 < t := by linarith
  -- Step 1: Rewrite φ₀''(I/t) as φ₀(S•(I*t)) using our helper
  rw [φ₀''_I_div_t_eq t ht_pos]
  -- Step 2: Use the S-transform formula
  rw [φ₀_S_transform]
  set z := mkI_mul_t t ht_pos with hz_def
  -- z = I*t has im = t ≥ 1
  have hz_im : z.im = t := mkI_mul_t_im t ht_pos
  have hz_im_ge : 1 ≤ z.im := by rw [hz_im]; exact ht
  -- Step 3: Apply triangle inequality twice for a - b - c
  have h_tri : ‖φ₀ z - (12 * Complex.I) / (↑π * z) * φ₂' z - 36 / (↑π ^ 2 * ↑z ^ 2) * φ₄' z‖
      ≤ ‖φ₀ z‖ + ‖(12 * Complex.I) / (↑π * z) * φ₂' z‖
          + ‖36 / (↑π ^ 2 * ↑z ^ 2) * φ₄' z‖ := by
    have h1 : ‖φ₀ z - (12 * Complex.I) / (↑π * z) * φ₂' z - 36 / (↑π ^ 2 * ↑z ^ 2) * φ₄' z‖
        ≤ ‖φ₀ z - (12 * Complex.I) / (↑π * z) * φ₂' z‖
            + ‖36 / (↑π ^ 2 * ↑z ^ 2) * φ₄' z‖ := norm_sub_le _ _
    have h2 : ‖φ₀ z - (12 * Complex.I) / (↑π * z) * φ₂' z‖
        ≤ ‖φ₀ z‖ + ‖(12 * Complex.I) / (↑π * z) * φ₂' z‖ := norm_sub_le _ _
    linarith
  refine h_tri.trans ?_
  -- Step 4: Bound each of the three terms
  have hz_ne : (z : ℂ) ≠ 0 := ne_zero z
  have hz_norm : ‖(z : ℂ)‖ = t := by
    simp only [hz_def, mkI_mul_t]
    exact norm_I_mul_t t ht_pos
  -- Bound (i): ‖φ₀ z‖ ≤ C₀ * exp(-2πt)  [from hb.hφ₀]
  have hbound1 : ‖φ₀ z‖ ≤ hb.C₀ * exp (-2 * π * t) := by
    have h := hb.hφ₀ z hz_im_ge
    rwa [hz_im] at h
  -- Bound (ii): ‖(12I)/(πz) * φ₂' z‖ ≤ (12/(πt)) * C₂
  have hbound2 : ‖(12 * Complex.I) / (↑π * z) * φ₂' z‖ ≤ (12 / (π * t)) * hb.C₂ := by
    rw [norm_mul, norm_coeff_12I_div (z : ℂ) hz_ne, hz_norm]
    exact mul_le_mul_of_nonneg_left (hb.hφ₂ z hz_im_ge) (by positivity)
  -- Bound (iii): ‖36/(π²z²) * φ₄' z‖ ≤ (36/(π²t²)) * C₄ * exp(2πt)
  have hbound3 : ‖36 / (↑π ^ 2 * ↑z ^ 2) * φ₄' z‖ ≤
      (36 / (π^2 * t^2)) * hb.C₄ * exp (2 * π * t) := by
    rw [norm_mul, norm_coeff_36_div_sq (z : ℂ) hz_ne, hz_norm]
    have h := hb.hφ₄ z hz_im_ge
    rw [hz_im] at h
    calc 36 / (π ^ 2 * t ^ 2) * ‖φ₄' z‖
        ≤ 36 / (π ^ 2 * t ^ 2) * (hb.C₄ * exp (2 * π * t)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 36 / (π ^ 2 * t ^ 2) * hb.C₄ * exp (2 * π * t) := by ring
  -- Combine bounds
  linarith

/-! ## Vertical Ray Integrand -/

/-- Vertical ray integrand at horizontal position x.
    Covers #229's edges at x = -1, 0, 1.

    Note: The integrand for vertical contours in the rectangle proof uses
    φ₀''(i/t) rather than φ₀''(it) due to the parameterization. -/
def verticalIntegrandX (x r t : ℝ) : ℂ :=
  Complex.I * φ₀'' (Complex.I / t) * (Complex.I * t)^2 *
    Complex.exp (Complex.I * π * r * (x + Complex.I * t))

/-- Special case x = 0. -/
def verticalIntegrand (r t : ℝ) : ℂ := verticalIntegrandX 0 r t

/-- The exponential phase factor has norm independent of x. -/
lemma norm_cexp_verticalPhase (x r t : ℝ) :
    ‖Complex.exp (Complex.I * π * r * (x + Complex.I * t))‖ = Real.exp (-π * r * t) := by
  rw [Complex.norm_exp]
  congr 1
  -- Goal: (I * π * r * (x + I * t)).re = -π * r * t
  have h1 : Complex.I * ↑π * ↑r * (↑x + Complex.I * ↑t) =
            Complex.I * (π * r * x) + Complex.I * Complex.I * (π * r * t) := by ring
  rw [h1, Complex.I_mul_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
             Complex.ofReal_re, Complex.ofReal_im, neg_one_mul, Complex.neg_re,
             Complex.mul_im]
  ring

/-! ## Integrability (complex-valued) -/

/-- Norm of the vertical integrand. -/
lemma norm_verticalIntegrandX (x r t : ℝ) (ht : 0 < t) :
    ‖verticalIntegrandX x r t‖ = t^2 * ‖φ₀'' (Complex.I / t)‖ * Real.exp (-π * r * t) := by
  simp only [verticalIntegrandX]
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul]
  rw [norm_cexp_verticalPhase]
  -- ‖(I*t)^2‖ = ‖-t^2‖ = t^2
  have h1 : ‖(Complex.I * ↑t : ℂ)^2‖ = t^2 := by
    have ht_abs : |t| = t := abs_of_pos ht
    simp only [sq, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, ht_abs]
    ring
  rw [h1]
  ring

/-- Bounding function for the vertical integrand norm.
    Uses the 3-term Cor 7.13 bound with t² · exp(-πrt) distributed. -/
def verticalBound (hb : PhiBounds) (r t : ℝ) : ℝ :=
  hb.C₀ * t^2 * Real.exp (-(2 * π + π * r) * t)
  + (12 * hb.C₂ / π) * t * Real.exp (-π * r * t)
  + (36 * hb.C₄ / π^2) * Real.exp (-(π * r - 2 * π) * t)

/-- The vertical bound dominates the integrand norm for t ≥ 1. -/
lemma norm_verticalIntegrandX_le (hb : PhiBounds) (x r t : ℝ) (ht : 1 ≤ t) :
    ‖verticalIntegrandX x r t‖ ≤ verticalBound hb r t := by
  have ht_pos : 0 < t := by linarith
  rw [norm_verticalIntegrandX x r t ht_pos]
  -- Apply Cor 7.13 bound: ‖φ₀''(I/t)‖ ≤ 3-term bound
  have hbound := norm_φ₀''_I_div_t_le hb t ht
  -- Need: t² * ‖φ₀''(I/t)‖ * exp(-πrt) ≤ verticalBound
  calc t^2 * ‖φ₀'' (Complex.I / ↑t)‖ * Real.exp (-π * r * t)
      ≤ t^2 * (hb.C₀ * Real.exp (-2 * π * t)
               + (12 / (π * t)) * hb.C₂
               + (36 / (π^2 * t^2)) * hb.C₄ * Real.exp (2 * π * t))
          * Real.exp (-π * r * t) := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left hbound (sq_nonneg t)
        · exact (Real.exp_pos _).le
    _ = verticalBound hb r t := by
        simp only [verticalBound]
        have hπ : π ≠ 0 := Real.pi_ne_zero
        have ht_ne : t ≠ 0 := ne_of_gt ht_pos
        have ht2_ne : t^2 ≠ 0 := pow_ne_zero 2 ht_ne
        -- Expand and distribute
        have hexp := Real.exp_pos (-π * r * t)
        have hπ_pos := Real.pi_pos
        -- Use calc to break down the equality term by term
        have term1 : t^2 * (hb.C₀ * Real.exp (-2 * π * t)) * Real.exp (-π * r * t)
            = hb.C₀ * t^2 * Real.exp (-(2 * π + π * r) * t) := by
          have hexp1 : Real.exp (-2 * π * t) * Real.exp (-π * r * t) =
              Real.exp (-(2 * π + π * r) * t) := by rw [← Real.exp_add]; ring_nf
          calc t^2 * (hb.C₀ * Real.exp (-2 * π * t)) * Real.exp (-π * r * t)
             = hb.C₀ * t^2 * (Real.exp (-2 * π * t) * Real.exp (-π * r * t)) := by ring
           _ = hb.C₀ * t^2 * Real.exp (-(2 * π + π * r) * t) := by rw [hexp1]
        have term2 : t^2 * ((12 / (π * t)) * hb.C₂) * Real.exp (-π * r * t)
            = (12 * hb.C₂ / π) * t * Real.exp (-π * r * t) := by
          field_simp
        have term3 : t^2 * ((36 / (π^2 * t^2)) * hb.C₄ * Real.exp (2 * π * t))
            * Real.exp (-π * r * t)
            = (36 * hb.C₄ / π^2) * Real.exp (-(π * r - 2 * π) * t) := by
          have hexp3 : Real.exp (2 * π * t) * Real.exp (-π * r * t) =
              Real.exp (-(π * r - 2 * π) * t) := by rw [← Real.exp_add]; ring_nf
          calc t^2 * ((36 / (π^2 * t^2)) * hb.C₄ * Real.exp (2 * π * t))
                 * Real.exp (-π * r * t)
             = (36 * hb.C₄ / (π^2 * t^2)) * t^2
                 * (Real.exp (2 * π * t) * Real.exp (-π * r * t)) := by ring
           _ = (36 * hb.C₄ / (π^2 * t^2)) * t^2 * Real.exp (-(π * r - 2 * π) * t) := by
               rw [hexp3]
           _ = (36 * hb.C₄ / π^2) * Real.exp (-(π * r - 2 * π) * t) := by
               field_simp
        -- Combine
        calc t^2 * (hb.C₀ * Real.exp (-2 * π * t) + (12 / (π * t)) * hb.C₂
               + (36 / (π^2 * t^2)) * hb.C₄ * Real.exp (2 * π * t))
             * Real.exp (-π * r * t)
           = t^2 * (hb.C₀ * Real.exp (-2 * π * t)) * Real.exp (-π * r * t)
             + t^2 * ((12 / (π * t)) * hb.C₂) * Real.exp (-π * r * t)
             + t^2 * ((36 / (π^2 * t^2)) * hb.C₄ * Real.exp (2 * π * t))
                 * Real.exp (-π * r * t) := by ring
         _ = hb.C₀ * t^2 * Real.exp (-(2 * π + π * r) * t)
             + (12 * hb.C₂ / π) * t * Real.exp (-π * r * t)
             + (36 * hb.C₄ / π^2) * Real.exp (-(π * r - 2 * π) * t) := by
             rw [term1, term2, term3]

/-- The vertical bound is integrable on [1,∞) for r > 2. -/
lemma integrableOn_verticalBound (hb : PhiBounds) (r : ℝ) (hr : 2 < r) :
    IntegrableOn (verticalBound hb r) (Ici 1) volume := by
  -- Sum of three integrable functions
  have h1 : 0 < 2 * π + π * r := by nlinarith [Real.pi_pos]
  have h2 : 0 < π * r := by nlinarith [Real.pi_pos]
  have h3 : 0 < π * r - 2 * π := by nlinarith [Real.pi_pos]
  -- Define integrable components (note: const_mul applies on the left as c * f(x))
  have i1 : IntegrableOn (fun s => hb.C₀ * (s^2 * Real.exp (-(2 * π + π * r) * s)))
      (Ici 1) volume :=
    (_root_.integrableOn_sq_mul_exp_neg_Ici (2 * π + π * r) h1).const_mul _
  have i2 : IntegrableOn (fun s => (12 * hb.C₂ / π) * (s * Real.exp (-(π * r) * s)))
      (Ici 1) volume :=
    (_root_.integrableOn_mul_exp_neg_Ici (π * r) h2).const_mul _
  have i3 : IntegrableOn (fun s => (36 * hb.C₄ / π^2) * Real.exp (-(π * r - 2 * π) * s))
      (Ici 1) volume :=
    (_root_.integrableOn_exp_mul_Ici (-(π * r - 2 * π)) (by linarith)).const_mul _
  -- Show functions are equal then combine
  have heq : verticalBound hb r = (fun s => hb.C₀ * (s^2 * Real.exp (-(2 * π + π * r) * s)))
       + (fun s => (12 * hb.C₂ / π) * (s * Real.exp (-(π * r) * s)))
       + (fun s => (36 * hb.C₄ / π^2) * Real.exp (-(π * r - 2 * π) * s)) := by
    funext s
    simp only [verticalBound, Pi.add_apply]
    ring_nf
  rw [heq]
  exact (i1.add i2).add i3

/-- Vertical ray integrand is integrable on [1,∞) for r > 2. -/
lemma integrableOn_verticalIntegrandX (hb : PhiBounds) (x r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t => verticalIntegrandX x r t) (Ici 1) volume := by
  -- Bound by verticalBound and use integrability of the bound
  apply MeasureTheory.Integrable.mono' (integrableOn_verticalBound hb r hr)
  · -- Measurability: verticalIntegrandX is measurable (needs continuity of φ₀'')
    -- TODO: Add Continuous.aestronglyMeasurable once continuous_φ₀'' is proved
    sorry
  · rw [ae_restrict_iff' measurableSet_Ici]
    apply ae_of_all
    intro t ht
    simp only [mem_Ici] at ht
    exact norm_verticalIntegrandX_le hb x r t ht

/-- Corollary: norm is also integrable. -/
lemma integrableOn_norm_verticalIntegrandX (hb : PhiBounds) (x r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t => ‖verticalIntegrandX x r t‖) (Ici 1) volume :=
  (integrableOn_verticalIntegrandX hb x r hr).norm

/-! ## Tendsto at Infinity (Proposition 7.14) -/

/-- The vertical bound → 0 as t → ∞ for r > 2. -/
lemma tendsto_verticalBound_atTop (hb : PhiBounds) (r : ℝ) (hr : 2 < r) :
    Tendsto (verticalBound hb r) atTop (𝓝 0) := by
  have h1 : 0 < 2 * π + π * r := by nlinarith [Real.pi_pos]
  have h2 : 0 < π * r := by nlinarith [Real.pi_pos]
  have h3 : 0 < π * r - 2 * π := by nlinarith [Real.pi_pos]
  -- Each term tends to 0
  have t1 : Tendsto (fun s => hb.C₀ * s^2 * Real.exp (-(2 * π + π * r) * s)) atTop (𝓝 0) := by
    have := (_root_.tendsto_sq_mul_exp_neg_atTop (2 * π + π * r) h1).const_mul hb.C₀
    simp only [mul_zero] at this
    convert this using 1
    funext s; ring
  have t2 : Tendsto (fun s => (12 * hb.C₂ / π) * s * Real.exp (-(π * r) * s)) atTop (𝓝 0) := by
    have := (_root_.tendsto_mul_exp_neg_atTop (π * r) h2).const_mul (12 * hb.C₂ / π)
    simp only [mul_zero] at this
    convert this using 1
    funext s; ring
  have t3 : Tendsto (fun s => (36 * hb.C₄ / π^2) * Real.exp (-(π * r - 2 * π) * s))
      atTop (𝓝 0) := by
    have := (_root_.tendsto_exp_neg_atTop (π * r - 2 * π) h3).const_mul (36 * hb.C₄ / π^2)
    simp only [mul_zero] at this
    exact this
  -- Combine
  have hsum : Tendsto (fun s => hb.C₀ * s^2 * Real.exp (-(2 * π + π * r) * s)
      + (12 * hb.C₂ / π) * s * Real.exp (-(π * r) * s)
      + (36 * hb.C₄ / π^2) * Real.exp (-(π * r - 2 * π) * s)) atTop (𝓝 0) := by
    convert (t1.add t2).add t3 using 1
    simp only [add_zero]
  convert hsum using 1
  funext s
  simp only [verticalBound]
  ring_nf

/-- Vertical integrand → 0 as t → ∞ for r > 2. -/
lemma tendsto_verticalIntegrandX_atTop (hb : PhiBounds) (x r : ℝ) (hr : 2 < r) :
    Tendsto (fun t => verticalIntegrandX x r t) atTop (𝓝 0) := by
  -- Use squeeze theorem: ‖f(t)‖ ≤ g(t) → 0 implies f(t) → 0
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  -- Get N such that verticalBound < ε for t ≥ N
  have htendsto := tendsto_verticalBound_atTop hb r hr
  rw [Metric.tendsto_atTop] at htendsto
  obtain ⟨N₁, hN₁⟩ := htendsto ε hε
  -- Use max(N₁, 1) to ensure we can apply norm_verticalIntegrandX_le
  use max N₁ 1
  intro t ht
  have ht_ge_1 : 1 ≤ t := le_of_max_le_right ht
  have ht_ge_N₁ : t ≥ N₁ := le_of_max_le_left ht
  simp only [dist_zero_right]
  -- ‖integrand‖ ≤ bound < ε
  calc ‖verticalIntegrandX x r t‖
      ≤ verticalBound hb r t := norm_verticalIntegrandX_le hb x r t ht_ge_1
    _ < ε := by
        have := hN₁ t ht_ge_N₁
        simp only [dist_zero_right, Real.norm_eq_abs] at this
        have hbound_pos : 0 ≤ verticalBound hb r t := by
          simp only [verticalBound]
          have hp := Real.pi_pos
          have ht_pos : 0 < t := by linarith
          refine add_nonneg (add_nonneg ?_ ?_) ?_
          · exact mul_nonneg (mul_nonneg (le_of_lt hb.hC₀_pos) (sq_nonneg t))
                (le_of_lt (Real.exp_pos _))
          · apply mul_nonneg _ (le_of_lt (Real.exp_pos _))
            apply mul_nonneg (div_nonneg (by linarith [hb.hC₂_pos]) (le_of_lt hp))
            linarith
          · exact mul_nonneg (div_nonneg (by linarith [hb.hC₄_pos]) (sq_nonneg π))
                (le_of_lt (Real.exp_pos _))
        rwa [abs_of_nonneg hbound_pos] at this

/-! ## Top Edge Integral → 0 -/

/-- Top edge integrand for the S-transformed function.
    The actual integrand in the rectangle deformation is φ₀(-1/z) · z² · exp(πir²z)
    where z = x + iT. Note: φ₀''(-1/z) = φ₀(S•z) when z is in ℍ. -/
def topEdgeIntegrand (r x T : ℝ) : ℂ :=
  φ₀'' (-1 / (↑x + Complex.I * ↑T)) * (↑x + Complex.I * ↑T)^2 *
    Complex.exp (Complex.I * π * r * (↑x + Complex.I * ↑T))

/-- Norm of z = x + iT when x ∈ [-1,1] and T ≥ 1. -/
lemma norm_x_add_I_mul_T_bounds (x T : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) (hT : 1 ≤ T) :
    T ≤ ‖(↑x + Complex.I * ↑T : ℂ)‖ ∧ ‖(↑x + Complex.I * ↑T : ℂ)‖ ≤ 1 + T := by
  constructor
  · -- Lower bound: ‖z‖ ≥ |Im(z)| = T
    have hT_pos : 0 < T := by linarith
    have hre : (↑x + Complex.I * ↑T : ℂ).re = x := by simp
    have him : (↑x + Complex.I * ↑T : ℂ).im = T := by simp
    rw [Complex.norm_eq_sqrt_sq_add_sq, hre, him]
    calc T = Real.sqrt (T^2) := (Real.sqrt_sq (le_of_lt hT_pos)).symm
      _ ≤ Real.sqrt (x^2 + T^2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
  · -- Upper bound: ‖z‖ ≤ |x| + |T| ≤ 1 + T
    simp only [mem_Icc] at hx
    calc ‖(↑x + Complex.I * ↑T : ℂ)‖
        ≤ ‖(↑x : ℂ)‖ + ‖Complex.I * ↑T‖ := norm_add_le _ _
      _ = |x| + |T| := by simp [Complex.norm_real, Complex.norm_I, Real.norm_eq_abs]
      _ ≤ 1 + T := by
          have hx_abs : |x| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
          have hT_abs : |T| = T := abs_of_pos (by linarith)
          linarith

/-- Top horizontal edge integral vanishes as height T → ∞.
    This is the "integrand at i∞ disappears" fact from Proposition 7.14.

    The integrand involves φ₀(-1/z) = φ₀(S•z), not φ₀(z) directly.
    For z = x + iT with T large, the S-transform bound gives exponential decay. -/
lemma tendsto_topEdgeIntegral_zero (hb : PhiBounds) (r : ℝ) (hr : 2 < r) :
    Tendsto (fun (T : ℝ) => ∫ x : ℝ in Icc (-1 : ℝ) 1, topEdgeIntegrand r x T)
    atTop (𝓝 0) := by
  -- Strategy: Uniform bound + squeeze theorem
  -- For z = x + iT with x ∈ [-1,1] and T ≥ 1:
  -- 1. ‖z‖ ≥ T (since im(z) = T), so 1/‖z‖ ≤ 1/T and 1/‖z‖² ≤ 1/T²
  -- 2. ‖z‖ ≤ 1 + T (by triangle inequality)
  -- 3. Use norm_φ₀_S_smul_le to bound ‖φ₀''(-1/z)‖ (since S•z = -1/z)
  -- 4. The exp factor has norm exp(-πrT)
  -- 5. Combine to get ‖topEdgeIntegrand‖ ≤ G(T) uniformly in x, where G(T) → 0
  -- 6. Then ‖∫₋₁¹ topEdgeIntegrand dx‖ ≤ 2 · G(T) → 0
  --
  -- Key bounds (for T ≥ 1, x ∈ [-1,1]):
  -- - ‖z²‖ ≤ (1+T)² (from upper bound on ‖z‖)
  -- - ‖exp(iπrz)‖ = exp(-πrT) (exponential decay in T)
  -- - ‖φ₀''(-1/z)‖ ≤ C₀ exp(-2πT) + (12C₂/πT) + (36C₄/π²T²) exp(2πT)
  --     (from norm_φ₀_S_smul_le with z having im = T ≥ 1)
  --
  -- The dominant term for large T is:
  --   (1+T)² · exp(-πrT) · (36C₄/π²T²) · exp(2πT)
  --   = O((1+T)² · T⁻² · exp(-(πr-2π)T))
  --   = O(exp(-(πr-2π)T)) since πr - 2π > 0 when r > 2
  --
  -- Full proof requires: continuity of integrand for Bochner integral,
  -- measurability, uniform bounds, and combining via tendsto_of_norm_tendsto.
  sorry

end MagicFunction.ContourEndpoints

end
