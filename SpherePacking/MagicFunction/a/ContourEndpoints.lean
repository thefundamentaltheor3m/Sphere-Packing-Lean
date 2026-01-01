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

/-- Vertical ray integrand is integrable on [1,∞) for r > 2. -/
lemma integrableOn_verticalIntegrandX (hb : PhiBounds) (x r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t => verticalIntegrandX x r t) (Ici 1) volume := by
  -- Strategy: bound the norm and show it's dominated by an integrable function
  -- ‖verticalIntegrandX x r t‖ = t² * ‖φ₀''(I/t)‖ * exp(-πrt)
  -- Using the 3-term bound on ‖φ₀''(I/t)‖, we get terms that are all integrable for r > 2:
  -- Term 1: t² * C₀ * exp(-2πt) * exp(-πrt) = C₀ * t² * exp(-(2π+πr)t)
  -- Term 2: t² * (12/(πt)) * C₂ * exp(-πrt) = (12C₂/π) * t * exp(-πrt)
  -- Term 3: t² * (36/(π²t²)) * C₄ * exp(2πt) * exp(-πrt) = (36C₄/π²) * exp(-(πr-2π)t)
  -- All integrable since 2π+πr > 0, πr > 0, and πr-2π > 0 when r > 2
  have h_decay : π * r - 2 * π > 0 := by nlinarith [Real.pi_pos]
  sorry

/-- Corollary: norm is also integrable. -/
lemma integrableOn_norm_verticalIntegrandX (hb : PhiBounds) (x r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t => ‖verticalIntegrandX x r t‖) (Ici 1) volume :=
  (integrableOn_verticalIntegrandX hb x r hr).norm

/-! ## Tendsto at Infinity (Proposition 7.14) -/

/-- Vertical integrand → 0 as t → ∞ for r > 2. -/
lemma tendsto_verticalIntegrandX_atTop (hb : PhiBounds) (x r : ℝ) (hr : 2 < r) :
    Tendsto (fun t => verticalIntegrandX x r t) atTop (𝓝 0) := by
  sorry

/-! ## Top Edge Integral → 0 -/

/-- Top edge integrand for the S-transformed function.
    The actual integrand in the rectangle deformation is φ₀(-1/z) · z² · exp(πir²z)
    where z = x + iT. Note: φ₀''(-1/z) = φ₀(S•z) when z is in ℍ. -/
def topEdgeIntegrand (r x T : ℝ) : ℂ :=
  φ₀'' (-1 / (↑x + Complex.I * ↑T)) * (↑x + Complex.I * ↑T)^2 *
    Complex.exp (Complex.I * π * r * (↑x + Complex.I * ↑T))

/-- Top horizontal edge integral vanishes as height T → ∞.
    This is the "integrand at i∞ disappears" fact from Proposition 7.14.

    The integrand involves φ₀(-1/z) = φ₀(S•z), not φ₀(z) directly.
    For z = x + iT with T large, the S-transform bound gives exponential decay. -/
lemma tendsto_topEdgeIntegral_zero (hb : PhiBounds) (r : ℝ) (hr : 2 < r) :
    Tendsto (fun (T : ℝ) => ∫ x : ℝ in Icc (-1 : ℝ) 1, topEdgeIntegrand r x T)
    atTop (𝓝 0) := by
  -- Strategy: Uniform bound + squeeze theorem
  -- For z = x + iT with x ∈ [-1,1] and T ≥ 1:
  -- 1. ‖z‖ ≥ T (since im(z) = T)
  -- 2. Use norm_φ₀_S_smul_le to bound φ₀(-1/z)
  -- 3. The exponential decay from exp(πir²z) dominates
  -- 4. Uniformly bound ‖F(x,T)‖ ≤ G(T) where G(T) → 0
  -- 5. Then ‖∫ F(x,T) dx‖ ≤ 2 · G(T) → 0
  sorry

end MagicFunction.ContourEndpoints

end
