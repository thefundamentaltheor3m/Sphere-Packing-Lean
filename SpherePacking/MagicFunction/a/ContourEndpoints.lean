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
  -- This requires showing:
  -- (i) ‖φ₀ z‖ ≤ C₀ * exp(-2πt)  [from hb.hφ₀]
  -- (ii) ‖(12I)/(πz) * φ₂' z‖ ≤ (12/(πt)) * C₂
  -- (iii) ‖36/(π²z²) * φ₄' z‖ ≤ (36/(π²t²)) * C₄ * exp(2πt)
  sorry

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

/-- Vertical ray integrand is integrable on [1,∞) for r > 2. -/
lemma integrableOn_verticalIntegrandX (hb : PhiBounds) (x r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t => verticalIntegrandX x r t) (Ici 1) volume := by
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

/-- Top horizontal edge integral vanishes as height T → ∞.
    This is the "integrand at i∞ disappears" fact from Proposition 7.14. -/
lemma tendsto_topEdgeIntegral_zero (hb : PhiBounds) (r : ℝ) (hr : 2 < r) :
    Tendsto (fun (T : ℝ) => ∫ x : ℝ in Icc (-1 : ℝ) 1,
      φ₀'' (↑x + Complex.I * ↑T) * (↑x + Complex.I * ↑T)^2 *
        Complex.exp (Complex.I * π * r * (↑x + Complex.I * ↑T)))
    atTop (𝓝 0) := by
  sorry

end MagicFunction.ContourEndpoints

end
