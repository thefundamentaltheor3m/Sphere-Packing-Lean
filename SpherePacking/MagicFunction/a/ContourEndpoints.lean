/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import SpherePacking.ModularForms.PhiTransform
import SpherePacking.MagicFunction.RealDecay
import SpherePacking.MagicFunction.CuspPath
import SpherePacking.MagicFunction.a.PhiBounds
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
open MagicFunction.a (PhiBounds phiBounds)

open scoped Interval Real NNReal ENNReal Topology BigOperators

noncomputable section

namespace MagicFunction.ContourEndpoints

/-! ## Corollary 7.13 - S-transform bound for φ₀''(I/t) -/

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
    rw [Complex.div_ofReal_im, Complex.I_im]; positivity
  rw [φ₀''_eq _ hI_div]
  exact congrArg φ₀ (Subtype.ext (S_smul_I_mul_t t ht).symm)

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
    calc 36 / (π ^ 2 * ‖(z : ℂ)‖ ^ 2) * ‖φ₄' z‖
        ≤ 36 / (π ^ 2 * ‖(z : ℂ)‖ ^ 2) * (hb.C₄ * exp (2 * π * z.im)) :=
          mul_le_mul_of_nonneg_left (hb.hφ₄ z hz) (by positivity)
      _ = 36 / (π ^ 2 * ‖(z : ℂ)‖ ^ 2) * hb.C₄ * exp (2 * π * z.im) := by ring
  -- Combine bounds
  linarith

/-- Corollary 7.13: S-transform bound for φ₀(i/t) at large t.
    Specializes norm_φ₀_S_smul_le to z = I*t where z.im = ‖z‖ = t. -/
lemma norm_φ₀''_I_div_t_le (hb : PhiBounds) (t : ℝ) (ht : 1 ≤ t) :
    ‖φ₀'' (Complex.I / t)‖ ≤ hb.C₀ * Real.exp (-2 * π * t)
                    + (12 / (π * t)) * hb.C₂
                    + (36 / (π^2 * t^2)) * hb.C₄ * Real.exp (2 * π * t) := by
  have ht_pos : 0 < t := by linarith
  rw [φ₀''_I_div_t_eq t ht_pos]
  set z := mkI_mul_t t ht_pos
  have hz_im : z.im = t := mkI_mul_t_im t ht_pos
  have hz_norm : ‖(z : ℂ)‖ = t := norm_I_mul_t t ht_pos
  have hz_im_ge : 1 ≤ z.im := by rw [hz_im]; exact ht
  have h := norm_φ₀_S_smul_le hb z hz_im_ge
  simp only [hz_im, hz_norm] at h
  exact h

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
        have ht_ne : t ≠ 0 := ne_of_gt ht_pos
        have hexp1 : Real.exp (-2 * π * t) * Real.exp (-π * r * t) =
            Real.exp (-(2 * π + π * r) * t) := by rw [← Real.exp_add]; ring_nf
        have hexp3 : Real.exp (2 * π * t) * Real.exp (-π * r * t) =
            Real.exp (-(π * r - 2 * π) * t) := by rw [← Real.exp_add]; ring_nf
        calc t^2 * (hb.C₀ * Real.exp (-2 * π * t) + (12 / (π * t)) * hb.C₂
               + (36 / (π^2 * t^2)) * hb.C₄ * Real.exp (2 * π * t))
             * Real.exp (-π * r * t)
           = hb.C₀ * t^2 * (Real.exp (-2 * π * t) * Real.exp (-π * r * t))
             + (12 * hb.C₂ / π) * t * Real.exp (-π * r * t)
             + (36 * hb.C₄ / π^2) * (Real.exp (2 * π * t) * Real.exp (-π * r * t)) := by
               field_simp
         _ = hb.C₀ * t^2 * Real.exp (-(2 * π + π * r) * t)
             + (12 * hb.C₂ / π) * t * Real.exp (-π * r * t)
             + (36 * hb.C₄ / π^2) * Real.exp (-(π * r - 2 * π) * t) := by
               rw [hexp1, hexp3]

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
  · -- Measurability: verticalIntegrandX is continuous on Ici 1 → AEStronglyMeasurable
    -- Use neg_one_div_I_mul: I/t = -1/(I*t) for t ≠ 0
    have h_cont_phi : ContinuousOn (fun t : ℝ => φ₀'' (Complex.I / t)) (Ici 1) := by
      have h1 := continuousOn_φ₀''_cusp_path.mono
        (fun t ht => lt_of_lt_of_le zero_lt_one (mem_Ici.mp ht))
      refine h1.congr (fun t ht => ?_)
      have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one (mem_Ici.mp ht)
      exact congrArg φ₀'' (neg_one_div_I_mul t (ne_of_gt ht_pos)).symm
    have h_cont : ContinuousOn (fun t : ℝ => verticalIntegrandX x r t) (Ici 1) := by
      unfold verticalIntegrandX
      refine ((continuousOn_const.mul h_cont_phi).mul ?_).mul ?_
      · exact (continuousOn_const.mul Complex.continuous_ofReal.continuousOn).pow _
      · refine Complex.continuous_exp.comp_continuousOn ?_
        refine (continuousOn_const.mul continuousOn_const).mul ?_
        exact continuousOn_const.add
          (continuousOn_const.mul Complex.continuous_ofReal.continuousOn)
    exact h_cont.aestronglyMeasurable measurableSet_Ici
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

/-- S action on x + iT gives -1/(x + iT).
    This is a restatement of `modular_S_smul` with explicit computation. -/
lemma S_smul_x_add_I_mul_T (x T : ℝ) (hT : 0 < T) :
    let w : ℍ := ⟨↑x + Complex.I * ↑T, by simp; exact hT⟩
    (↑(ModularGroup.S • w) : ℂ) = -1 / (↑x + Complex.I * ↑T) := by
  -- S•z = -z⁻¹ for z ∈ ℍ, and -z⁻¹ = -1/z
  simp only [modular_S_smul, UpperHalfPlane.coe_mk_subtype]
  -- Goal: ↑(mk ((-z)⁻¹) ...) = -1/z where z = x + iT
  simp only [UpperHalfPlane.coe_mk]
  -- Goal: (-z)⁻¹ = -1/z, which equals -(z⁻¹) = -(z⁻¹) by neg_inv
  rw [← neg_inv]
  ring

/-- φ₀''(-1/z) equals φ₀(S•w) where w = ⟨z, _⟩ ∈ ℍ.
    This connects the extension φ₀'' on ℂ to the original φ₀ on ℍ via S-transform. -/
lemma φ₀''_neg_inv_eq_φ₀_S_smul (x T : ℝ) (hT : 0 < T) :
    let z : ℂ := ↑x + Complex.I * ↑T
    let w : ℍ := ⟨z, by simp only [z]; simp; exact hT⟩
    φ₀'' (-1 / z) = φ₀ (ModularGroup.S • w) := by
  intro z w
  have hneg_inv_im : 0 < (-1 / z : ℂ).im := by
    simp only [z, neg_div, one_div, neg_inv]
    exact UpperHalfPlane.im_inv_neg_coe_pos ⟨_, by simp [Complex.add_im]; exact hT⟩
  rw [φ₀''_eq _ hneg_inv_im]
  exact congrArg φ₀ (Subtype.ext (S_smul_x_add_I_mul_T x T hT).symm)

/-- Bounding function for top edge integrand norm.
    For z = x + iT with x ∈ [-1,1] and T ≥ 1, this bounds ‖topEdgeIntegrand r x T‖. -/
def topEdgeBound (hb : PhiBounds) (r T : ℝ) : ℝ :=
  (1 + T)^2 * Real.exp (-π * r * T) *
    (hb.C₀ * Real.exp (-2 * π * T) + (12 * hb.C₂ / (π * T)) + (36 * hb.C₄ / (π^2 * T^2))
        * Real.exp (2 * π * T))

/-- The top edge bound → 0 as T → ∞ for r > 2. -/
lemma tendsto_topEdgeBound_atTop (hb : PhiBounds) (r : ℝ) (hr : 2 < r) :
    Tendsto (topEdgeBound hb r) atTop (𝓝 0) := by
  unfold topEdgeBound
  have hπ := Real.pi_pos
  have h1 : 0 < π * r + 2 * π := by nlinarith
  have h2 : 0 < π * r := by nlinarith
  have h3 : 0 < π * r - 2 * π := by nlinarith
  -- Strategy: Expand (1+T)² = 1 + 2T + T² and use individual tendsto lemmas
  -- Term 1: C₀ * (1+T)² * exp(-(πr+2π)T) → 0
  have t1 : Tendsto (fun T => hb.C₀ * (1 + T)^2 * Real.exp (-(π * r + 2 * π) * T))
      atTop (𝓝 0) := by
    -- Expand: (1+T)² = 1 + 2T + T²
    have t1a : Tendsto (fun T => hb.C₀ * Real.exp (-(π * r + 2 * π) * T)) atTop (𝓝 0) := by
      have h := (_root_.tendsto_exp_neg_atTop (π * r + 2 * π) h1).const_mul hb.C₀
      simp only [mul_zero] at h; exact h
    have t1b : Tendsto (fun T => 2 * hb.C₀ * T * Real.exp (-(π * r + 2 * π) * T))
        atTop (𝓝 0) := by
      have h := (_root_.tendsto_mul_exp_neg_atTop (π * r + 2 * π) h1).const_mul (2 * hb.C₀)
      simp only [mul_zero] at h
      convert h using 1; funext T; ring
    have t1c : Tendsto (fun T => hb.C₀ * T^2 * Real.exp (-(π * r + 2 * π) * T))
        atTop (𝓝 0) := by
      have h := (_root_.tendsto_sq_mul_exp_neg_atTop (π * r + 2 * π) h1).const_mul hb.C₀
      simp only [mul_zero] at h
      convert h using 1; funext T; ring
    have hsum := (t1a.add t1b).add t1c
    simp only [add_zero] at hsum
    convert hsum using 1
    funext T; ring
  -- Term 2: (12C₂/(πT)) * (1+T)² * exp(-πrT) → 0
  -- Use squeeze: (1+T)²/T ≤ 4T for T ≥ 1
  have t2 : Tendsto (fun T => (12 * hb.C₂ / (π * T)) * (1 + T)^2 * Real.exp (-π * r * T))
      atTop (𝓝 0) := by
    have hbound : Tendsto (fun T => (48 * hb.C₂ / π) * T * Real.exp (-π * r * T))
        atTop (𝓝 0) := by
      have h := (_root_.tendsto_mul_exp_neg_atTop (π * r) h2).const_mul (48 * hb.C₂ / π)
      simp only [mul_zero] at h
      convert h using 1; funext T; ring_nf
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop 1] with T hT
      have hT_pos : 0 < T := by linarith
      apply mul_nonneg (mul_nonneg _ (sq_nonneg _)) (le_of_lt (Real.exp_pos _))
      exact div_nonneg (by linarith [hb.hC₂_pos]) (by positivity)
    · filter_upwards [eventually_ge_atTop 1] with T hT
      have hT_pos : 0 < T := by linarith
      have hπT_pos : 0 < π * T := by positivity
      have h1 : (12 * hb.C₂ / (π * T)) * (1 + T)^2 = (12 * hb.C₂ / π) * ((1 + T)^2 / T) := by
        field_simp
      have h2 : (1 + T)^2 / T = 1 / T + 2 + T := by field_simp; ring
      have h3 : 1 / T + 2 + T ≤ 4 * T := by
        have : 1 / T ≤ 1 := by rw [div_le_one hT_pos]; exact hT
        linarith
      calc (12 * hb.C₂ / (π * T)) * (1 + T)^2 * Real.exp (-π * r * T)
          = (12 * hb.C₂ / π) * (1 / T + 2 + T) * Real.exp (-π * r * T) := by
              rw [h1, h2]
        _ ≤ (12 * hb.C₂ / π) * (4 * T) * Real.exp (-π * r * T) := by
            apply mul_le_mul_of_nonneg_right
            · apply mul_le_mul_of_nonneg_left h3
              exact div_nonneg (by linarith [hb.hC₂_pos]) (le_of_lt hπ)
            · exact le_of_lt (Real.exp_pos _)
        _ = (48 * hb.C₂ / π) * T * Real.exp (-π * r * T) := by ring
    · exact hbound
  -- Term 3: (36C₄/(π²T²)) * (1+T)² * exp(2πT-πrT) → 0
  -- Use squeeze: (1+T)²/T² ≤ 4 for T ≥ 1
  have t3 : Tendsto (fun T => (36 * hb.C₄ / (π^2 * T^2)) * (1 + T)^2 *
      Real.exp (2 * π * T) * Real.exp (-π * r * T)) atTop (𝓝 0) := by
    have hbound : Tendsto (fun T => (144 * hb.C₄ / π^2) * Real.exp (-(π * r - 2 * π) * T))
        atTop (𝓝 0) := by
      have h := (_root_.tendsto_exp_neg_atTop (π * r - 2 * π) h3).const_mul (144 * hb.C₄ / π^2)
      simp only [mul_zero] at h
      exact h
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop 1] with T hT
      have hT_pos : 0 < T := by linarith
      apply mul_nonneg (mul_nonneg (mul_nonneg _ (sq_nonneg _)) (le_of_lt (Real.exp_pos _)))
          (le_of_lt (Real.exp_pos _))
      exact div_nonneg (by linarith [hb.hC₄_pos]) (by positivity)
    · filter_upwards [eventually_ge_atTop 1] with T hT
      have hT_pos : 0 < T := by linarith
      have hexp_comb : Real.exp (2 * π * T) * Real.exp (-π * r * T) =
          Real.exp (-(π * r - 2 * π) * T) := by rw [← Real.exp_add]; ring_nf
      have h1 : (1 + T)^2 / T^2 = (1 / T + 1)^2 := by field_simp
      have hle2 : 1 / T + 1 ≤ 2 := by
        have : 1 / T ≤ 1 := by rw [div_le_one hT_pos]; exact hT
        linarith
      have h2 : (1 / T + 1)^2 ≤ 4 := by
        have h0 : 0 ≤ 1 / T + 1 := by positivity
        calc (1 / T + 1)^2 ≤ 2^2 := by
              apply sq_le_sq' (by linarith) hle2
          _ = 4 := by norm_num
      -- Combine the exponentials and rearrange
      have heq : (36 * hb.C₄ / (π^2 * T^2)) * (1 + T)^2 * Real.exp (2 * π * T) *
          Real.exp (-π * r * T) =
          (36 * hb.C₄ / π^2) * ((1 + T)^2 / T^2) *
          (Real.exp (2 * π * T) * Real.exp (-π * r * T)) := by
        field_simp
      calc (36 * hb.C₄ / (π^2 * T^2)) * (1 + T)^2 * Real.exp (2 * π * T) *
               Real.exp (-π * r * T)
          = (36 * hb.C₄ / π^2) * ((1 + T)^2 / T^2) *
              (Real.exp (2 * π * T) * Real.exp (-π * r * T)) := heq
        _ = (36 * hb.C₄ / π^2) * (1 / T + 1)^2 * Real.exp (-(π * r - 2 * π) * T) := by
              rw [h1, hexp_comb]
        _ ≤ (36 * hb.C₄ / π^2) * 4 * Real.exp (-(π * r - 2 * π) * T) := by
            apply mul_le_mul_of_nonneg_right
            · apply mul_le_mul_of_nonneg_left h2
              exact div_nonneg (by linarith [hb.hC₄_pos]) (sq_nonneg π)
            · exact le_of_lt (Real.exp_pos _)
        _ = (144 * hb.C₄ / π^2) * Real.exp (-(π * r - 2 * π) * T) := by ring
    · exact hbound
  -- Combine by showing function equals sum of three terms
  have heq : ∀ T, (1 + T)^2 * Real.exp (-π * r * T) *
      (hb.C₀ * Real.exp (-2 * π * T) + 12 * hb.C₂ / (π * T) +
       36 * hb.C₄ / (π^2 * T^2) * Real.exp (2 * π * T))
      = hb.C₀ * (1 + T)^2 * Real.exp (-(π * r + 2 * π) * T)
        + (12 * hb.C₂ / (π * T)) * (1 + T)^2 * Real.exp (-π * r * T)
        + (36 * hb.C₄ / (π^2 * T^2)) * (1 + T)^2 * Real.exp (2 * π * T) *
            Real.exp (-π * r * T) := fun T => by
    have hexp1 : Real.exp (-π * r * T) * Real.exp (-2 * π * T) =
        Real.exp (-(π * r + 2 * π) * T) := by rw [← Real.exp_add]; ring_nf
    calc (1 + T)^2 * Real.exp (-π * r * T) *
        (hb.C₀ * Real.exp (-2 * π * T) + 12 * hb.C₂ / (π * T) +
         36 * hb.C₄ / (π^2 * T^2) * Real.exp (2 * π * T))
      = (1 + T)^2 * hb.C₀ * (Real.exp (-π * r * T) * Real.exp (-2 * π * T))
        + (12 * hb.C₂ / (π * T)) * (1 + T)^2 * Real.exp (-π * r * T)
        + (36 * hb.C₄ / (π^2 * T^2)) * (1 + T)^2 * Real.exp (2 * π * T) *
            Real.exp (-π * r * T) := by ring
    _ = hb.C₀ * (1 + T)^2 * Real.exp (-(π * r + 2 * π) * T)
        + (12 * hb.C₂ / (π * T)) * (1 + T)^2 * Real.exp (-π * r * T)
        + (36 * hb.C₄ / (π^2 * T^2)) * (1 + T)^2 * Real.exp (2 * π * T) *
            Real.exp (-π * r * T) := by rw [hexp1]; ring
  simp_rw [heq]
  have hsum := (t1.add t2).add t3
  simp only [add_zero] at hsum
  exact hsum

/-- Uniform bound on top edge integrand for x ∈ [-1,1], T ≥ 1.
    Uses S-transform bound (norm_φ₀_S_smul_le) with ‖z‖ ≥ T.

    Proof strategy:
    1. Show φ₀''(-1/z) = φ₀(S•w) where w = x + iT ∈ ℍ
    2. Apply norm_φ₀_S_smul_le to get 3-term bound
    3. Use ‖z‖ ≥ T to bound 1/‖z‖ terms by 1/T
    4. Combine with ‖z²‖ ≤ (1+T)² and exponential phase norm -/
lemma norm_topEdgeIntegrand_le (hb : PhiBounds) (r : ℝ) (x T : ℝ)
    (hx : x ∈ Icc (-1 : ℝ) 1) (hT : 1 ≤ T) :
    ‖topEdgeIntegrand r x T‖ ≤ topEdgeBound hb r T := by
  -- This proof connects topEdgeIntegrand to the S-transform bound.
  -- The key insight is: φ₀''(-1/z) = φ₀(S•w) where w = ⟨z, _⟩ ∈ ℍ
  have hT_pos : 0 < T := lt_of_lt_of_le one_pos hT
  -- Define z and the upper half plane point w
  let z : ℂ := ↑x + Complex.I * ↑T
  have hz_im : z.im = T := by simp [z]
  have hz_im_pos : 0 < z.im := by rw [hz_im]; exact hT_pos
  let w : ℍ := ⟨z, hz_im_pos⟩
  -- Get the S-transform bound with w.im = T ≥ 1
  have hw_im : w.im = T := hz_im
  have hw_im_ge : 1 ≤ w.im := by rw [hw_im]; exact hT
  -- Get z norm bounds
  have hz_bounds := norm_x_add_I_mul_T_bounds x T hx hT
  have hz_norm_ge : T ≤ ‖z‖ := hz_bounds.1
  have hz_norm_le : ‖z‖ ≤ 1 + T := hz_bounds.2
  have hz_norm_pos : 0 < ‖z‖ := lt_of_lt_of_le hT_pos hz_norm_ge
  -- Step 1: Rewrite φ₀''(-1/z) = φ₀(S•w)
  have hφ₀_eq : φ₀'' (-1 / z) = φ₀ (ModularGroup.S • w) := φ₀''_neg_inv_eq_φ₀_S_smul x T hT_pos
  -- Step 2: Get the S-transform bound
  have hS_bound := norm_φ₀_S_smul_le hb w hw_im_ge
  -- Step 3: Bound the norm of z² and the exponential phase
  have hz_sq_norm : ‖z^2‖ ≤ (1 + T)^2 := by
    rw [norm_pow]
    exact sq_le_sq' (by linarith) hz_norm_le
  have hexp_norm : ‖Complex.exp (Complex.I * π * r * z)‖ = Real.exp (-π * r * T) :=
    norm_cexp_verticalPhase x r T
  -- Step 4: Compute the full norm using triangle inequality
  unfold topEdgeIntegrand topEdgeBound
  simp only [z] at *
  rw [norm_mul, norm_mul, hφ₀_eq, hexp_norm]
  -- Now we need: ‖φ₀(S•w)‖ * ‖z²‖ * exp(-πrT) ≤ topEdgeBound
  -- First bound ‖z²‖ ≤ (1+T)²
  have hz_sq_bound : ‖(↑x + Complex.I * ↑T : ℂ)^2‖ ≤ (1 + T)^2 := hz_sq_norm
  -- Step 5: Rewrite the S-transform bound with 1/T replacing 1/‖z‖ (using ‖z‖ ≥ T)
  have h12_div_le : 12 / (π * ‖(w : ℂ)‖) ≤ 12 / (π * T) := by
    apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 12) (by positivity)
    exact mul_le_mul_of_nonneg_left hz_norm_ge (le_of_lt Real.pi_pos)
  have h36_div_le : 36 / (π^2 * ‖(w : ℂ)‖^2) ≤ 36 / (π^2 * T^2) := by
    apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 36) (by positivity)
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg π)
    exact sq_le_sq₀ (by linarith : 0 ≤ T) (norm_nonneg _) |>.mpr hz_norm_ge
  have hS_bound' : ‖φ₀ (ModularGroup.S • w)‖ ≤
      hb.C₀ * Real.exp (-2 * π * T) + 12 * hb.C₂ / (π * T) +
        36 * hb.C₄ / (π^2 * T^2) * Real.exp (2 * π * T) := by
    calc ‖φ₀ (ModularGroup.S • w)‖
        ≤ hb.C₀ * Real.exp (-2 * π * w.im) + 12 / (π * ‖(w : ℂ)‖) * hb.C₂ +
            36 / (π^2 * ‖(w : ℂ)‖^2) * hb.C₄ * Real.exp (2 * π * w.im) := hS_bound
      _ = hb.C₀ * Real.exp (-2 * π * T) + 12 / (π * ‖(w : ℂ)‖) * hb.C₂ +
            36 / (π^2 * ‖(w : ℂ)‖^2) * hb.C₄ * Real.exp (2 * π * T) := by rw [hw_im]
      _ ≤ hb.C₀ * Real.exp (-2 * π * T) + 12 / (π * T) * hb.C₂ +
            36 / (π^2 * T^2) * hb.C₄ * Real.exp (2 * π * T) := by
          apply add_le_add
          · apply add_le_add le_rfl
            exact mul_le_mul_of_nonneg_right h12_div_le (le_of_lt hb.hC₂_pos)
          · apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
            exact mul_le_mul_of_nonneg_right h36_div_le (le_of_lt hb.hC₄_pos)
      _ = hb.C₀ * Real.exp (-2 * π * T) + 12 * hb.C₂ / (π * T) +
            36 * hb.C₄ / (π^2 * T^2) * Real.exp (2 * π * T) := by ring
  -- Step 7: Combine everything
  have hbound_pos : 0 ≤ hb.C₀ * Real.exp (-2 * π * T) + 12 * hb.C₂ / (π * T) +
      36 * hb.C₄ / (π^2 * T^2) * Real.exp (2 * π * T) := by
    have := hb.hC₀_pos; have := hb.hC₂_pos; have := hb.hC₄_pos
    positivity
  calc ‖φ₀ (ModularGroup.S • w)‖ * ‖(↑x + Complex.I * ↑T)^2‖ * Real.exp (-π * r * T)
      ≤ (hb.C₀ * Real.exp (-2 * π * T) + 12 * hb.C₂ / (π * T) +
          36 * hb.C₄ / (π^2 * T^2) * Real.exp (2 * π * T)) * (1 + T)^2 * Real.exp (-π * r * T) := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
        apply mul_le_mul hS_bound' hz_sq_bound (norm_nonneg _) hbound_pos
    _ = (1 + T)^2 * Real.exp (-π * r * T) *
          (hb.C₀ * Real.exp (-2 * π * T) + 12 * hb.C₂ / (π * T) +
            36 * hb.C₄ / (π^2 * T^2) * Real.exp (2 * π * T)) := by ring

/-- Top horizontal edge integral vanishes as height T → ∞.
    This is the "integrand at i∞ disappears" fact from Proposition 7.14.

    The integrand involves φ₀(-1/z) = φ₀(S•z), not φ₀(z) directly.
    For z = x + iT with T large, the S-transform bound gives exponential decay.

    Strategy: Use squeeze theorem with topEdgeBound
    ‖∫₋₁¹ f(x,T) dx‖ ≤ ∫₋₁¹ ‖f(x,T)‖ dx ≤ 2 * topEdgeBound(T) → 0 -/
lemma tendsto_topEdgeIntegral_zero (hb : PhiBounds) (r : ℝ) (hr : 2 < r) :
    Tendsto (fun (T : ℝ) => ∫ x : ℝ in Icc (-1 : ℝ) 1, topEdgeIntegrand r x T)
    atTop (𝓝 0) := by
  -- Strategy: Use tendsto_zero_iff_norm_tendsto_zero + squeeze_zero'
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  -- Lower bound: 0 ≤ ‖∫...‖
  · filter_upwards with T
    exact norm_nonneg _
  -- Upper bound: ‖∫...‖ ≤ 2 * topEdgeBound hb r T for T ≥ 1
  · filter_upwards [eventually_ge_atTop 1] with T hT
    have h_meas : volume (Icc (-1 : ℝ) 1) < ⊤ := measure_Icc_lt_top
    have h_bound : ∀ x ∈ Icc (-1 : ℝ) 1, ‖topEdgeIntegrand r x T‖ ≤ topEdgeBound hb r T :=
      fun x hx => norm_topEdgeIntegrand_le hb r x T hx hT
    calc ‖∫ x in Icc (-1 : ℝ) 1, topEdgeIntegrand r x T‖
        ≤ topEdgeBound hb r T * volume.real (Icc (-1 : ℝ) 1) :=
          norm_setIntegral_le_of_norm_le_const h_meas h_bound
      _ = topEdgeBound hb r T * 2 := by
          rw [Measure.real, Real.volume_Icc]; norm_num
      _ = 2 * topEdgeBound hb r T := mul_comm _ _
  -- Limit: 2 * topEdgeBound hb r T → 0
  · have h := tendsto_topEdgeBound_atTop hb r hr
    convert h.const_mul 2 using 1
    simp

end MagicFunction.ContourEndpoints

end
