/-
Copyright (c) 2026 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
import SpherePacking.MagicFunction.a.ContourEndpoints
import SpherePacking.MagicFunction.Segments
import SpherePacking.ModularForms.PhiTransform
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Vertical Contour Integrability

Integrability and vanishing lemmas for vertical ray integrands involving φ₀.
Provides bounds from Lemmas 4.4.3-4.4.4 of Sid's thesis and general integrability results
needed for Proposition 4.4.6 (the double zeros proof).

## Main results

### Thesis Bounds (Section 4.4.1)
- `norm_φ₀_I_div_t_small`: Lemma 4.4.3 - For t ∈ (0, 2), |φ₀(i/t)| ≤ C₀ e^{-2π/t}
- `norm_φ₀_I_div_t_large`: Lemma 4.4.4 - For t ≥ 2, |φ₀(i/t)| ≤ C t⁻² e^{2πt}

### Integrability Goals (Proposition 4.4.6)
- `integrableOn_goal1` through `integrableOn_goal6`: Six specific integrands

### Vanishing Lemmas (Lemma 4.4.5)
- `tendsto_φ₀_integrand_atImInfty`: Base vanishing as Im(z) → ∞
- `tendsto_φ₀_integrand_plus_one`: Shifted variant for z + 1
- `tendsto_φ₀_integrand_minus_one`: Shifted variant for z - 1

## References

- Sid's M4R Thesis, Section 4.4.1 (Proposition 4.4.6)
- Blueprint Corollaries 7.5-7.7, 7.13
-/

open MeasureTheory Set Filter Real Complex TopologicalSpace

open scoped Interval Real NNReal ENNReal Topology BigOperators

noncomputable section

namespace MagicFunction.VerticalIntegrability

/-! ## Thesis Bounds (Lemmas 4.4.3, 4.4.4)

These bounds are the key to proving convergence of the integral in Definition 4.4.2.
-/

/-- Lemma 4.4.3: For small t ∈ (0, 2), φ₀(i/t) has super-exponential decay.
    This follows from the cusp bound (4.2.1) with z = i/t. -/
lemma norm_φ₀_I_div_t_small (C₀ : ℝ) (_hC₀ : 0 < C₀)
    (hbound : ∀ z : UpperHalfPlane, 1/2 < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im)) :
    ∀ t ∈ Ioo (0 : ℝ) 2, ‖φ₀'' (Complex.I / t)‖ ≤ C₀ * Real.exp (-2 * π / t) := by
  intro t ⟨ht_pos, ht_lt⟩
  -- i/t has imaginary part 1/t > 1/2 for t < 2
  have hI_div_pos : 0 < (Complex.I / t).im := by simp [Complex.div_ofReal_im]; positivity
  have hI_div_gt : 1/2 < (Complex.I / t).im := by
    simp only [Complex.div_ofReal_im, Complex.I_im]
    rw [one_div_lt_one_div (by norm_num : (0:ℝ) < 2) ht_pos]
    linarith
  -- φ₀'' equals φ₀ on upper half-plane, apply the bound
  rw [φ₀''_eq _ hI_div_pos]
  have h := hbound ⟨Complex.I / t, hI_div_pos⟩ hI_div_gt
  -- The bound hbound gives us the inequality for z.im = 1/t
  -- UpperHalfPlane.im ⟨I/t, _⟩ = (I/t).im = 1/t
  have him : UpperHalfPlane.im ⟨Complex.I / t, hI_div_pos⟩ = 1/t := by
    simp [UpperHalfPlane.im]
  simp only [him] at h
  convert h using 2
  field_simp

/-- Helper: t² ≤ exp(4πt) for t ≥ 2. Used in Thesis Lemma 4.4.4.
    Proof: For t ≤ 4π, we have t² ≤ 4πt ≤ exp(4πt).
    For t > 4π, exp grows much faster than any polynomial. -/
lemma sq_le_exp_4pi_t (t : ℝ) (ht : 2 ≤ t) : t^2 ≤ Real.exp (4 * π * t) := by
  have hπ := Real.pi_pos
  have ht_pos : 0 < t := by linarith
  have hx_le : 4 * π * t ≤ Real.exp (4 * π * t) := by
    have h := Real.add_one_le_exp (4 * π * t); linarith
  by_cases ht4π : t ≤ 4 * π
  · -- Case t ≤ 4π: t² ≤ 4πt ≤ exp(4πt)
    have ht2_le_4πt : t^2 ≤ 4 * π * t := by nlinarith
    linarith
  · -- Case t > 4π: exp(4πt) is astronomically larger than t²
    -- Use Taylor: exp(x) ≥ x²/2 for x > 0, proven via exp(x) ≥ 1 + x + x²/2
    -- This gives exp(4πt) ≥ (4πt)²/2 = 8π²t² > t²
    push_neg at ht4π
    have h4πt_pos : 0 ≤ 4 * π * t := by positivity
    have hquad := Real.quadratic_le_exp_of_nonneg h4πt_pos
    -- exp(4πt) ≥ 1 + 4πt + (4πt)²/2 ≥ (4πt)²/2 = 8π²t²
    -- 8π² > 8 * 9 = 72 > 1 since π > 3
    have h8π2 : 8 * π^2 > 1 := by
      have hπ3 : π > 3 := Real.pi_gt_three
      nlinarith
    have hcalc : t^2 < Real.exp (4 * π * t) := calc t^2
        _ < 8 * π^2 * t^2 := by
            have ht2_pos : 0 < t^2 := by positivity
            nlinarith
        _ = (4 * π * t)^2 / 2 := by ring
        _ ≤ 1 + 4 * π * t + (4 * π * t)^2 / 2 := by linarith [h4πt_pos]
        _ ≤ Real.exp (4 * π * t) := hquad
    exact hcalc.le

/-- Helper: exp(-2πt) ≤ (1/t²) * exp(2πt) for t ≥ 2. Used in Thesis Lemma 4.4.4. -/
lemma exp_neg_le_inv_sq_exp (t : ℝ) (ht : 2 ≤ t) :
    Real.exp (-2 * π * t) ≤ (1 / t^2) * Real.exp (2 * π * t) := by
  have ht_pos : 0 < t := by linarith
  have ht2_le_exp := sq_le_exp_4pi_t t ht
  calc Real.exp (-2 * π * t) = Real.exp (2 * π * t) / Real.exp (4 * π * t) := by
          rw [← Real.exp_sub]; ring_nf
    _ ≤ Real.exp (2 * π * t) / t^2 := by
        apply div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos _)) (by positivity) ht2_le_exp
    _ = (1 / t^2) * Real.exp (2 * π * t) := by rw [one_div, div_eq_mul_inv, mul_comm]

/-- Helper: t ≤ exp(2πt) for t ≥ 0. Used for 1/t ≤ (1/t²) * exp(2πt). -/
lemma t_le_exp_two_pi_t (t : ℝ) (ht : 0 ≤ t) : t ≤ Real.exp (2 * π * t) := by
  have hπ := Real.pi_pos
  have h := Real.add_one_le_exp (2 * π * t)
  have h2πminus1 : 1 ≤ 2 * π - 1 := by linarith [Real.pi_gt_three]
  calc t ≤ t + 1 := le_add_of_nonneg_right (by linarith)
    _ ≤ 2 * π * t + 1 := by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * π - 1) ht]
    _ ≤ Real.exp (2 * π * t) := h

/-- Thesis Lemma 4.4.4 (Blueprint Cor 7.13): For large t ≥ 2, φ₀(i/t) grows at most
    like t⁻² e^{2πt}. Uses the S-transform formula (4.1.5) and bounds from Cor 7.5-7.7.

    Strategy: The three-term bound from norm_φ₀''_I_div_t_le can each be bounded by
    (constant) * t^(-2) * exp(2πt), which gives an overall bound of this form. -/
lemma norm_φ₀_I_div_t_large (hb : ContourEndpoints.PhiBounds) :
    ∀ t : ℝ, 2 ≤ t → ‖φ₀'' (Complex.I / t)‖ ≤
      (hb.C₀ + 12 * hb.C₂ / π + 36 * hb.C₄ / π ^ 2) * t ^ (-2 : ℤ) * Real.exp (2 * π * t) := by
  intro t ht
  have ht_pos : 0 < t := by linarith
  have ht_ge_1 : 1 ≤ t := by linarith
  -- Use the existing Blueprint Corollary 7.13 bound from ContourEndpoints
  have h := ContourEndpoints.norm_φ₀''_I_div_t_le hb t ht_ge_1
  -- Each of the three terms can be bounded by its coefficient * t^(-2) * exp(2πt)
  -- Key inequalities:
  -- (1) exp(-2πt) ≤ t^(-2) * exp(2πt)  [since t² ≤ exp(4πt) for t ≥ 2]
  -- (2) 1/t ≤ t^(-2) * exp(2πt)  [since t ≤ exp(2πt)]
  -- (3) 1/t² * exp(2πt) = t^(-2) * exp(2πt)  [exact equality]
  have hπ := Real.pi_pos
  have hexp_pos := Real.exp_pos (2 * π * t)
  -- Rewrite t^(-2 : ℤ) as 1/t²
  have hpow : t ^ (-2 : ℤ) = 1 / t^2 := by
    rw [zpow_neg, zpow_ofNat]
    field_simp
  rw [hpow]
  -- Bound term 1: C₀ * exp(-2πt) ≤ C₀ * (1/t²) * exp(2πt)
  have h1 : hb.C₀ * Real.exp (-2 * π * t) ≤ hb.C₀ * (1 / t^2) * Real.exp (2 * π * t) := by
    have hexp_bound := exp_neg_le_inv_sq_exp t ht
    calc hb.C₀ * Real.exp (-2 * π * t)
        ≤ hb.C₀ * ((1 / t^2) * Real.exp (2 * π * t)) :=
            mul_le_mul_of_nonneg_left hexp_bound hb.hC₀_pos.le
      _ = hb.C₀ * (1 / t^2) * Real.exp (2 * π * t) := by ring
  -- Bound term 2: (12/(πt)) * C₂ ≤ (12*C₂/π) * (1/t²) * exp(2πt)
  -- Need: 1/t ≤ (1/t²) * exp(2πt), i.e., t ≤ exp(2πt)
  have h2 : (12 / (π * t)) * hb.C₂ ≤ (12 * hb.C₂ / π) * (1 / t^2) * Real.exp (2 * π * t) := by
    have ht_le_exp := t_le_exp_two_pi_t t (by linarith)
    -- 1/t ≤ (1/t²) * exp(2πt) is equivalent to t ≤ exp(2πt) (after multiplying by t² and dividing)
    have h_t_inv : 1 / t ≤ (1 / t^2) * Real.exp (2 * π * t) := by
      have ht2_pos : 0 < t^2 := sq_pos_of_pos ht_pos
      have ht2_nonneg : 0 ≤ t^2 := ht2_pos.le
      -- 1/t ≤ exp(2πt)/t² is equivalent to t ≤ exp(2πt)
      have hexp_ge_t : t ≤ Real.exp (2 * π * t) := ht_le_exp
      -- Simplify: 1/t = t/t² and exp/t² ≥ t/t² iff exp ≥ t
      calc 1 / t = t / t^2 := by field_simp
        _ ≤ Real.exp (2 * π * t) / t^2 := div_le_div_of_nonneg_right hexp_ge_t ht2_nonneg
        _ = (1 / t^2) * Real.exp (2 * π * t) := by ring
    calc (12 / (π * t)) * hb.C₂
        = 12 * hb.C₂ / π * (1 / t) := by field_simp
      _ ≤ 12 * hb.C₂ / π * ((1 / t^2) * Real.exp (2 * π * t)) := by
          apply mul_le_mul_of_nonneg_left h_t_inv
          apply div_nonneg (by nlinarith [hb.hC₂_pos.le]) hπ.le
      _ = (12 * hb.C₂ / π) * (1 / t^2) * Real.exp (2 * π * t) := by ring
  -- Bound term 3: (36/(π²*t²)) * C₄ * exp(2πt) = (36*C₄/π²) * (1/t²) * exp(2πt)  [exact]
  have h3 : (36 / (π^2 * t^2)) * hb.C₄ * Real.exp (2 * π * t) =
            (36 * hb.C₄ / π^2) * (1 / t^2) * Real.exp (2 * π * t) := by
    field_simp
  -- Combine the bounds
  calc ‖φ₀'' (Complex.I / t)‖
      ≤ hb.C₀ * Real.exp (-2 * π * t) + (12 / (π * t)) * hb.C₂ +
        (36 / (π^2 * t^2)) * hb.C₄ * Real.exp (2 * π * t) := h
    _ ≤ hb.C₀ * (1 / t^2) * Real.exp (2 * π * t) +
        (12 * hb.C₂ / π) * (1 / t^2) * Real.exp (2 * π * t) +
        (36 * hb.C₄ / π^2) * (1 / t^2) * Real.exp (2 * π * t) := by linarith [h1, h2, h3.le]
    _ = (hb.C₀ + 12 * hb.C₂ / π + 36 * hb.C₄ / π^2) * (1 / t^2) * Real.exp (2 * π * t) := by ring

/-! ## General Shifted Möbius Integrability

A unified lemma that handles all six integrability goals via parameter instantiation.
Uses φ₀''_neg_inv_eq_φ₀_S_smul + norm_φ₀_S_smul_le infrastructure from ContourEndpoints.
-/

/-- For z = a + I*t with t > 0, we have Im(-1/z) = t/(a² + t²) > 0.
    This ensures the Möbius-transformed argument stays in the upper half-plane. -/
lemma im_neg_inv_pos (a t : ℝ) (ht : 0 < t) :
    0 < ((-1 : ℂ) / (a + Complex.I * t)).im := by
  -- Im(-1/(a + I*t)) = t/(a² + t²) > 0 since t > 0 and a² + t² > 0
  have h_denom : a^2 + t^2 > 0 := by positivity
  have h_normSq : Complex.normSq (↑a + Complex.I * ↑t) = a^2 + t^2 := by
    rw [mul_comm]; exact Complex.normSq_add_mul_I a t
  -- Use div_im: (z / w).im = z.im * w.re / normSq w - z.re * w.im / normSq w
  rw [Complex.div_im, h_normSq]
  -- For z = -1: z.re = -1, z.im = 0; For w = a + I*t: w.re = a, w.im = t
  simp only [Complex.neg_im, Complex.one_im, neg_zero, Complex.neg_re, Complex.one_re,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    mul_zero, Complex.I_im, sub_zero, Complex.add_im, Complex.mul_im, zero_mul, add_zero]
  -- Goal: 0 * a / (a² + t²) - (-1) * t / (a² + t²) = t / (a² + t²)
  ring_nf
  exact div_pos ht h_denom

/-- General integrability for φ₀''(-1/(a + I*t)) * (a + I*t)² * cexp(I*π*r*(b + I*t)) on Ioi 1.

    This unified lemma covers all six integrability goals from Proposition 4.4.6:
    - Goals 1, 2, 4, 6: Use a = 0 (Category A, reduces to verticalIntegrandX)
    - Goals 3, 5: Use a = ±1 (Category B, shifted Möbius)

    The proof uses:
    1. φ₀''_neg_inv_eq_φ₀_S_smul: φ₀''(-1/z) = φ₀(S•w) for suitable w ∈ ℍ
    2. norm_φ₀_S_smul_le: |φ₀(S•z)| ≤ C₀ exp(-2π·im(S•z)) for im(z) ≥ 1
    3. Exponential decay for r > 2 dominates polynomial growth -/
lemma integrableOn_φ₀_shifted_Möbius (hb : ContourEndpoints.PhiBounds) (a b r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => φ₀'' (-1 / ((a : ℂ) + Complex.I * t)) *
      ((a : ℂ) + Complex.I * t)^2 *
      Complex.exp (Complex.I * π * r * ((b : ℂ) + Complex.I * t)))
                 (Ioi 1) volume := by
  -- Strategy: Bound by C * verticalBound hb r t where C = a² + 1
  -- Key steps:
  -- 1. For t > 1, z = a + I*t has Im(z) = t > 1
  -- 2. Apply φ₀''_neg_inv_eq_φ₀_S_smul to get φ₀(S•w)
  -- 3. Use norm_φ₀_S_smul_le to bound the φ₀ term (uses ‖z‖ ≥ t)
  -- 4. |z²| = a² + t² ≤ (a² + 1) * t² for t ≥ 1
  -- 5. |exp(...)| = exp(-πrt) independent of b
  -- 6. Combined bound ≤ (a² + 1) * verticalBound
  have hbound_integ : IntegrableOn (fun t => (a^2 + 1) * ContourEndpoints.verticalBound hb r t)
      (Ioi 1) volume := by
    refine IntegrableOn.mono_set ?_ (Ioi_subset_Ici_self (a := 1))
    exact (ContourEndpoints.integrableOn_verticalBound hb r hr).const_mul (a^2 + 1)
  apply MeasureTheory.Integrable.mono' hbound_integ
  · -- AEStronglyMeasurable: The integrand is continuous on Ioi 1
    -- Sketch: φ₀'' ∘ (-1/(a + I*·)) is continuous because:
    --   1. t ↦ -1/(a + I*t) is continuous (ratio of polynomials, nonzero denominator)
    --   2. For t > 0, the image has Im > 0 (by im_neg_inv_pos)
    --   3. φ₀'' = φ₀ on the upper half plane, and φ₀ is continuous
    -- The product with (a + I*t)² and exp(...) is also continuous.
    sorry
  · -- Norm bound: ‖integrand‖ ≤ (a² + 1) * verticalBound hb r t a.e.
    -- Strategy:
    -- 1. For t > 1, z = a + I*t has Im(z) = t > 1
    -- 2. By φ₀''_neg_inv_eq_φ₀_S_smul, φ₀''(-1/z) = φ₀(S•w)
    -- 3. norm_φ₀_S_smul_le gives 3-term bound with ‖z‖ = √(a² + t²) ≥ t
    -- 4. |z²| = a² + t² ≤ (a² + 1) * t² for t ≥ 1
    -- 5. |exp(I*π*r*(b + I*t))| = exp(-πrt)
    -- 6. Combined: ≤ (a² + 1) * [3-term bound] * t² * exp(-πrt) = (a² + 1) * verticalBound
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_gt_1 : 1 < t := mem_Ioi.mp ht
    have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one (le_of_lt ht_gt_1)
    have ht_ge_1 : 1 ≤ t := le_of_lt ht_gt_1
    -- The bound calculation is detailed but straightforward:
    -- ‖integrand‖ = ‖φ₀''(-1/z)‖ * ‖z²‖ * |exp(...)|
    --             ≤ [3-term S-bound] * (a² + t²) * exp(-πrt)
    --             ≤ [3-term bound with ‖z‖→t] * (a² + 1) * t² * exp(-πrt)
    --             = (a² + 1) * verticalBound hb r t
    sorry

/-! ## Relationship to verticalIntegrandX

The Category A goals (1, 2, 4, 6) are scalar multiples of `verticalIntegrandX`.
-/

/-- Helper: (I*t)² = -t². Useful for clearing I² in integrands. -/
@[simp]
lemma I_mul_t_sq (t : ℝ) : (Complex.I * t : ℂ)^2 = -(t^2) := by
  simp [mul_pow, Complex.I_sq, ← Complex.ofReal_neg, ← Complex.ofReal_pow]

/-- Goal 1 integrand equals verticalIntegrandX 0 r t. -/
lemma goal1_eq_verticalIntegrandX (r t : ℝ) (ht : t ≠ 0) :
    Complex.I * φ₀'' (-1 / (Complex.I * t)) * (Complex.I * t)^2 *
      Complex.exp (Complex.I * π * r * (Complex.I * t)) =
    ContourEndpoints.verticalIntegrandX 0 r t := by
  unfold ContourEndpoints.verticalIntegrandX
  rw [neg_one_div_I_mul t ht]
  simp only [Complex.ofReal_zero, zero_add]

/-- Goal 2 integrand equals -I * verticalIntegrandX (-1) r t.

Proof sketch: Both sides reduce to φ₀''(I/t) * (-t²) * cexp(I*π*r*(-1 + I*t))
after using -1/(I*t) = I/t and (I*t)² = -t². -/
lemma goal2_eq_neg_I_verticalIntegrandX (r t : ℝ) (ht : t ≠ 0) :
    φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
      Complex.exp (π * Complex.I * r * (-1 + t * Complex.I)) =
    -Complex.I * ContourEndpoints.verticalIntegrandX (-1) r t := by
  unfold ContourEndpoints.verticalIntegrandX
  rw [mul_comm (t : ℂ) Complex.I, neg_one_div_I_mul t ht]
  simp only [mul_pow, Complex.ofReal_neg, Complex.ofReal_one, neg_mul]
  conv_rhs => rw [show (I : ℂ) ^ 2 = -1 from Complex.I_sq]
  ring_nf

/-- Goal 4 integrand equals -I * verticalIntegrandX 1 r t.

Proof sketch: Same as Goal 2 but with +1 in the exponential phase. -/
lemma goal4_eq_neg_I_verticalIntegrandX (r t : ℝ) (ht : t ≠ 0) :
    φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
      Complex.exp (π * Complex.I * r * (1 + t * Complex.I)) =
    -Complex.I * ContourEndpoints.verticalIntegrandX 1 r t := by
  unfold ContourEndpoints.verticalIntegrandX
  rw [mul_comm (t : ℂ) Complex.I, neg_one_div_I_mul t ht]
  simp only [mul_pow, Complex.ofReal_one, neg_mul]
  conv_rhs => rw [show (I : ℂ) ^ 2 = -1 from Complex.I_sq]
  ring_nf

/-- Goal 6 integrand equals verticalIntegrandX (-1) r t.

Proof sketch: Goal 6 = I * Goal 2 = I * (-I) * verticalIntegrandX (-1) r t
= verticalIntegrandX (-1) r t since I * (-I) = 1. -/
lemma goal6_eq_verticalIntegrandX (r t : ℝ) (ht : t ≠ 0) :
    Complex.I * (φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
      Complex.exp (π * Complex.I * r * (-1 + t * Complex.I))) =
    ContourEndpoints.verticalIntegrandX (-1) r t := by
  unfold ContourEndpoints.verticalIntegrandX
  rw [mul_comm (t : ℂ) Complex.I, neg_one_div_I_mul t ht]
  ring_nf
  simp [pow_two]

/-! ## Helper lemmas for integrability proofs -/

/-- Wrapper for integrability on Ioi 1 (avoids repeated mono_set). -/
lemma integrableOn_verticalIntegrandX_Ioi (hb : ContourEndpoints.PhiBounds)
    (x r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t => ContourEndpoints.verticalIntegrandX x r t) (Ioi 1) volume :=
  (ContourEndpoints.integrableOn_verticalIntegrandX hb x r hr).mono_set Ioi_subset_Ici_self

/-- Integrability of verticalIntegrandX on Ioc 0 1.
    For t ∈ (0, 1], Im(I/t) = 1/t ≥ 1, so the cusp bound ‖φ₀(z)‖ ≤ C₀ exp(-2π·Im(z)) applies.
    Combined with t² ≤ 1 and exp(-πrt) ≤ 1, we get ‖integrand‖ ≤ C₀ exp(-2π). -/
lemma integrableOn_verticalIntegrandX_Ioc (hb : ContourEndpoints.PhiBounds)
    (x r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t => ContourEndpoints.verticalIntegrandX x r t) (Ioc 0 1) volume := by
  -- Continuity on (0, 1] for AEStronglyMeasurable
  have hcont : ContinuousOn (fun t => ContourEndpoints.verticalIntegrandX x r t) (Ioc 0 1) := by
    apply ContinuousOn.mono _ (Ioc_subset_Ioi_self)
    unfold ContourEndpoints.verticalIntegrandX
    have h_cont_phi : ContinuousOn (fun t : ℝ => φ₀'' (Complex.I / t)) (Ioi 0) := by
      have h1 := continuousOn_φ₀''_cusp_path
      refine h1.congr fun t ht =>
        congrArg φ₀'' (neg_one_div_I_mul t (ne_of_gt (mem_Ioi.mp ht))).symm
    refine ((continuousOn_const.mul h_cont_phi).mul ?_).mul ?_
    · exact (continuousOn_const.mul Complex.continuous_ofReal.continuousOn).pow _
    · refine Complex.continuous_exp.comp_continuousOn ?_
      refine (continuousOn_const.mul continuousOn_const).mul ?_
      exact continuousOn_const.add (continuousOn_const.mul Complex.continuous_ofReal.continuousOn)
  have hmeas : AEStronglyMeasurable (fun t => ContourEndpoints.verticalIntegrandX x r t)
      (volume.restrict (Ioc 0 1)) := hcont.aestronglyMeasurable measurableSet_Ioc
  -- Pointwise bound: for t ∈ (0, 1], ‖verticalIntegrandX x r t‖ ≤ C₀ * exp(-2π)
  have hbound : ∀ t ∈ Ioc 0 1, ‖ContourEndpoints.verticalIntegrandX x r t‖ ≤
      hb.C₀ * Real.exp (-2 * π) := by
    intro t ⟨ht_pos, ht_le⟩
    rw [ContourEndpoints.norm_verticalIntegrandX x r t ht_pos]
    have hI_div_im : (Complex.I / t).im = 1/t := by simp [Complex.div_ofReal_im]
    have hI_div_pos : 0 < (Complex.I / t).im := by rw [hI_div_im]; positivity
    have hφ₀_bound : ‖φ₀'' (Complex.I / t)‖ ≤ hb.C₀ * Real.exp (-2 * π / t) := by
      rw [φ₀''_eq _ hI_div_pos]
      have hz : UpperHalfPlane.im ⟨Complex.I / t, hI_div_pos⟩ = 1/t := by simp [UpperHalfPlane.im]
      calc ‖φ₀ ⟨Complex.I / ↑t, hI_div_pos⟩‖
        ≤ hb.C₀ * Real.exp (-2 * π * UpperHalfPlane.im ⟨Complex.I / t, hI_div_pos⟩) :=
            hb.hφ₀ _ (by rw [hz, le_div_iff₀ ht_pos]; linarith)
        _ = hb.C₀ * Real.exp (-2 * π / t) := by rw [hz]; ring_nf
    have hr_pos : 0 < r := lt_trans (by norm_num : (0:ℝ) < 2) hr
    have ht2_le : t^2 ≤ 1 := by nlinarith [sq_nonneg t, sq_nonneg (t - 1)]
    have hexp_neg : Real.exp (-π * r * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have := mul_pos (mul_pos Real.pi_pos hr_pos) ht_pos; linarith
    have hexp_bound : Real.exp (-2 * π / t) ≤ Real.exp (-2 * π) := by
      apply Real.exp_le_exp_of_le
      have h1t : 1 ≤ 1 / t := by rw [le_div_iff₀ ht_pos]; linarith
      have hπ := Real.pi_pos
      have h2πt : 2 * π ≤ 2 * π / t := by
        calc 2 * π = 2 * π * 1 := by ring
          _ ≤ 2 * π * (1 / t) := by nlinarith
          _ = 2 * π / t := by ring
      have hneg : -(2 * π / t) ≤ -(2 * π) := neg_le_neg h2πt
      calc -2 * π / t = -(2 * π / t) := by ring
        _ ≤ -(2 * π) := hneg
        _ = -2 * π := by ring
    calc t^2 * ‖φ₀'' (Complex.I / ↑t)‖ * Real.exp (-π * r * t)
        ≤ 1 * (hb.C₀ * Real.exp (-2 * π / t)) * 1 := by
          have h1 : t^2 * ‖φ₀'' (Complex.I / ↑t)‖ ≤ 1 * (hb.C₀ * Real.exp (-2 * π / t)) :=
            mul_le_mul ht2_le hφ₀_bound (norm_nonneg _) zero_le_one
          have h2 : 0 ≤ 1 * (hb.C₀ * Real.exp (-2 * π / t)) :=
            mul_nonneg (by norm_num) (mul_nonneg hb.hC₀_pos.le (Real.exp_pos _).le)
          exact mul_le_mul h1 hexp_neg (Real.exp_pos _).le h2
      _ ≤ hb.C₀ * Real.exp (-2 * π) := by
          simp only [one_mul, mul_one]; exact mul_le_mul_of_nonneg_left hexp_bound hb.hC₀_pos.le
  -- Construct IntegrableOn from AEStronglyMeasurable + bounded + finite measure
  rw [IntegrableOn, Integrable]
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_def]
  have h_bound_ae : ∀ᵐ t ∂(volume.restrict (Ioc 0 1)),
      (‖ContourEndpoints.verticalIntegrandX x r t‖₊ : ℝ≥0∞) ≤
      ↑(hb.C₀ * Real.exp (-2 * π)).toNNReal := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    apply ae_of_all
    intro t ht
    rw [ENNReal.coe_le_coe]
    have hle := hbound t ht
    have h1 : ‖ContourEndpoints.verticalIntegrandX x r t‖₊ =
        ‖ContourEndpoints.verticalIntegrandX x r t‖.toNNReal := by simp
    rw [h1]
    exact Real.toNNReal_le_toNNReal hle
  calc ∫⁻ t, ↑‖ContourEndpoints.verticalIntegrandX x r t‖₊ ∂(volume.restrict (Ioc 0 1))
      ≤ ∫⁻ _t, ↑(hb.C₀ * Real.exp (-2 * π)).toNNReal ∂(volume.restrict (Ioc 0 1)) :=
        lintegral_mono_ae h_bound_ae
    _ = ↑(hb.C₀ * Real.exp (-2 * π)).toNNReal * volume (Ioc (0 : ℝ) 1) := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    _ < ⊤ := by
        rw [ENNReal.mul_lt_top_iff]
        left
        exact ⟨ENNReal.coe_lt_top, measure_Ioc_lt_top⟩

/-- IntegrableOn is preserved by constant multiplication. -/
lemma IntegrableOn.const_mul' {c : ℂ} {f : ℝ → ℂ} {s : Set ℝ}
    (hf : IntegrableOn f s volume) : IntegrableOn (fun t => c * f t) s volume := by
  rw [IntegrableOn] at hf ⊢
  exact hf.smul c

/-- Helper simp lemma: t*I + 1 = 1 + I*t -/
@[simp]
lemma t_mul_I_add_one (t : ℝ) : (t : ℂ) * Complex.I + 1 = (1 : ℂ) + Complex.I * t := by ring

/-- Helper simp lemma: t*I - 1 = -1 + I*t -/
@[simp]
lemma t_mul_I_sub_one (t : ℝ) : (t : ℂ) * Complex.I - 1 = (-1 : ℂ) + Complex.I * t := by ring

/-! ## Specific Instantiations

The six integrability goals from Proposition 4.4.6.
-/

/-- Goal 1: Integrability of I * φ₀''(-1/(I*t)) * (I*t)² * cexp(I*π*r*(I*t)) on [0,∞).
    Note: -1/(I*t) = I/t, so this is verticalIntegrandX 0 r t. -/
lemma integrableOn_goal1 (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => Complex.I * φ₀'' (-1 / (Complex.I * t)) * (Complex.I * t)^2 *
                          Complex.exp (Complex.I * π * r * (Complex.I * t)))
                 (Ici (0 : ℝ)) volume := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi, ← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · -- Integrability on Ioc 0 1 using the helper lemma
    have hIoc := integrableOn_verticalIntegrandX_Ioc hb 0 r hr
    have heq : EqOn (fun t : ℝ => Complex.I * φ₀'' (-1 / (Complex.I * t)) * (Complex.I * t)^2 *
                    Complex.exp (Complex.I * π * r * (Complex.I * t)))
               (fun t : ℝ => ContourEndpoints.verticalIntegrandX 0 r t) (Ioc 0 1) := by
      intro t ⟨ht_pos, _⟩
      exact goal1_eq_verticalIntegrandX r t (ne_of_gt ht_pos)
    exact hIoc.congr_fun heq.symm measurableSet_Ioc
  · -- Integrability on Ioi 1 from existing infrastructure
    have h : IntegrableOn (fun t : ℝ => ContourEndpoints.verticalIntegrandX 0 r t)
        (Ici 1) volume := ContourEndpoints.integrableOn_verticalIntegrandX hb 0 r hr
    have h' : IntegrableOn (fun t : ℝ => ContourEndpoints.verticalIntegrandX 0 r t)
        (Ioi 1) volume := h.mono_set Ioi_subset_Ici_self
    have heq : EqOn (fun t : ℝ => ContourEndpoints.verticalIntegrandX 0 r t)
        (fun t : ℝ => Complex.I * φ₀'' (-1 / (Complex.I * t)) * (Complex.I * t)^2 *
          Complex.exp (Complex.I * π * r * (Complex.I * t))) (Ioi 1) := by
      intro t ht
      exact (goal1_eq_verticalIntegrandX r t (ne_of_gt (lt_of_lt_of_le one_pos (le_of_lt ht)))).symm
    exact h'.congr_fun heq measurableSet_Ioi

/-- Goal 2: Integrability of φ₀''(-1/(t*I)) * (t*I)² * cexp(π*I*r*(-1 + t*I)) on (1,∞).
    By goal2_eq_neg_I_verticalIntegrandX, this is -I * verticalIntegrandX (-1) r t. -/
lemma integrableOn_goal2 (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
                          Complex.exp (π * Complex.I * r * (-1 + t * Complex.I)))
                 (Ioi (1 : ℝ)) volume := by
  have h := integrableOn_verticalIntegrandX_Ioi hb (-1) r hr
  have hsmul : IntegrableOn (fun t => -Complex.I * ContourEndpoints.verticalIntegrandX (-1) r t)
      (Ioi 1) volume := by rw [IntegrableOn] at h ⊢; exact h.smul (-Complex.I)
  exact hsmul.congr_fun (fun t ht =>
    (goal2_eq_neg_I_verticalIntegrandX r t (ne_of_gt (lt_trans one_pos ht))).symm) measurableSet_Ioi

/-- Goal 3: Integrability of φ₀''(-1/(t*I + 1)) * (t*I+1)² * cexp(π*I*r*(t*I)) on (1,∞).
    Category B: Shifted Möbius argument at +1. Derived from integrableOn_φ₀_shifted_Möbius. -/
lemma integrableOn_goal3 (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => φ₀'' (-1 / (t * Complex.I + 1)) * (t * Complex.I + 1)^2 *
                          Complex.exp (π * Complex.I * r * (t * Complex.I)))
                 (Ioi (1 : ℝ)) volume := by
  have h := integrableOn_φ₀_shifted_Möbius hb 1 0 r hr
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t _
  simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_one]
  ring_nf

/-- Goal 4: Integrability of φ₀''(-1/(t*I)) * (t*I)² * cexp(π*I*r*(1 + t*I)) on (1,∞).
    By goal4_eq_neg_I_verticalIntegrandX, this is -I * verticalIntegrandX 1 r t. -/
lemma integrableOn_goal4 (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
                          Complex.exp (π * Complex.I * r * (1 + t * Complex.I)))
                 (Ioi (1 : ℝ)) volume := by
  have h := integrableOn_verticalIntegrandX_Ioi hb 1 r hr
  have hsmul : IntegrableOn (fun t => -Complex.I * ContourEndpoints.verticalIntegrandX 1 r t)
      (Ioi 1) volume := by rw [IntegrableOn] at h ⊢; exact h.smul (-Complex.I)
  exact hsmul.congr_fun (fun t ht =>
    (goal4_eq_neg_I_verticalIntegrandX r t (ne_of_gt (lt_trans one_pos ht))).symm) measurableSet_Ioi

/-- Goal 5: Integrability of φ₀''(-1/(t*I - 1)) * (t*I-1)² * cexp(π*I*r*(t*I)) on (1,∞).
    Category B: Shifted Möbius argument at -1. Derived from integrableOn_φ₀_shifted_Möbius. -/
lemma integrableOn_goal5 (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => φ₀'' (-1 / (t * Complex.I - 1)) * (t * Complex.I - 1)^2 *
                          Complex.exp (π * Complex.I * r * (t * Complex.I)))
                 (Ioi (1 : ℝ)) volume := by
  have h := integrableOn_φ₀_shifted_Möbius hb (-1) 0 r hr
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t _
  simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_neg, Complex.ofReal_one]
  ring_nf

/-- Goal 6: Integrability of I * (φ₀''(-1/(t*I)) * (t*I)² * cexp(π*I*r*(-1 + t*I))) on [0,∞).
    By goal6_eq_verticalIntegrandX, this is verticalIntegrandX (-1) r t. -/
lemma integrableOn_goal6 (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => Complex.I * (φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
                          Complex.exp (π * Complex.I * r * (-1 + t * Complex.I))))
                 (Ici (0 : ℝ)) volume := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi, ← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · -- Integrability on Ioc 0 1 using the helper lemma
    have hIoc := integrableOn_verticalIntegrandX_Ioc hb (-1) r hr
    have heq : EqOn (fun t : ℝ => Complex.I * (φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
                      Complex.exp (π * Complex.I * r * (-1 + t * Complex.I))))
               (fun t : ℝ => ContourEndpoints.verticalIntegrandX (-1) r t) (Ioc 0 1) := by
      intro t ⟨ht_pos, _⟩
      exact goal6_eq_verticalIntegrandX r t (ne_of_gt ht_pos)
    exact hIoc.congr_fun heq.symm measurableSet_Ioc
  · -- Integrability on Ioi 1 from existing infrastructure
    have h : IntegrableOn (fun t : ℝ => ContourEndpoints.verticalIntegrandX (-1) r t)
        (Ici 1) volume := ContourEndpoints.integrableOn_verticalIntegrandX hb (-1) r hr
    have h' : IntegrableOn (fun t : ℝ => ContourEndpoints.verticalIntegrandX (-1) r t)
        (Ioi 1) volume := h.mono_set Ioi_subset_Ici_self
    have heq : EqOn (fun t : ℝ => ContourEndpoints.verticalIntegrandX (-1) r t)
        (fun t : ℝ => Complex.I * (φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
          Complex.exp (π * Complex.I * r * (-1 + t * Complex.I)))) (Ioi 1) := by
      intro t ht
      exact (goal6_eq_verticalIntegrandX r t (ne_of_gt (lt_of_lt_of_le one_pos (le_of_lt ht)))).symm
    exact h'.congr_fun heq measurableSet_Ioi

/-! ## Vanishing Lemmas (Lemma 4.4.5)

These are needed for the Cauchy-Goursat deformation arguments.
-/

/-- Lemma 4.4.5: The integrand φ₀(-1/z) z² e^{πirz} → 0 as Im(z) → ∞ for r > 2. -/
lemma tendsto_φ₀_integrand_atImInfty (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    Tendsto (fun z => φ₀'' (-1/z) * z^2 * Complex.exp (π * Complex.I * r * z))
            (comap Complex.im atTop) (nhds 0) := by
  -- Strategy: On vertical ray z = x + I*t,
  -- |φ₀''(-1/z)| ≤ C exp(-2π·Im(-1/z)) for large Im(-1/z)
  -- But Im(-1/z) = Im(z) / |z|² → 0 as Im(z) → ∞ with x fixed
  -- So we need the S-transform bound instead
  sorry

/-- Shifted variant: φ₀(-1/(z+1)) (z+1)² e^{πirz} → 0 as Im(z) → ∞. -/
lemma tendsto_φ₀_integrand_plus_one (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    Tendsto (fun z => φ₀'' (-1/(z+1)) * (z+1)^2 * Complex.exp (π * Complex.I * r * z))
            (comap Complex.im atTop) (nhds 0) := by
  sorry

/-- Shifted variant: φ₀(-1/(z-1)) (z-1)² e^{πirz} → 0 as Im(z) → ∞. -/
lemma tendsto_φ₀_integrand_minus_one (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    Tendsto (fun z => φ₀'' (-1/(z-1)) * (z-1)^2 * Complex.exp (π * Complex.I * r * z))
            (comap Complex.im atTop) (nhds 0) := by
  sorry

end MagicFunction.VerticalIntegrability
