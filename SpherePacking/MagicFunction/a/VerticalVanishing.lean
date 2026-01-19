/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import SpherePacking.MagicFunction.a.ContourEndpoints

/-!
# Vertical Ray Vanishing Lemmas

Vanishing lemmas for vertical ray integrands involving φ₀, needed for Cauchy-Goursat
deformation arguments in the double zeros proof.

## Main results

- `tendsto_φ₀_integrand_atImInfty`: Base vanishing as Im(z) → ∞
- `tendsto_φ₀_integrand_plus_one`: Shifted variant for z + 1
- `tendsto_φ₀_integrand_minus_one`: Shifted variant for z - 1

## References

- Sidharth Hariharan's thesis, Lemma 4.4.5
- Blueprint Proposition 4.4.6
-/

open MeasureTheory Set Filter Real Complex TopologicalSpace

open scoped Interval Real NNReal ENNReal Topology BigOperators

noncomputable section

namespace MagicFunction.VerticalVanishing

/-! ## Helper lemmas -/

/-- Goal 1 integrand equals verticalIntegrandX 0 r t. -/
lemma goal1_eq_verticalIntegrandX (r t : ℝ) (ht : t ≠ 0) :
    Complex.I * φ₀'' (-1 / (Complex.I * t)) * (Complex.I * t)^2 *
      Complex.exp (Complex.I * π * r * (Complex.I * t)) =
    ContourEndpoints.verticalIntegrandX 0 r t := by
  unfold ContourEndpoints.verticalIntegrandX
  rw [neg_one_div_I_mul t ht]
  simp only [Complex.ofReal_zero, zero_add]

/-! ## Vanishing Lemmas (Lemma 4.4.5)

These are needed for the Cauchy-Goursat deformation arguments.
The lemmas are stated in vertical-line form for a fixed real part x, which directly
uses the existing `tendsto_verticalIntegrandX_atTop` infrastructure.
-/

/-- Lemma 4.4.5 (vertical line at x = 0): The integrand → 0 as t → ∞.
    On z = I*t, we have φ₀''(-1/(I*t)) = φ₀''(I/t) which uses verticalIntegrandX 0 r t. -/
lemma tendsto_φ₀_integrand_atImInfty (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    Tendsto (fun t : ℝ => φ₀'' (-1 / (Complex.I * t)) * (Complex.I * t)^2 *
                         Complex.exp (π * Complex.I * r * (Complex.I * t)))
            atTop (𝓝 0) := by
  -- This equals (1/I) * verticalIntegrandX 0 r t by goal1_eq_verticalIntegrandX
  have h := ContourEndpoints.tendsto_verticalIntegrandX_atTop hb 0 r hr
  -- The integrand differs from verticalIntegrandX 0 r t by a factor of 1/I
  have heq : ∀ t : ℝ, t ≠ 0 →
      φ₀'' (-1 / (Complex.I * t)) * (Complex.I * t)^2 *
        Complex.exp (π * Complex.I * r * (Complex.I * t)) =
      (-Complex.I) * ContourEndpoints.verticalIntegrandX 0 r t := by
    intro t ht
    have h1 := goal1_eq_verticalIntegrandX r t ht
    -- From h1: I * φ₀''(-1/(I*t)) * (I*t)² * exp(I*π*r*(I*t)) = verticalIntegrandX 0 r t
    -- So: φ₀''(...) * ... = (1/I) * verticalIntegrandX = -I * verticalIntegrandX
    have hI_inv : (Complex.I)⁻¹ = -Complex.I := Complex.inv_I
    calc φ₀'' (-1 / (Complex.I * t)) * (Complex.I * t)^2 *
             Complex.exp (π * Complex.I * r * (Complex.I * t))
        = φ₀'' (-1 / (Complex.I * t)) * (Complex.I * t)^2 *
             Complex.exp (Complex.I * π * r * (Complex.I * t)) := by ring
      _ = (Complex.I)⁻¹ * Complex.I * (φ₀'' (-1 / (Complex.I * t)) * (Complex.I * t)^2 *
             Complex.exp (Complex.I * π * r * (Complex.I * t))) := by
          rw [inv_mul_cancel₀ Complex.I_ne_zero, one_mul]
      _ = (Complex.I)⁻¹ * (Complex.I * φ₀'' (-1 / (Complex.I * t)) * (Complex.I * t)^2 *
             Complex.exp (Complex.I * π * r * (Complex.I * t))) := by ring
      _ = (Complex.I)⁻¹ * ContourEndpoints.verticalIntegrandX 0 r t := by rw [h1]
      _ = -Complex.I * ContourEndpoints.verticalIntegrandX 0 r t := by rw [hI_inv]
  -- Use eventually_atTop to apply heq for large t
  have hconv : Tendsto (fun t => (-Complex.I) * ContourEndpoints.verticalIntegrandX 0 r t)
      atTop (𝓝 0) := by
    convert h.const_mul (-Complex.I) using 1
    simp only [mul_zero]
  apply hconv.congr'
  filter_upwards [eventually_gt_atTop 0] with t ht
  exact (heq t (ne_of_gt ht)).symm

/-- Shifted variant at x = 1: φ₀(-1/(z+1)) (z+1)² e^{πirz} → 0 as Im(z) → ∞.
    On z = I*t, we have z+1 = 1 + I*t, using verticalIntegrandX 1 r t. -/
lemma tendsto_φ₀_integrand_plus_one (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    Tendsto (fun t : ℝ => φ₀'' (-1 / ((1 : ℂ) + Complex.I * t)) * ((1 : ℂ) + Complex.I * t)^2 *
                         Complex.exp (π * Complex.I * r * (Complex.I * t)))
            atTop (𝓝 0) := by
  -- Our integrand has the same norm as topEdgeIntegrand r 1 t (differ by unit-modulus exp(I*π*r))
  -- Use squeeze theorem: ‖f(t)‖ ≤ topEdgeBound → 0 implies f(t) → 0
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have htendsto := ContourEndpoints.tendsto_topEdgeBound_atTop hb r hr
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htendsto ε hε
  use max N 1
  intro t ht
  have ht_ge_1 : 1 ≤ t := le_of_max_le_right ht
  have ht_ge_N : N ≤ t := le_of_max_le_left ht
  have ht_pos : 0 < t := by linarith
  simp only [dist_zero_right]
  -- The integrand norm equals ‖topEdgeIntegrand r 1 t‖ (exponential phases have same norm)
  have h_x_mem : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by simp
  -- Direct approach: bound our integrand norm by topEdgeBound
  have h_norm_bound : ‖φ₀'' (-1 / ((1 : ℂ) + Complex.I * t)) * ((1 : ℂ) + Complex.I * t)^2 *
                       Complex.exp (π * Complex.I * r * (Complex.I * t))‖ ≤
                      ContourEndpoints.topEdgeBound hb r t := by
    -- Both exponentials have norm exp(-πrt)
    have hexp_our :
        ‖Complex.exp (π * Complex.I * r * (Complex.I * t))‖ = Real.exp (-π * r * t) := by
      rw [show π * Complex.I * r * (Complex.I * t) =
          Complex.I * π * r * (0 + Complex.I * t) by ring]
      exact ContourEndpoints.norm_cexp_verticalPhase 0 r t
    have hexp_top :
        ‖Complex.exp (Complex.I * π * r * (1 + Complex.I * t))‖ = Real.exp (-π * r * t) :=
      ContourEndpoints.norm_cexp_verticalPhase 1 r t
    -- So the norms are equal
    calc ‖φ₀'' (-1 / ((1 : ℂ) + Complex.I * t)) * ((1 : ℂ) + Complex.I * t)^2 *
            Complex.exp (π * Complex.I * r * (Complex.I * t))‖
        = ‖φ₀'' (-1 / ((1 : ℂ) + Complex.I * t))‖ * ‖((1 : ℂ) + Complex.I * t)^2‖ *
          Real.exp (-π * r * t) := by rw [norm_mul, norm_mul, hexp_our]
      _ = ‖φ₀'' (-1 / ((1 : ℂ) + Complex.I * t))‖ * ‖((1 : ℂ) + Complex.I * t)^2‖ *
          ‖Complex.exp (Complex.I * π * r * (1 + Complex.I * t))‖ := by rw [hexp_top]
      _ = ‖ContourEndpoints.topEdgeIntegrand r 1 t‖ := by
          simp only [ContourEndpoints.topEdgeIntegrand, Complex.ofReal_one]
          rw [norm_mul, norm_mul]
      _ ≤ ContourEndpoints.topEdgeBound hb r t :=
          ContourEndpoints.norm_topEdgeIntegrand_le hb r 1 t h_x_mem ht_ge_1
  calc ‖φ₀'' (-1 / ((1 : ℂ) + Complex.I * t)) * ((1 : ℂ) + Complex.I * t)^2 *
            Complex.exp (π * Complex.I * r * (Complex.I * t))‖
      ≤ ContourEndpoints.topEdgeBound hb r t := h_norm_bound
    _ < ε := by
        have := hN t ht_ge_N
        simp only [dist_zero_right, Real.norm_eq_abs] at this
        have hbound_nonneg : 0 ≤ ContourEndpoints.topEdgeBound hb r t := by
          unfold ContourEndpoints.topEdgeBound
          have hp : 0 < π := Real.pi_pos
          have hC₀ : 0 < hb.C₀ := hb.hC₀_pos
          have hC₂ : 0 < hb.C₂ := hb.hC₂_pos
          have hC₄ : 0 < hb.C₄ := hb.hC₄_pos
          have hpt : 0 < π * t := mul_pos hp ht_pos
          have hpt2 : 0 < π^2 * t^2 := mul_pos (sq_pos_of_pos hp) (sq_pos_of_pos ht_pos)
          apply mul_nonneg
          · apply mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
          · apply add_nonneg
            · apply add_nonneg
              · exact mul_nonneg hC₀.le (Real.exp_pos _).le
              · exact div_nonneg (mul_nonneg (by norm_num) hC₂.le) hpt.le
            · exact mul_nonneg
                (div_nonneg (mul_nonneg (by norm_num) hC₄.le) hpt2.le) (Real.exp_pos _).le
        exact abs_of_nonneg hbound_nonneg ▸ this

/-- Shifted variant at x = -1: φ₀(-1/(z-1)) (z-1)² e^{πirz} → 0 as Im(z) → ∞.
    On z = I*t, we have z-1 = -1 + I*t, using verticalIntegrandX (-1) r t. -/
lemma tendsto_φ₀_integrand_minus_one (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    Tendsto (fun t : ℝ => φ₀'' (-1 / ((-1 : ℂ) + Complex.I * t)) * ((-1 : ℂ) + Complex.I * t)^2 *
                         Complex.exp (π * Complex.I * r * (Complex.I * t)))
            atTop (𝓝 0) := by
  -- Same as plus_one but with x = -1
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have htendsto := ContourEndpoints.tendsto_topEdgeBound_atTop hb r hr
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htendsto ε hε
  use max N 1
  intro t ht
  have ht_ge_1 : 1 ≤ t := le_of_max_le_right ht
  have ht_ge_N : N ≤ t := le_of_max_le_left ht
  have ht_pos : 0 < t := by linarith
  simp only [dist_zero_right]
  have h_x_mem : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by simp
  -- Direct approach: bound our integrand norm by topEdgeBound
  have h_norm_bound : ‖φ₀'' (-1 / ((-1 : ℂ) + Complex.I * t)) *
      ((-1 : ℂ) + Complex.I * t)^2 *
      Complex.exp (π * Complex.I * r * (Complex.I * t))‖ ≤
      ContourEndpoints.topEdgeBound hb r t := by
    -- Both exponentials have norm exp(-πrt)
    have hexp_our :
        ‖Complex.exp (π * Complex.I * r * (Complex.I * t))‖ = Real.exp (-π * r * t) := by
      rw [show π * Complex.I * r * (Complex.I * t) =
          Complex.I * π * r * (0 + Complex.I * t) by ring]
      exact ContourEndpoints.norm_cexp_verticalPhase 0 r t
    have hexp_top :
        ‖Complex.exp (Complex.I * π * r * (-1 + Complex.I * t))‖ = Real.exp (-π * r * t) := by
      have h := ContourEndpoints.norm_cexp_verticalPhase (-1) r t
      simp only [Complex.ofReal_neg, Complex.ofReal_one] at h
      exact h
    calc ‖φ₀'' (-1 / ((-1 : ℂ) + Complex.I * t)) * ((-1 : ℂ) + Complex.I * t)^2 *
            Complex.exp (π * Complex.I * r * (Complex.I * t))‖
        = ‖φ₀'' (-1 / ((-1 : ℂ) + Complex.I * t))‖ * ‖((-1 : ℂ) + Complex.I * t)^2‖ *
          Real.exp (-π * r * t) := by rw [norm_mul, norm_mul, hexp_our]
      _ = ‖φ₀'' (-1 / ((-1 : ℂ) + Complex.I * t))‖ * ‖((-1 : ℂ) + Complex.I * t)^2‖ *
          ‖Complex.exp (Complex.I * π * r * (-1 + Complex.I * t))‖ := by rw [hexp_top]
      _ = ‖ContourEndpoints.topEdgeIntegrand r (-1) t‖ := by
          simp only [ContourEndpoints.topEdgeIntegrand, Complex.ofReal_neg, Complex.ofReal_one]
          rw [norm_mul, norm_mul]
      _ ≤ ContourEndpoints.topEdgeBound hb r t :=
          ContourEndpoints.norm_topEdgeIntegrand_le hb r (-1) t h_x_mem ht_ge_1
  calc ‖φ₀'' (-1 / ((-1 : ℂ) + Complex.I * t)) * ((-1 : ℂ) + Complex.I * t)^2 *
            Complex.exp (π * Complex.I * r * (Complex.I * t))‖
      ≤ ContourEndpoints.topEdgeBound hb r t := h_norm_bound
    _ < ε := by
        have := hN t ht_ge_N
        simp only [dist_zero_right, Real.norm_eq_abs] at this
        have hbound_nonneg : 0 ≤ ContourEndpoints.topEdgeBound hb r t := by
          unfold ContourEndpoints.topEdgeBound
          have hp : 0 < π := Real.pi_pos
          have hC₀ : 0 < hb.C₀ := hb.hC₀_pos
          have hC₂ : 0 < hb.C₂ := hb.hC₂_pos
          have hC₄ : 0 < hb.C₄ := hb.hC₄_pos
          have hpt : 0 < π * t := mul_pos hp ht_pos
          have hpt2 : 0 < π^2 * t^2 := mul_pos (sq_pos_of_pos hp) (sq_pos_of_pos ht_pos)
          apply mul_nonneg
          · apply mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
          · apply add_nonneg
            · apply add_nonneg
              · exact mul_nonneg hC₀.le (Real.exp_pos _).le
              · exact div_nonneg (mul_nonneg (by norm_num) hC₂.le) hpt.le
            · exact mul_nonneg
                (div_nonneg (mul_nonneg (by norm_num) hC₄.le) hpt2.le) (Real.exp_pos _).le
        exact abs_of_nonneg hbound_nonneg ▸ this

end MagicFunction.VerticalVanishing
