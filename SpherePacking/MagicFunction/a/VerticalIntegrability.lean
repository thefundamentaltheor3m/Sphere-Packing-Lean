/-
Copyright (c) 2026 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
import SpherePacking.MagicFunction.a.ContourEndpoints
import SpherePacking.ModularForms.PhiTransform

/-!
# Vertical Contour Integrability

Integrability and vanishing lemmas for vertical ray integrands involving φ₀.
Provides bounds from Lemmas 4.4.3-4.4.4 of Sid's thesis and general integrability results
needed for Proposition 4.4.6 (the double zeros proof).

## Main results

### Thesis Bounds (Section 4.4.1)
- `norm_φ₀_I_div_t_small`: Lemma 4.4.3 - For t ∈ (0, 2), |φ₀(i/t)| ≤ C₀ e^{-2π/t}
- `norm_φ₀_I_div_t_large`: Lemma 4.4.4 - For t ≥ 2, |φ₀(i/t)| ≤ C t⁻² e^{2πt}

### General Integrability
- `integrableOn_vertical_general`: General integrability for r > 2 on (0, ∞)

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
lemma norm_φ₀_I_div_t_small (C₀ : ℝ) (hC₀ : 0 < C₀)
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
  simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_mk, Complex.div_ofReal_im, Complex.I_im] at h
  -- Exact algebra: -2 * π / t = -2 * π * (1/t)
  sorry

/-- Lemma 4.4.4: For large t ≥ 2, φ₀(i/t) grows at most like t⁻² e^{2πt}.
    This uses the S-transform formula (4.1.5) and bounds from Cor 7.5-7.7. -/
lemma norm_φ₀_I_div_t_large (hb : ContourEndpoints.PhiBounds) :
    ∀ t : ℝ, 2 ≤ t → ‖φ₀'' (Complex.I / t)‖ ≤
      (hb.C₀ + 12 * hb.C₂ / π + 36 * hb.C₄ / π ^ 2) * t ^ (-2 : ℤ) * Real.exp (2 * π * t) := by
  intro t ht
  have ht_pos : 0 < t := by linarith
  have ht_ge_1 : 1 ≤ t := by linarith
  -- Use the existing Corollary 7.13 bound from ContourEndpoints
  have h := ContourEndpoints.norm_φ₀''_I_div_t_le hb t ht_ge_1
  -- The bound from ContourEndpoints is a 3-term sum, we need to combine
  -- For simplicity, use that for t ≥ 2, we can bound crudely
  sorry

/-! ## Integrand Boundedness

For the integral ∫₀^∞ φ₀(i/t) t² e^{-πrt} dt to converge (r > 2):
- Small t: |φ₀(i/t) t² e^{-πrt}| ≤ C₀ e^{-2π/t} · t² ≤ 4C₀ (bounded)
- Large t: |φ₀(i/t) t² e^{-πrt}| ≤ C · e^{(2-r)πt} (exponentially decaying for r > 2)
-/

/-- The integrand φ₀(i/t) t² e^{-πrt} is bounded on (0, 2] for any r. -/
lemma integrand_bounded_small (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hbound : ∀ z : UpperHalfPlane, 1/2 < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (r : ℝ) :
    ∃ M : ℝ, ∀ t ∈ Ioo (0 : ℝ) 2,
      ‖φ₀'' (Complex.I / t) * t ^ 2 * Real.exp (-π * r * t)‖ ≤ M := by
  use 4 * C₀
  intro t ⟨ht_pos, ht_lt⟩
  have h1 := norm_φ₀_I_div_t_small C₀ hC₀ hbound t ⟨ht_pos, ht_lt⟩
  -- Use sorry for now; proof needs careful norm handling
  sorry

/-- The integrand has exponential decay on [2, ∞) for r > 2. -/
lemma integrand_exp_decay_large (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    ∃ C : ℝ, ∀ t : ℝ, 2 ≤ t →
      ‖φ₀'' (Complex.I / t) * t^2 * Complex.exp (-π * r * t)‖ ≤ C * Real.exp ((2 - r) * π * t) := by
  sorry

/-! ## General Integrability Lemma

The main result: integrability of vertical-type integrands for r > 2.
-/

/-- General integrability for vertical-type integrands.
    Pattern: φ₀'' (-1 / (a + I*t)) * (a + I*t)² * cexp(π*I*r*(b + I*t))
    where a, b are real constants (shifts).

    Key observation: -1/(a + I*t) = (-a + I*t) / (a² + t²), which has positive
    imaginary part t/(a² + t²) > 0 for t > 0. -/
lemma integrableOn_vertical_general (hb : ContourEndpoints.PhiBounds) (a b r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => φ₀'' (-1 / (a + Complex.I * t)) * (a + Complex.I * t)^2 *
                          Complex.exp (π * Complex.I * r * (b + Complex.I * t)))
                 (Ioi (0 : ℝ)) volume := by
  -- Split into (0, 2] and [2, ∞)
  -- Small t: bounded integrand on compact set → integrable
  -- Large t: exponential decay → integrable
  sorry

/-! ## Specific Instantiations

The six integrability goals from Proposition 4.4.6.
-/

/-- Goal 1: Integrability of I * φ₀''(-1/(I*t)) * (I*t)² * cexp(I*π*r*(I*t)) on [0,∞).
    Note: -1/(I*t) = I/t, so this is the base vertical integrand at x = 0. -/
lemma integrableOn_goal1 (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => Complex.I * φ₀'' (-1 / (Complex.I * t)) * (Complex.I * t)^2 *
                          Complex.exp (Complex.I * π * r * (Complex.I * t)))
                 (Ici (0 : ℝ)) volume := by
  -- This follows from integrableOn_vertical_general with a = 0, b = 0
  sorry

/-- Goal 2: Integrability of φ₀''(-1/(t*I)) * (t*I)² * cexp(π*I*r*(-1 + t*I)) on (1,∞). -/
lemma integrableOn_goal2 (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
                          Complex.exp (π * Complex.I * r * (-1 + t * Complex.I)))
                 (Ioi (1 : ℝ)) volume := by
  -- This follows from integrableOn_vertical_general with a = 0, b = -1
  sorry

/-- Goal 3: Integrability of φ₀''(-1/(t*I + 1)) * (t*I+1)² * cexp(π*I*r*(t*I)) on (1,∞). -/
lemma integrableOn_goal3 (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => φ₀'' (-1 / (t * Complex.I + 1)) * (t * Complex.I + 1)^2 *
                          Complex.exp (π * Complex.I * r * (t * Complex.I)))
                 (Ioi (1 : ℝ)) volume := by
  -- This follows from integrableOn_vertical_general with a = 1, b = 0
  sorry

/-- Goal 4: Integrability of φ₀''(-1/(t*I)) * (t*I)² * cexp(π*I*r*(1 + t*I)) on (1,∞). -/
lemma integrableOn_goal4 (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
                          Complex.exp (π * Complex.I * r * (1 + t * Complex.I)))
                 (Ioi (1 : ℝ)) volume := by
  -- This follows from integrableOn_vertical_general with a = 0, b = 1
  sorry

/-- Goal 5: Integrability of φ₀''(-1/(t*I - 1)) * (t*I-1)² * cexp(π*I*r*(t*I)) on (1,∞). -/
lemma integrableOn_goal5 (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => φ₀'' (-1 / (t * Complex.I - 1)) * (t * Complex.I - 1)^2 *
                          Complex.exp (π * Complex.I * r * (t * Complex.I)))
                 (Ioi (1 : ℝ)) volume := by
  -- This follows from integrableOn_vertical_general with a = -1, b = 0
  sorry

/-- Goal 6: Integrability of I * (φ₀''(-1/(t*I)) * (t*I)² * cexp(π*I*r*(-1 + t*I))) on [0,∞).
    This is I times Goal 2. -/
lemma integrableOn_goal6 (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    Integrable (fun t : ℝ => Complex.I * (φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
                          Complex.exp (π * Complex.I * r * (-1 + t * Complex.I))))
               (volume.restrict (Ici (0 : ℝ))) := by
  sorry

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
