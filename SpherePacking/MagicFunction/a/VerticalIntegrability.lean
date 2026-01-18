/-
Copyright (c) 2026 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
import SpherePacking.MagicFunction.a.ContourEndpoints
import SpherePacking.MagicFunction.Segments
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
    sorry

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
  sorry

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
  -- Direct calculation: -1/(a + I*t) = (-a + I*t) / (a² + t²)
  -- So Im(-1/(a + I*t)) = t / (a² + t²) > 0
  sorry

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
  -- Strategy:
  -- 1. For t > 1, z = a + I*t has Im(z) > 1
  -- 2. By im_neg_inv_pos, -1/z has positive imaginary part
  -- 3. Apply φ₀''_neg_inv_eq_φ₀_S_smul to get φ₀(S•w)
  -- 4. Use norm_φ₀_S_smul_le to bound the φ₀ term
  -- 5. The product |z²| * |cexp(...)| = (a² + t²) * exp(-πrt)
  -- 6. Combined decay: exp(-πrt + O(t)) → 0 for r > 2
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

/-! ## Specific Instantiations

The six integrability goals from Proposition 4.4.6.
-/

/-- Goal 1: Integrability of I * φ₀''(-1/(I*t)) * (I*t)² * cexp(I*π*r*(I*t)) on [0,∞).
    Note: -1/(I*t) = I/t, so this is verticalIntegrandX 0 r t. -/
lemma integrableOn_goal1 (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => Complex.I * φ₀'' (-1 / (Complex.I * t)) * (Complex.I * t)^2 *
                          Complex.exp (Complex.I * π * r * (Complex.I * t)))
                 (Ici (0 : ℝ)) volume := by
  -- Step 1: Reduce to Ioi 0 (singleton {0} has measure zero)
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  -- Step 2: Split Ioi 0 into Ioc 0 1 ∪ Ioi 1
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · -- Integrability on Ioc 0 1 (bounded interval)
    -- The integrand equals verticalIntegrandX 0 r t for t > 0
    have heq : EqOn (fun t : ℝ => Complex.I * φ₀'' (-1 / (Complex.I * t)) * (Complex.I * t)^2 *
                    Complex.exp (Complex.I * π * r * (Complex.I * t)))
               (fun t : ℝ => ContourEndpoints.verticalIntegrandX 0 r t) (Ioc 0 1) := by
      intro t ⟨ht_pos, _⟩
      exact goal1_eq_verticalIntegrandX r t (ne_of_gt ht_pos)
    -- verticalIntegrandX is continuous on (0, ∞), hence on (0, 1]
    -- The integrand → 0 as t → 0+ (super-exponential decay of φ₀'' dominates)
    -- So it extends continuously to [0, 1], and continuous functions on compact sets are integrable
    -- TODO: Show boundedness using cusp decay + finite measure argument
    sorry
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
  -- The integrand equals -I * verticalIntegrandX (-1) r t by goal2_eq_neg_I_verticalIntegrandX
  -- Use integrableOn_verticalIntegrandX with x = -1 on Ici 1, restrict to Ioi 1
  have h : IntegrableOn (fun t => ContourEndpoints.verticalIntegrandX (-1) r t) (Ici 1) volume :=
    ContourEndpoints.integrableOn_verticalIntegrandX hb (-1) r hr
  have h' : IntegrableOn (fun t => ContourEndpoints.verticalIntegrandX (-1) r t) (Ioi 1) volume :=
    h.mono_set Ioi_subset_Ici_self
  -- Scale by -I using Integrable.smul (IntegrableOn = Integrable on restricted measure)
  have hsmul : IntegrableOn (fun t => -Complex.I * ContourEndpoints.verticalIntegrandX (-1) r t)
      (Ioi 1) volume := by
    rw [IntegrableOn] at h' ⊢
    exact Integrable.smul (-Complex.I) h'
  have heq : EqOn (fun t => -Complex.I * ContourEndpoints.verticalIntegrandX (-1) r t)
      (fun t => φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
        Complex.exp (π * Complex.I * r * (-1 + t * Complex.I))) (Ioi 1) := fun t ht =>
    (goal2_eq_neg_I_verticalIntegrandX r t (ne_of_gt (lt_of_lt_of_le one_pos (le_of_lt ht)))).symm
  exact hsmul.congr_fun heq measurableSet_Ioi

/-- Goal 3: Integrability of φ₀''(-1/(t*I + 1)) * (t*I+1)² * cexp(π*I*r*(t*I)) on (1,∞).
    Category B: Shifted Möbius argument at +1. Uses norm_φ₀_S_smul_le. -/
lemma integrableOn_goal3 (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => φ₀'' (-1 / (t * Complex.I + 1)) * (t * Complex.I + 1)^2 *
                          Complex.exp (π * Complex.I * r * (t * Complex.I)))
                 (Ioi (1 : ℝ)) volume := by
  -- -1/(tI+1) has Im = t/(1+t²) > 0 for t > 0, so norm_φ₀_S_smul_le applies
  sorry

/-- Goal 4: Integrability of φ₀''(-1/(t*I)) * (t*I)² * cexp(π*I*r*(1 + t*I)) on (1,∞).
    By goal4_eq_neg_I_verticalIntegrandX, this is -I * verticalIntegrandX 1 r t. -/
lemma integrableOn_goal4 (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
                          Complex.exp (π * Complex.I * r * (1 + t * Complex.I)))
                 (Ioi (1 : ℝ)) volume := by
  -- The integrand equals -I * verticalIntegrandX 1 r t by goal4_eq_neg_I_verticalIntegrandX
  have h : IntegrableOn (fun t => ContourEndpoints.verticalIntegrandX 1 r t) (Ici 1) volume :=
    ContourEndpoints.integrableOn_verticalIntegrandX hb 1 r hr
  have h' : IntegrableOn (fun t => ContourEndpoints.verticalIntegrandX 1 r t) (Ioi 1) volume :=
    h.mono_set Ioi_subset_Ici_self
  have hsmul : IntegrableOn (fun t => -Complex.I * ContourEndpoints.verticalIntegrandX 1 r t)
      (Ioi 1) volume := by
    rw [IntegrableOn] at h' ⊢
    exact Integrable.smul (-Complex.I) h'
  have heq : EqOn (fun t => -Complex.I * ContourEndpoints.verticalIntegrandX 1 r t)
      (fun t => φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
        Complex.exp (π * Complex.I * r * (1 + t * Complex.I))) (Ioi 1) := fun t ht =>
    (goal4_eq_neg_I_verticalIntegrandX r t (ne_of_gt (lt_of_lt_of_le one_pos (le_of_lt ht)))).symm
  exact hsmul.congr_fun heq measurableSet_Ioi

/-- Goal 5: Integrability of φ₀''(-1/(t*I - 1)) * (t*I-1)² * cexp(π*I*r*(t*I)) on (1,∞).
    Category B: Shifted Möbius argument at -1. Uses norm_φ₀_S_smul_le. -/
lemma integrableOn_goal5 (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => φ₀'' (-1 / (t * Complex.I - 1)) * (t * Complex.I - 1)^2 *
                          Complex.exp (π * Complex.I * r * (t * Complex.I)))
                 (Ioi (1 : ℝ)) volume := by
  -- -1/(tI-1) has Im = t/(1+t²) > 0 for t > 0, so norm_φ₀_S_smul_le applies
  sorry

/-- Goal 6: Integrability of I * (φ₀''(-1/(t*I)) * (t*I)² * cexp(π*I*r*(-1 + t*I))) on [0,∞).
    By goal6_eq_verticalIntegrandX, this is verticalIntegrandX (-1) r t. -/
lemma integrableOn_goal6 (hb : ContourEndpoints.PhiBounds) (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => Complex.I * (φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
                          Complex.exp (π * Complex.I * r * (-1 + t * Complex.I))))
                 (Ici (0 : ℝ)) volume := by
  -- Step 1: Reduce to Ioi 0 (singleton {0} has measure zero)
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  -- Step 2: Split Ioi 0 into Ioc 0 1 ∪ Ioi 1
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · -- Integrability on Ioc 0 1 (bounded interval)
    -- The integrand equals verticalIntegrandX (-1) r t for t > 0
    have heq : EqOn (fun t : ℝ => Complex.I * (φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
                      Complex.exp (π * Complex.I * r * (-1 + t * Complex.I))))
               (fun t : ℝ => ContourEndpoints.verticalIntegrandX (-1) r t) (Ioc 0 1) := by
      intro t ⟨ht_pos, _⟩
      exact goal6_eq_verticalIntegrandX r t (ne_of_gt ht_pos)
    -- verticalIntegrandX is continuous on (0, ∞), hence on (0, 1]
    sorry
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
