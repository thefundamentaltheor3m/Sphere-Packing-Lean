/-
Copyright (c) 2025 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/

import SpherePacking.MagicFunction.a.Basic
import SpherePacking.MagicFunction.a.Schwartz
import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.ModularForms.Derivative
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integrability of Iⱼ over ℝ⁸

This file proves that the contour integral components I₁-I₆ are integrable over ℝ⁸,
enabling Fubini/Tonelli for swapping ∫_{ℝ⁸} and ∫_{contour} in the Fourier eigenfunction proofs.

## Contour classification

The six contour segments fall into three classes with different proof strategies:

- **Class A** (safe, Im ≥ 1): I₂, I₄ — horizontal segments where Im(z) = 1 throughout.
  Bounded-on-compact argument for φ₀'', combined with Gaussian decay.

- **Class B** (Im → 0 at endpoint): I₁, I₃, I₅ — vertical segments approaching the real axis.
  Require substitution s = 1/t and Corollary 7.5 (φ₀ bound). Use `Ioc 0 1` to avoid endpoint.

- **Class C** (unbounded tail): I₆ — vertical ray from i to i∞.
  Direct application of Corollary 7.5: `|φ₀(z)| ≤ C₀·e^{-2π·Im(z)}` for Im(z) > 1/2.

## Main results

### Level 2: Product integrability (main goal for Fubini)
- `I₂_integrand_integrable`, `I₄_integrand_integrable`: Class A (easiest)
- `I₆_integrand_integrable`: Class C (tail)
- `I₁_integrand_integrable`, `I₃_integrand_integrable`, `I₅_integrand_integrable`: Class B

### Level 3: Fubini swap lemmas
- `I₁_integral_swap` through `I₆_integral_swap`: Swap ∫_{ℝ⁸} and ∫_{contour}

### Level 1: Basic integrability (corollaries)
- `I₁_integrable` through `I₆_integrable`: Each Iⱼ is integrable on ℝ⁸

## References

- Blueprint Corollary 7.5: φ₀ bound `|φ₀(z)| ≤ C₀·e^{-2π·Im(z)}` for Im(z) > 1/2
- Blueprint Section 7 for contour definitions and integral representations
-/

open MeasureTheory Complex Real Set intervalIntegral

local notation "V" => EuclideanSpace ℝ (Fin 8)

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions

noncomputable section

/-! ## Workhorse Lemmas

These lemmas are used across multiple integrability proofs.
-/

/-- Unfold φ₀'' to φ₀ when the imaginary part is positive. -/
lemma φ₀''_eq (z : ℂ) (hz : 0 < z.im) : φ₀'' z = φ₀ ⟨z, hz⟩ := by
  simp only [φ₀'', hz, dite_true]

/-- Norm of cexp(-π * ‖x‖²) equals exp(-π * ‖x‖²). -/
lemma norm_cexp_neg_pi_norm_sq (x : V) : ‖cexp ((-π : ℂ) * ‖x‖^2)‖ = Real.exp (-π * ‖x‖^2) := by
  rw [Complex.norm_exp]; simp [sq]

/-- Norm of cexp(-π * ‖x‖² * t) equals exp(-π * ‖x‖² * t). -/
lemma norm_cexp_neg_pi_norm_sq_mul (x : V) (t : ℝ) :
    ‖cexp (-π * ‖x‖^2 * t)‖ = Real.exp (-π * ‖x‖^2 * t) := by
  rw [Complex.norm_exp]; simp [sq]

/-- Gaussian integrability on ℝ⁸: `∫_{ℝ⁸} e^{-c·‖x‖²} < ∞` for c > 0. -/
lemma gaussian_integrable_R8 (c : ℝ) (hc : 0 < c) :
    Integrable (fun x : V => Real.exp (-c * ‖x‖^2)) := by
  -- Use the complex Gaussian integrability with c = 0, w = 0
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    (b := c) (by simp [hc]) (0 : ℂ) (0 : V)
  simp only [inner_zero_left, ofReal_zero, mul_zero, add_zero] at h
  -- Now h : Integrable (fun v => cexp (-c * ‖v‖^2))
  -- Extract real integrability from complex
  have hf : ∀ x : V, Real.exp (-c * ‖x‖^2) = ‖cexp (-(c : ℂ) * ‖x‖^2)‖ := fun x => by
    rw [Complex.norm_exp]
    congr 1
    simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, sq]
  simp_rw [hf]
  exact h.norm

/-- Scaled Gaussian integrability: `∫_{ℝ⁸} e^{-c·t·‖x‖²} < ∞` for c > 0, t > 0.
Useful for Class A/C where we have uniform lower bounds on Im(z). -/
lemma gaussian_integrable_scaled (c : ℝ) (t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    Integrable (fun x : V => Real.exp (-c * t * ‖x‖^2)) := by
  have h : -c * t = -(c * t) := by ring
  simp_rw [h]
  exact gaussian_integrable_R8 (c * t) (mul_pos hc ht)

/-- φ₀ : ℍ → ℂ is continuous.
Follows from continuity of E₂, E₄, E₆, Δ (via their MDifferentiability) and Δ ≠ 0. -/
lemma φ₀_continuous : Continuous φ₀ := by
  unfold φ₀
  have hE₂ : Continuous E₂ := MDifferentiable.continuous E₂_holo'
  have hE₄ : Continuous (fun z : UpperHalfPlane => E₄ z) := MDifferentiable.continuous E₄.holo'
  have hE₆ : Continuous (fun z : UpperHalfPlane => E₆ z) := MDifferentiable.continuous E₆.holo'
  have hΔ : Continuous (fun z : UpperHalfPlane => Δ z) := MDifferentiable.continuous Delta.holo'
  have h24 : Continuous (fun z : UpperHalfPlane => E₂ z * E₄ z) := hE₂.mul hE₄
  have h246 : Continuous (fun z : UpperHalfPlane => E₂ z * E₄ z - E₆ z) := h24.sub hE₆
  have h_sq : Continuous (fun z : UpperHalfPlane => (E₂ z * E₄ z - E₆ z)^2) := h246.pow 2
  exact Continuous.div h_sq hΔ (fun z => Δ_ne_zero z)

/-! ## Class A: Safe segments (I₂, I₄)

For these segments, the argument to φ₀'' has Im ≥ 1/2 throughout:
- I₂: z = -1/(t + I) has Im = 1/(t² + 1) ≥ 1/2 for t ∈ [0,1]
- I₄: z = -1/(-t + I) has Im = 1/(t² + 1) ≥ 1/2 for t ∈ [0,1]

So `norm_φ₀_le` applies, giving uniform bounds on φ₀''.
Combined with Gaussian decay `e^{-π‖x‖²}`, we get product integrability.
-/

section ClassA

/-- For t ∈ [0,1], Im(-1/(t + I)) ≥ 1/2. -/
lemma im_neg_inv_t_add_I (t : ℝ) (ht : t ∈ Icc 0 1) : 1/2 ≤ (-1 / (t + I)).im := by
  have h1 : (t + I) ≠ 0 := by simp [Complex.ext_iff]
  have hns : normSq (t + I) = t^2 + 1 := by simp [normSq, sq]
  have him : (t + I).im = 1 := by simp
  simp only [neg_div, neg_im, one_div, inv_im, hns, him, neg_neg]
  -- Goal: 2⁻¹ ≤ (t^2 + 1)⁻¹, i.e., t^2 + 1 ≤ 2
  have ht2 : t^2 ≤ 1 := by nlinarith [ht.1, ht.2, sq_nonneg t]
  have h_pos : 0 < t^2 + 1 := by positivity
  rw [← one_div, ← one_div, one_div_le_one_div (by positivity) h_pos]
  linarith

/-- For t ∈ [0,1], Im(-1/(-t + I)) ≥ 1/2. -/
lemma im_neg_inv_neg_t_add_I (t : ℝ) (ht : t ∈ Icc 0 1) : 1/2 ≤ (-1 / (-t + I)).im := by
  have h1 : (-t + I) ≠ 0 := by simp [Complex.ext_iff]
  have hns : normSq (-t + I) = t^2 + 1 := by simp [normSq, sq]
  have him : (-t + I).im = 1 := by simp
  simp only [neg_div, neg_im, one_div, inv_im, hns, him, neg_neg]
  -- Goal: 2⁻¹ ≤ (t^2 + 1)⁻¹, i.e., t^2 + 1 ≤ 2
  have ht2 : t^2 ≤ 1 := by nlinarith [ht.1, ht.2, sq_nonneg t]
  have h_pos : 0 < t^2 + 1 := by positivity
  rw [← one_div, ← one_div, one_div_le_one_div (by positivity) h_pos]
  linarith

/-- For t ∈ [0,1], |(t + I)²| ≤ 2. -/
lemma norm_sq_t_add_I_le (t : ℝ) (ht : t ∈ Icc 0 1) : ‖(t + I) ^ 2‖ ≤ 2 := by
  rw [norm_pow, ← normSq_eq_norm_sq]
  simp only [normSq_apply, add_re, ofReal_re, I_re, add_zero, add_im, ofReal_im, I_im, zero_add]
  nlinarith [sq_nonneg t, ht.1, ht.2]

/-- For t ∈ [0,1], |(-t + I)²| ≤ 2. -/
lemma norm_sq_neg_t_add_I_le (t : ℝ) (ht : t ∈ Icc 0 1) : ‖(-t + I) ^ 2‖ ≤ 2 := by
  rw [norm_pow, ← normSq_eq_norm_sq]
  simp only [normSq_apply, add_re, neg_re, ofReal_re, I_re, add_zero, add_im, neg_im,
    ofReal_im, I_im]
  nlinarith [sq_nonneg t, ht.1, ht.2]

/-- For t ∈ [0,1], the positive imaginary part of -1/(t+I). -/
lemma im_neg_inv_t_add_I_pos (t : ℝ) (ht : t ∈ Icc 0 1) : 0 < (-1 / (t + I)).im := by
  have h := im_neg_inv_t_add_I t ht
  linarith

/-- For t ∈ [0,1], the positive imaginary part of -1/(-t+I). -/
lemma im_neg_inv_neg_t_add_I_pos (t : ℝ) (ht : t ∈ Icc 0 1) : 0 < (-1 / (-t + I)).im := by
  have h := im_neg_inv_neg_t_add_I t ht
  linarith

/-- For any t ∈ ℝ, Im(-1/(t+I)) = 1/(t² + 1) > 0. -/
lemma im_neg_inv_t_add_I_pos_general (t : ℝ) : 0 < (-1 / (t + I)).im := by
  simp only [neg_div, neg_im, one_div, inv_im, add_im, ofReal_im, I_im, zero_add, neg_neg]
  have hns : normSq (t + I) = t^2 + 1 := by simp [normSq, sq]
  rw [hns]
  positivity

/-- The path t ↦ -1/(t+I) is continuous on ℝ. -/
lemma continuous_neg_inv_t_add_I : Continuous (fun t : ℝ => -1 / (t + I)) := by
  apply Continuous.div continuous_const
  · exact continuous_ofReal.add continuous_const
  · intro t h
    have him : (t + I).im = 0 := by rw [h]; simp
    simp only [add_im, ofReal_im, I_im, zero_add] at him
    exact one_ne_zero him

/-- The map t ↦ φ₀''(-1/(t+I)) is continuous.
This follows from: (1) t ↦ -1/(t+I) is continuous, (2) for all t, Im(-1/(t+I)) > 0,
(3) φ₀ is holomorphic on ℍ, hence continuous. -/
lemma continuous_φ₀''_I₂_param : Continuous (fun t : ℝ => φ₀'' (-1 / (t + I))) := by
  -- Factor through ℍ using the fact that Im > 0 for all t
  have h_im_pos : ∀ t : ℝ, 0 < (-1 / (t + I)).im := im_neg_inv_t_add_I_pos_general
  -- Lift the path to ℍ
  have h_lift : Continuous (fun t : ℝ => (⟨-1 / (t + I), h_im_pos t⟩ : UpperHalfPlane)) :=
    Continuous.subtype_mk continuous_neg_inv_t_add_I h_im_pos
  -- Show φ₀'' equals φ₀ on the image (which is in UHP)
  have h_eq : (fun t : ℝ => φ₀'' (-1 / (t + I))) =
              (fun t : ℝ => φ₀ ⟨-1 / (t + I), h_im_pos t⟩) := by
    ext t; rw [φ₀''_eq _ (h_im_pos t)]
  rw [h_eq]
  exact φ₀_continuous.comp h_lift

/-- Bound on φ₀'' for I₂ segment: |φ₀''(-1/(t+I))| ≤ C₀ * e^{-π} for t ∈ [0,1).
Uses `norm_φ₀_le` (Cor 7.5) with Im > 1/2.
Note: At t=1, Im = 1/2 exactly, so we use [0,1) instead of [0,1]. -/
lemma norm_φ₀''_I₂_bound_Ico : ∃ C₀ > 0, ∀ t : ℝ, t ∈ Ico 0 1 →
    ‖φ₀'' (-1 / (t + I))‖ ≤ C₀ * Real.exp (-π) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  refine ⟨C₀, hC₀_pos, fun t ht => ?_⟩
  have ht' : t ∈ Icc 0 1 := Ico_subset_Icc_self ht
  have him_pos : 0 < (-1 / (t + I)).im := im_neg_inv_t_add_I_pos t ht'
  have him_ge : 1/2 < (-1 / (t + I)).im := by
    -- For t ∈ [0,1), Im = 1/(t²+1) > 1/2 since t² < 1
    simp only [neg_div, neg_im, one_div, inv_im, add_im, ofReal_im, I_im, zero_add, neg_neg]
    have hns : normSq (t + I) = t^2 + 1 := by simp [normSq, sq]
    rw [hns]
    have ht1 : t < 1 := ht.2
    have ht2 : t^2 < 1 := by nlinarith [sq_nonneg t, ht.1]
    have h_lt : t^2 + 1 < 2 := by linarith
    exact (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 2) (by positivity : (0 : ℝ) < t^2 + 1)).mpr h_lt
  let z : UpperHalfPlane := ⟨-1 / (t + I), him_pos⟩
  have hz_im : z.im = (-1 / (t + I)).im := rfl
  rw [φ₀''_eq _ him_pos]
  calc ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im) := hC₀ z (by rw [hz_im]; exact him_ge)
    _ ≤ C₀ * Real.exp (-π) := by
        gcongr
        simp only [neg_mul, neg_le_neg_iff]
        have him_ge' : 1/2 < z.im := by rw [hz_im]; exact him_ge
        have : 2 * π * z.im > 2 * π * (1/2) := by
          apply mul_lt_mul_of_pos_left him_ge'
          norm_num [Real.pi_pos]
        linarith [Real.pi_pos]

/-- For any t ∈ ℝ, Im(-1/(-t+I)) = 1/(t² + 1) > 0. -/
lemma im_neg_inv_neg_t_add_I_pos_general (t : ℝ) : 0 < (-1 / (-t + I)).im := by
  simp only [neg_div, neg_im, one_div, inv_im, add_im, neg_im, ofReal_im, I_im, neg_neg]
  have hns : normSq (-t + I) = t^2 + 1 := by simp [normSq, sq]
  rw [hns]
  positivity

/-- The path t ↦ -1/(-t+I) is continuous on ℝ. -/
lemma continuous_neg_inv_neg_t_add_I : Continuous (fun t : ℝ => -1 / (-t + I)) := by
  apply Continuous.div continuous_const
  · exact (continuous_ofReal.neg).add continuous_const
  · intro t h
    have him : (-t + I).im = 0 := by rw [h]; simp
    simp only [add_im, neg_im, ofReal_im, I_im] at him
    norm_num at him

/-- The map t ↦ φ₀''(-1/(-t+I)) is continuous. -/
lemma continuous_φ₀''_I₄_param : Continuous (fun t : ℝ => φ₀'' (-1 / (-t + I))) := by
  have h_im_pos : ∀ t : ℝ, 0 < (-1 / (-t + I)).im := im_neg_inv_neg_t_add_I_pos_general
  have h_lift : Continuous (fun t : ℝ => (⟨-1 / (-t + I), h_im_pos t⟩ : UpperHalfPlane)) :=
    Continuous.subtype_mk continuous_neg_inv_neg_t_add_I h_im_pos
  have h_eq : (fun t : ℝ => φ₀'' (-1 / (-t + I))) =
              (fun t : ℝ => φ₀ ⟨-1 / (-t + I), h_im_pos t⟩) := by
    ext t; rw [φ₀''_eq _ (h_im_pos t)]
  rw [h_eq]
  exact φ₀_continuous.comp h_lift

/-- Bound on φ₀'' for I₄ segment: |φ₀''(-1/(-t+I))| ≤ C₀ * e^{-π} for t ∈ [0,1).
Uses `norm_φ₀_le` (Cor 7.5) with Im > 1/2. -/
lemma norm_φ₀''_I₄_bound_Ico : ∃ C₀ > 0, ∀ t : ℝ, t ∈ Ico 0 1 →
    ‖φ₀'' (-1 / (-t + I))‖ ≤ C₀ * Real.exp (-π) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  refine ⟨C₀, hC₀_pos, fun t ht => ?_⟩
  have ht' : t ∈ Icc 0 1 := Ico_subset_Icc_self ht
  have him_pos : 0 < (-1 / (-t + I)).im := im_neg_inv_neg_t_add_I_pos t ht'
  have him_ge : 1/2 < (-1 / (-t + I)).im := by
    have hns : normSq (-t + I) = t^2 + 1 := by simp [normSq, sq]
    have him_eq : (-1 / (-t + I)).im = 1 / (t^2 + 1) := by
      simp only [neg_div, neg_im, one_div, inv_im, add_im, neg_im, ofReal_im, I_im, neg_neg, hns]
      ring
    rw [him_eq, one_div, one_div]
    have ht1 : t < 1 := ht.2
    have ht2 : t^2 < 1 := by nlinarith [sq_nonneg t, ht.1]
    have h_lt : t^2 + 1 < 2 := by linarith
    exact (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 2) (by positivity : (0 : ℝ) < t^2 + 1)).mpr h_lt
  let z : UpperHalfPlane := ⟨-1 / (-t + I), him_pos⟩
  have hz_im : z.im = (-1 / (-t + I)).im := rfl
  rw [φ₀''_eq _ him_pos]
  calc ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im) := hC₀ z (by rw [hz_im]; exact him_ge)
    _ ≤ C₀ * Real.exp (-π) := by
        gcongr
        simp only [neg_mul, neg_le_neg_iff]
        have him_ge' : 1/2 < z.im := by rw [hz_im]; exact him_ge
        have : 2 * π * z.im > 2 * π * (1/2) := by
          apply mul_lt_mul_of_pos_left him_ge'
          norm_num [Real.pi_pos]
        linarith [Real.pi_pos]

/-- The integrand for I₂ over V × [0,1].
Using the simplified form from `I₂'_eq`: integrand has factors
`φ₀'' (-1 / (t + I)) * (t + I)² * e^{-πIr} * e^{πIrt} * e^{-πr}`. -/
def I₂_integrand (p : V × ℝ) : ℂ :=
  φ₀'' (-1 / (p.2 + I)) * (p.2 + I) ^ 2 *
  cexp (-π * I * ‖p.1‖^2) * cexp (π * I * ‖p.1‖^2 * p.2) * cexp (-π * ‖p.1‖^2)

/-- The integrand for I₄ over V × [0,1].
Using the simplified form from `I₄'_eq`. -/
def I₄_integrand (p : V × ℝ) : ℂ :=
  -1 * φ₀'' (-1 / (-p.2 + I)) * (-p.2 + I) ^ 2 *
  cexp (π * I * ‖p.1‖^2) * cexp (-π * I * ‖p.1‖^2 * p.2) * cexp (-π * ‖p.1‖^2)

/-- The I₂ integrand is continuous as a function V × ℝ → ℂ.
Follows from: continuity of φ₀''(-1/(t+I)), polynomial in t, and cexp compositions. -/
lemma I₂_integrand_continuous : Continuous I₂_integrand := by
  unfold I₂_integrand
  -- Each factor is continuous in (x, t)
  have h1 : Continuous (fun p : V × ℝ => φ₀'' (-1 / (p.2 + I))) :=
    continuous_φ₀''_I₂_param.comp continuous_snd
  have h2 : Continuous (fun p : V × ℝ => (p.2 + I) ^ 2) :=
    (continuous_ofReal.comp continuous_snd).add continuous_const |>.pow 2
  have h_norm_sq : Continuous (fun p : V × ℝ => (‖p.1‖^2 : ℂ)) := by
    have h1 : Continuous (fun p : V × ℝ => ‖p.1‖^2) := (continuous_norm.comp continuous_fst).pow 2
    have h2 : Continuous (fun r : ℝ => (r : ℂ)) := continuous_ofReal
    have h3 : (fun p : V × ℝ => (‖p.1‖^2 : ℂ)) = (fun r : ℝ => (r : ℂ)) ∘ (fun p => ‖p.1‖^2) := by
      funext p
      simp only [Function.comp_apply, ofReal_pow]
    rw [h3]
    exact h2.comp h1
  have h3 : Continuous (fun p : V × ℝ => cexp (-π * I * ‖p.1‖^2)) :=
    Complex.continuous_exp.comp (continuous_const.mul h_norm_sq)
  have h4 : Continuous (fun p : V × ℝ => cexp (π * I * ‖p.1‖^2 * p.2)) :=
    Complex.continuous_exp.comp ((continuous_const.mul h_norm_sq).mul
      (continuous_ofReal.comp continuous_snd))
  have h5 : Continuous (fun p : V × ℝ => cexp (-π * ‖p.1‖^2)) :=
    Complex.continuous_exp.comp (continuous_const.mul h_norm_sq)
  exact ((h1.mul h2).mul h3).mul h4 |>.mul h5

/-- The norm of I₂_integrand is bounded by C * exp(-π‖x‖²) for all (x, t) ∈ V × [0,1].
Uses continuity of φ₀'' on [0,1] to get a uniform bound. -/
lemma I₂_integrand_norm_bound : ∃ C > 0, ∀ x : V, ∀ t ∈ Icc (0 : ℝ) 1,
    ‖I₂_integrand (x, t)‖ ≤ C * Real.exp (-π * ‖x‖^2) := by
  -- Get a bound on |φ₀''(-1/(t+I))| for t ∈ [0,1] using continuity
  -- Since φ₀''(-1/(t+I)) is continuous on the compact set [0,1], it's bounded
  have h_bdd : BddAbove ((fun t : ℝ => ‖φ₀'' (-1 / (t + I))‖) '' Icc (0 : ℝ) 1) :=
    IsCompact.bddAbove_image isCompact_Icc
      (continuous_norm.comp continuous_φ₀''_I₂_param).continuousOn
  -- Get an upper bound M ≥ 0 such that all elements of the set are ≤ M
  obtain ⟨M, hM_nonneg, hM_le⟩ := h_bdd.exists_ge (0 : ℝ)
  -- hM_le says: for all y in the image, y ≤ M
  -- The bound constant: combine M with the |(t+I)²| ≤ 2 bound
  refine ⟨2 * (M + 1), by positivity, fun x t ht => ?_⟩
  unfold I₂_integrand
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  -- |φ₀''(...)| ≤ M (the value is in the image set)
  have h_φ : ‖φ₀'' (-1 / (t + I))‖ ≤ M := by
    apply hM_le
    exact ⟨t, ht, rfl⟩
  -- |(t + I)²| ≤ 2
  have h_sq : ‖(t + I) ^ 2‖ ≤ 2 := norm_sq_t_add_I_le t ht
  -- Phase factors have unit norm (use Complex.norm_exp_ofReal_mul_I)
  have h_phase1 : ‖cexp (-π * I * ‖x‖^2)‖ = 1 := by
    rw [show (-π * I * ‖x‖^2 : ℂ) = ↑(-π * ‖x‖^2) * I from by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have h_phase2 : ‖cexp (π * I * ‖x‖^2 * t)‖ = 1 := by
    rw [show (π * I * ‖x‖^2 * t : ℂ) = ↑(π * ‖x‖^2 * t) * I from by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have h_gauss := norm_cexp_neg_pi_norm_sq x
  -- Combine the bounds using explicit multiplication
  have h1 : ‖φ₀'' (-1 / (t + I))‖ * ‖(t + I) ^ 2‖ ≤ M * 2 := by
    calc ‖φ₀'' (-1 / (t + I))‖ * ‖(t + I) ^ 2‖
        ≤ M * ‖(t + I) ^ 2‖ := by apply mul_le_mul_of_nonneg_right h_φ (norm_nonneg _)
      _ ≤ M * 2 := by apply mul_le_mul_of_nonneg_left h_sq hM_nonneg
  calc ‖φ₀'' (-1 / (t + I))‖ * ‖(t + I) ^ 2‖ * ‖cexp (-π * I * ‖x‖^2)‖ *
       ‖cexp (π * I * ‖x‖^2 * t)‖ * ‖cexp ((-π : ℂ) * ‖x‖^2)‖
       = ‖φ₀'' (-1 / (t + I))‖ * ‖(t + I) ^ 2‖ * 1 * 1 * Real.exp (-π * ‖x‖^2) := by
         rw [h_phase1, h_phase2, h_gauss]
    _ = ‖φ₀'' (-1 / (t + I))‖ * ‖(t + I) ^ 2‖ * Real.exp (-π * ‖x‖^2) := by ring
    _ ≤ M * 2 * Real.exp (-π * ‖x‖^2) := by
         apply mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ ≤ 2 * (M + 1) * Real.exp (-π * ‖x‖^2) := by nlinarith [Real.exp_pos (-π * ‖x‖^2), hM_nonneg]

/-- I₂ integrand is integrable on V × [0,1] (Class A segment).

Proof: Continuous, bounded by C * exp(-π‖x‖²), and Gaussian is integrable on V. -/
theorem I₂_integrand_integrable :
    Integrable I₂_integrand (volume.prod (volume.restrict (Icc 0 1))) := by
  -- Use Integrable.mono' with dominating function C * exp(-π‖x‖²) ∘ fst
  obtain ⟨C, hC_pos, hC⟩ := I₂_integrand_norm_bound
  -- The dominating function
  let g : V × ℝ → ℝ := fun p => C * Real.exp (-π * ‖p.1‖^2)
  -- Step 1: I₂_integrand is AEStronglyMeasurable (it's continuous)
  have h_meas : AEStronglyMeasurable I₂_integrand (volume.prod (volume.restrict (Icc 0 1))) :=
    I₂_integrand_continuous.aestronglyMeasurable
  -- Step 2: The dominating function g is integrable on the product
  have h_g_int : Integrable g (volume.prod (volume.restrict (Icc 0 1))) := by
    -- g(x, t) = C * exp(-π‖x‖²) depends only on x
    -- ∫∫ g = C * ∫_V exp(-π‖x‖²) dx * ∫_{[0,1]} 1 dt = C * (Gaussian integral) * 1
    have h_fst : g = (fun p : V × ℝ => C * Real.exp (-π * ‖p.1‖^2)) := rfl
    rw [h_fst]
    -- Establish that the restricted measure is a finite measure
    haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
      ⟨by simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
          exact measure_Icc_lt_top⟩
    -- Now use Integrable.comp_fst which requires IsFiniteMeasure on the second factor
    have h_gauss : Integrable (fun x : V => C * Real.exp (-π * ‖x‖^2)) volume :=
      (gaussian_integrable_R8 π Real.pi_pos).const_mul C
    exact h_gauss.comp_fst (volume.restrict (Icc 0 1))
  -- Step 3: The bound ‖I₂_integrand‖ ≤ g holds a.e. on V × [0,1]
  -- The product measure with restriction only sees t ∈ [0,1], where the bound holds
  have h_bound : ∀ᵐ p ∂(volume.prod (volume.restrict (Icc 0 1))), ‖I₂_integrand p‖ ≤ g p := by
    -- The bound holds for all (x, t) with t ∈ [0,1], and the product measure only sees such t
    -- First show that a.e. under restricted measure, t ∈ [0,1]
    have h_ae_snd : ∀ᵐ (t : ℝ) ∂(volume.restrict (Icc 0 1)), t ∈ Icc 0 1 := by
      rw [ae_restrict_iff' measurableSet_Icc]
      exact ae_of_all _ (fun _ h => h)
    -- For product measures, use ae_prod_iff_ae_ae with measurability of the bound set
    have h_meas_bound : MeasurableSet {p : V × ℝ | ‖I₂_integrand p‖ ≤ g p} := by
      apply measurableSet_le
      · exact I₂_integrand_continuous.norm.measurable
      · exact (continuous_const.mul (Real.continuous_exp.comp
          (continuous_const.mul ((continuous_norm.comp continuous_fst).pow 2)))).measurable
    rw [Measure.ae_prod_iff_ae_ae h_meas_bound]
    apply ae_of_all
    intro x
    filter_upwards [h_ae_snd] with t ht
    exact hC x t ht
  exact Integrable.mono' h_g_int h_meas h_bound

/-- The I₄ integrand is continuous as a function V × ℝ → ℂ. -/
lemma I₄_integrand_continuous : Continuous I₄_integrand := by
  unfold I₄_integrand
  have h1 : Continuous (fun p : V × ℝ => φ₀'' (-1 / (-p.2 + I))) :=
    continuous_φ₀''_I₄_param.comp continuous_snd
  have h2 : Continuous (fun p : V × ℝ => (-p.2 + I) ^ 2) :=
    ((continuous_ofReal.comp continuous_snd).neg.add continuous_const).pow 2
  have h_norm_sq : Continuous (fun p : V × ℝ => (‖p.1‖^2 : ℂ)) := by
    have h1 : Continuous (fun p : V × ℝ => ‖p.1‖^2) := (continuous_norm.comp continuous_fst).pow 2
    have h2 : Continuous (fun r : ℝ => (r : ℂ)) := continuous_ofReal
    have h3 : (fun p : V × ℝ => (‖p.1‖^2 : ℂ)) = (fun r : ℝ => (r : ℂ)) ∘ (fun p => ‖p.1‖^2) := by
      funext p; simp only [Function.comp_apply, ofReal_pow]
    rw [h3]; exact h2.comp h1
  have h3 : Continuous (fun p : V × ℝ => cexp (π * I * ‖p.1‖^2)) :=
    Complex.continuous_exp.comp (continuous_const.mul h_norm_sq)
  have h4 : Continuous (fun p : V × ℝ => cexp (-π * I * ‖p.1‖^2 * p.2)) :=
    Complex.continuous_exp.comp ((continuous_const.mul h_norm_sq).mul
      (continuous_ofReal.comp continuous_snd))
  have h5 : Continuous (fun p : V × ℝ => cexp (-π * ‖p.1‖^2)) :=
    Complex.continuous_exp.comp (continuous_const.mul h_norm_sq)
  exact ((continuous_const.mul h1).mul h2).mul h3 |>.mul h4 |>.mul h5

/-- The norm of I₄_integrand is bounded by C * exp(-π‖x‖²) for all (x, t) ∈ V × [0,1]. -/
lemma I₄_integrand_norm_bound : ∃ C > 0, ∀ x : V, ∀ t ∈ Icc (0 : ℝ) 1,
    ‖I₄_integrand (x, t)‖ ≤ C * Real.exp (-π * ‖x‖^2) := by
  have h_bdd : BddAbove ((fun t : ℝ => ‖φ₀'' (-1 / (-t + I))‖) '' Icc (0 : ℝ) 1) :=
    IsCompact.bddAbove_image isCompact_Icc
      (continuous_norm.comp continuous_φ₀''_I₄_param).continuousOn
  obtain ⟨M, hM_nonneg, hM_le⟩ := h_bdd.exists_ge (0 : ℝ)
  refine ⟨2 * (M + 1), by positivity, fun x t ht => ?_⟩
  unfold I₄_integrand
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
  have h_neg1 : ‖(-1 : ℂ)‖ = 1 := by simp
  have h_φ : ‖φ₀'' (-1 / (-t + I))‖ ≤ M := by apply hM_le; exact ⟨t, ht, rfl⟩
  have h_sq : ‖(-t + I) ^ 2‖ ≤ 2 := norm_sq_neg_t_add_I_le t ht
  have h_phase1 : ‖cexp (π * I * ‖x‖^2)‖ = 1 := by
    rw [show (π * I * ‖x‖^2 : ℂ) = ↑(π * ‖x‖^2) * I from by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have h_phase2 : ‖cexp (-π * I * ‖x‖^2 * t)‖ = 1 := by
    rw [show (-π * I * ‖x‖^2 * t : ℂ) = ↑(-π * ‖x‖^2 * t) * I from by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have h_gauss := norm_cexp_neg_pi_norm_sq x
  have h1 : ‖φ₀'' (-1 / (-t + I))‖ * ‖(-t + I) ^ 2‖ ≤ M * 2 := by
    calc ‖φ₀'' (-1 / (-t + I))‖ * ‖(-t + I) ^ 2‖
        ≤ M * ‖(-t + I) ^ 2‖ := by apply mul_le_mul_of_nonneg_right h_φ (norm_nonneg _)
      _ ≤ M * 2 := by apply mul_le_mul_of_nonneg_left h_sq hM_nonneg
  calc ‖(-1 : ℂ)‖ * ‖φ₀'' (-1 / (-t + I))‖ * ‖(-t + I) ^ 2‖ * ‖cexp (π * I * ‖x‖^2)‖ *
       ‖cexp (-π * I * ‖x‖^2 * t)‖ * ‖cexp ((-π : ℂ) * ‖x‖^2)‖
       = 1 * ‖φ₀'' (-1 / (-t + I))‖ * ‖(-t + I) ^ 2‖ * 1 * 1 * Real.exp (-π * ‖x‖^2) := by
         rw [h_neg1, h_phase1, h_phase2, h_gauss]
    _ = ‖φ₀'' (-1 / (-t + I))‖ * ‖(-t + I) ^ 2‖ * Real.exp (-π * ‖x‖^2) := by ring
    _ ≤ M * 2 * Real.exp (-π * ‖x‖^2) := by
         apply mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ ≤ 2 * (M + 1) * Real.exp (-π * ‖x‖^2) := by nlinarith [Real.exp_pos (-π * ‖x‖^2), hM_nonneg]

/-- I₄ integrand is integrable on V × [0,1] (Class A segment).
Strategy: Same as I₂ - φ₀'' bounded via Im ≥ 1/2, Gaussian decay dominates. -/
theorem I₄_integrand_integrable :
    Integrable I₄_integrand (volume.prod (volume.restrict (Icc 0 1))) := by
  obtain ⟨C, hC_pos, hC⟩ := I₄_integrand_norm_bound
  let g : V × ℝ → ℝ := fun p => C * Real.exp (-π * ‖p.1‖^2)
  have h_meas : AEStronglyMeasurable I₄_integrand (volume.prod (volume.restrict (Icc 0 1))) :=
    I₄_integrand_continuous.aestronglyMeasurable
  have h_g_int : Integrable g (volume.prod (volume.restrict (Icc 0 1))) := by
    have h_fst : g = (fun p : V × ℝ => C * Real.exp (-π * ‖p.1‖^2)) := rfl
    rw [h_fst]
    haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
      ⟨by simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
          exact measure_Icc_lt_top⟩
    have h_gauss : Integrable (fun x : V => C * Real.exp (-π * ‖x‖^2)) volume :=
      (gaussian_integrable_R8 π Real.pi_pos).const_mul C
    exact h_gauss.comp_fst (volume.restrict (Icc 0 1))
  have h_bound : ∀ᵐ p ∂(volume.prod (volume.restrict (Icc 0 1))), ‖I₄_integrand p‖ ≤ g p := by
    have h_ae_snd : ∀ᵐ (t : ℝ) ∂(volume.restrict (Icc 0 1)), t ∈ Icc 0 1 := by
      rw [ae_restrict_iff' measurableSet_Icc]
      exact ae_of_all _ (fun _ h => h)
    have h_meas_bound : MeasurableSet {p : V × ℝ | ‖I₄_integrand p‖ ≤ g p} := by
      apply measurableSet_le
      · exact I₄_integrand_continuous.norm.measurable
      · exact (continuous_const.mul (Real.continuous_exp.comp
          (continuous_const.mul ((continuous_norm.comp continuous_fst).pow 2)))).measurable
    rw [Measure.ae_prod_iff_ae_ae h_meas_bound]
    apply ae_of_all
    intro x
    filter_upwards [h_ae_snd] with t ht
    exact hC x t ht
  exact Integrable.mono' h_g_int h_meas h_bound

end ClassA

/-! ## Class C: Unbounded tail (I₆)

For I₆, we integrate over t ∈ [1,∞) with z₆(t) = it.
Since Im(z) = t ≥ 1, Corollary 7.5 gives `|φ₀(z)| ≤ C₀·e^{-2πt}`.
Combined with Gaussian `e^{-π·r·t}`, we get `e^{-π(2+r)t}` which is integrable over [1,∞).

Key domination: For t ≥ 1, `e^{-π·r·t} ≤ e^{-π·r}`, so we can bound by
`C₀·e^{-π·r} · ∫_1^∞ e^{-2πt} dt` which is integrable on ℝ⁸.
-/

section ClassC

/-- The integrand for I₆ over V × [1,∞).
Using the simplified form from `I₆'_eq`: `I * φ₀''(it) * e^{-πrt}`. -/
def I₆_integrand (p : V × ℝ) : ℂ :=
  I * φ₀'' (I * p.2) * cexp (-π * ‖p.1‖^2 * p.2)

/-- For t > 0, Im(I*t) = t > 0. -/
lemma im_I_mul_pos' (t : ℝ) (ht : 0 < t) : 0 < (I * t).im := by simp [ht]

/-- The path t ↦ I*t is continuous. -/
lemma continuous_I_mul : Continuous (fun t : ℝ => I * t) :=
  continuous_const.mul continuous_ofReal

/-- ContinuousOn for φ₀'' ∘ (I*·) on positive reals.
This uses the homeomorphism between Ioi 0 and the positive subtype. -/
lemma continuousOn_φ₀''_I_mul_Ioi : ContinuousOn (fun t : ℝ => φ₀'' (I * t)) (Set.Ioi (0 : ℝ)) := by
  have h_im_pos : ∀ t : ℝ, 0 < t → 0 < (I * t).im := fun t ht => by simp [ht]
  -- The key is that the restriction to Ioi 0 factors through the subtype
  -- Step 1: Define the path on the subtype
  let path : {s : ℝ // 0 < s} → UpperHalfPlane := fun s => ⟨I * (s : ℝ), h_im_pos s s.2⟩
  -- Step 2: path is continuous
  have h_path_cont : Continuous path := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_const.mul (continuous_ofReal.comp continuous_subtype_val)
  -- Step 3: φ₀ ∘ path is continuous on the subtype
  have h_comp_cont : Continuous (φ₀ ∘ path) := φ₀_continuous.comp h_path_cont
  -- Step 4: For any s > 0, φ₀''(I*s) = φ₀(path ⟨s, hs⟩)
  have h_eq : ∀ s : ℝ, ∀ hs : 0 < s, φ₀'' (I * s) = φ₀ (path ⟨s, hs⟩) := fun s hs => by
    rw [φ₀''_eq _ (h_im_pos s hs)]
  -- Step 5: Use Set.restrictPreimage to get ContinuousOn
  -- The restriction of (φ₀ ∘ path) to the subtype gives ContinuousOn on Ioi 0
  -- via the homeomorphism Subtype.val : {s : ℝ // 0 < s} ≃ₜ Set.Ioi 0
  intro t ht
  rw [Set.mem_Ioi] at ht
  -- Show ContinuousWithinAt at t
  -- φ₀'' (I * s) = (φ₀ ∘ path) ⟨s, hs⟩ for s ∈ Ioi 0
  -- This is ContinuousWithinAt because φ₀ ∘ path is continuous
  have h_at : ContinuousAt (φ₀ ∘ path) ⟨t, ht⟩ := h_comp_cont.continuousAt
  -- Use map_nhds_subtype_val: map (↑) (𝓝 ⟨t, ht⟩) = 𝓝[{s | 0 < s}] t = 𝓝[Ioi 0] t
  have h_map_eq : Filter.map (Subtype.val : {s : ℝ // 0 < s} → ℝ) (nhds ⟨t, ht⟩) =
      nhdsWithin t (Set.Ioi 0) := by
    convert map_nhds_subtype_val ⟨t, ht⟩
  -- The composed function (φ₀ ∘ path) ∘ (fun s => ⟨s, _⟩) agrees with φ₀'' ∘ (I*·) on Ioi 0
  rw [ContinuousWithinAt, h_eq t ht]
  -- Goal: Tendsto (fun s => φ₀'' (I * s)) (nhdsWithin t (Ioi 0)) (nhds (φ₀ (path ⟨t, ht⟩)))
  -- Key insight: φ₀ ∘ path is the pullback of our function to the subtype
  -- ContinuousAt gives tendsto in nhds ⟨t, ht⟩, and map_nhds_subtype_val converts this
  -- Step 1: Use h_map_eq to convert nhdsWithin to Filter.map
  rw [← h_map_eq]
  -- Step 2: Use tendsto_map'_iff to convert to composition
  rw [Filter.tendsto_map'_iff]
  -- Step 3: The function (fun s : ℝ => φ₀'' (I * s)) ∘ Subtype.val
  --         = fun x => φ₀'' (I * x.val) = fun x => φ₀ (path x) by h_eq
  -- First simplify the composition to make the rewrite work
  change Filter.Tendsto (fun x : {s : ℝ // 0 < s} => φ₀'' (I * (x : ℝ)))
      (nhds ⟨t, ht⟩) (nhds (φ₀ (path ⟨t, ht⟩)))
  have h_fun_eq : (fun x : {s : ℝ // 0 < s} => φ₀'' (I * (x : ℝ))) = fun x => φ₀ (path x) := by
    funext x; exact h_eq x.val x.prop
  rw [h_fun_eq]
  exact h_at.tendsto

/-- Continuity of φ₀'' along the imaginary axis on [1, ∞): t ↦ φ₀''(I*t).
This is the domain used for I₆ in the blueprint (Lemma 7.10), which parametrizes
z = it for t ∈ [1,∞). We avoid the cusp limit at t = 0 by restricting to Ici 1. -/
lemma continuousOn_φ₀''_I₆_param :
    ContinuousOn (fun t : ℝ => φ₀'' (I * t)) (Set.Ici (1 : ℝ)) := by
  -- Derive from continuousOn_φ₀''_I_mul_Ioi by monotonicity: Ici 1 ⊆ Ioi 0
  refine continuousOn_φ₀''_I_mul_Ioi.mono ?_
  intro t ht
  -- ht : t ∈ Ici 1, so t ≥ 1 hence t > 0
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht

/-- For t ≥ 1, Im(I*t) = t ≥ 1 > 1/2, so norm_φ₀_le applies. -/
lemma norm_φ₀''_I₆_bound : ∃ C₀ > 0, ∀ t : ℝ, 1 ≤ t →
    ‖φ₀'' (I * t)‖ ≤ C₀ * Real.exp (-2 * π * t) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  refine ⟨C₀, hC₀_pos, fun t ht => ?_⟩
  -- For t ≥ 1, Im(I*t) = t ≥ 1 > 1/2
  have him : (I * t).im = t := by simp
  have him_pos : 0 < (I * t).im := by rw [him]; linarith
  have him_ge : 1/2 < (I * t).im := by rw [him]; linarith
  -- φ₀''(I*t) = φ₀(⟨I*t, ...⟩) since Im(I*t) > 0
  rw [φ₀''_eq _ him_pos]
  let z : UpperHalfPlane := ⟨I * t, him_pos⟩
  have hz_im : z.im = t := him
  calc ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im) := hC₀ z him_ge
    _ = C₀ * Real.exp (-2 * π * t) := by rw [hz_im]

/-- The I₆ integrand is continuous on V × [1, ∞).
This matches the blueprint's I₆ parametrization z = it for t ∈ [1,∞). -/
lemma continuousOn_I₆_integrand :
    ContinuousOn I₆_integrand (Set.univ ×ˢ Set.Ici (1 : ℝ)) := by
  unfold I₆_integrand
  -- φ₀''(I * p.2) is ContinuousOn on univ ×ˢ Ici 1 via continuousOn_φ₀''_I₆_param
  have h1 : ContinuousOn (fun p : V × ℝ => φ₀'' (I * p.2)) (Set.univ ×ˢ Set.Ici 1) := by
    apply ContinuousOn.comp continuousOn_φ₀''_I₆_param continuous_snd.continuousOn
    intro ⟨_, t⟩ ht
    exact ht.2
  -- The other factors are globally continuous
  have h_norm_sq : Continuous (fun p : V × ℝ => (‖p.1‖^2 : ℂ)) := by
    have h1 : Continuous (fun p : V × ℝ => ‖p.1‖^2) := (continuous_norm.comp continuous_fst).pow 2
    have h2 : Continuous (fun r : ℝ => (r : ℂ)) := continuous_ofReal
    have h3 : (fun p : V × ℝ => (‖p.1‖^2 : ℂ)) = (fun r : ℝ => (r : ℂ)) ∘ (fun p => ‖p.1‖^2) := by
      funext p; simp only [Function.comp_apply, ofReal_pow]
    rw [h3]; exact h2.comp h1
  have h2 : Continuous (fun p : V × ℝ => cexp (-π * ‖p.1‖^2 * p.2)) :=
    Complex.continuous_exp.comp ((continuous_const.mul h_norm_sq).mul
      (continuous_ofReal.comp continuous_snd))
  exact (continuous_const.continuousOn.mul h1).mul h2.continuousOn

/-- The norm of I₆_integrand is bounded by C * exp(-2πt) * exp(-π‖x‖²) for t ≥ 1. -/
lemma I₆_integrand_norm_bound : ∃ C > 0, ∀ x : V, ∀ t : ℝ, 1 ≤ t →
    ‖I₆_integrand (x, t)‖ ≤ C * Real.exp (-2 * π * t) * Real.exp (-π * ‖x‖^2) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀''_I₆_bound
  refine ⟨C₀, hC₀_pos, fun x t ht => ?_⟩
  unfold I₆_integrand
  rw [norm_mul, norm_mul]
  have h_I : ‖(I : ℂ)‖ = 1 := Complex.norm_I
  have h_φ : ‖φ₀'' (I * t)‖ ≤ C₀ * Real.exp (-2 * π * t) := hC₀ t ht
  have h_gauss_norm := norm_cexp_neg_pi_norm_sq_mul x t
  have h_gauss_le : Real.exp (-π * ‖x‖^2 * t) ≤ Real.exp (-π * ‖x‖^2) := by
    apply Real.exp_le_exp.mpr
    have h1 : -π * ‖x‖^2 * t ≤ -π * ‖x‖^2 * 1 := by
      have hpi : -π * ‖x‖^2 ≤ 0 := by nlinarith [Real.pi_pos, sq_nonneg ‖x‖]
      nlinarith
    linarith
  calc ‖(I : ℂ)‖ * ‖φ₀'' (I * t)‖ * ‖cexp (-π * ‖x‖^2 * t)‖
      = 1 * ‖φ₀'' (I * t)‖ * Real.exp (-π * ‖x‖^2 * t) := by rw [h_I, h_gauss_norm]
    _ ≤ 1 * (C₀ * Real.exp (-2 * π * t)) * Real.exp (-π * ‖x‖^2) := by gcongr
    _ = C₀ * Real.exp (-2 * π * t) * Real.exp (-π * ‖x‖^2) := by ring

/-- I₆ integrand is integrable on V × [1,∞) (Class C tail).
Strategy: φ₀ decay (Cor 7.5) + domination `e^{-πrt} ≤ e^{-πr}` for t ≥ 1. -/
theorem I₆_integrand_integrable :
    Integrable I₆_integrand (volume.prod (volume.restrict (Ici 1))) := by
  obtain ⟨C, hC_pos, hC⟩ := I₆_integrand_norm_bound
  -- Dominating function: C * exp(-2πt) * exp(-π‖x‖²) = (C * exp(-π‖x‖²)) * exp(-2πt)
  let g : V × ℝ → ℝ := fun p => C * Real.exp (-2 * π * p.2) * Real.exp (-π * ‖p.1‖^2)
  -- Use ContinuousOn.aestronglyMeasurable with the restricted measure
  have h_meas : AEStronglyMeasurable I₆_integrand (volume.prod (volume.restrict (Ici 1))) := by
    have hmeas' : AEStronglyMeasurable I₆_integrand
        ((volume.prod volume).restrict (Set.univ ×ˢ Set.Ici (1 : ℝ))) :=
      continuousOn_I₆_integrand.aestronglyMeasurable
        (MeasurableSet.univ.prod measurableSet_Ici)
    -- Rewrite the product measure to match: μ.prod (ν.restrict t) = (μ.prod ν).restrict (univ ×ˢ t)
    have h_eq : (volume : Measure V).prod ((volume : Measure ℝ).restrict (Set.Ici 1)) =
        ((volume : Measure V).prod (volume : Measure ℝ)).restrict (Set.univ ×ˢ Set.Ici 1) := by
      conv_lhs => rw [← Measure.restrict_univ (μ := (volume : Measure V))]
      rw [Measure.prod_restrict]
    rw [h_eq]
    exact hmeas'
  -- The dominating function is integrable (product of two integrable functions)
  have h_g_int : Integrable g (volume.prod (volume.restrict (Ici 1))) := by
    -- Rewrite as product: g(x,t) = (C * exp(-π‖x‖²)) * exp(-2πt)
    have h_eq : g = fun p : V × ℝ => (C * Real.exp (-π * ‖p.1‖^2)) * Real.exp (-2 * π * p.2) := by
      ext p; ring
    rw [h_eq]
    -- Use integrability of product of independent factors
    have h_x : Integrable (fun x : V => C * Real.exp (-π * ‖x‖^2)) volume :=
      (gaussian_integrable_R8 π Real.pi_pos).const_mul C
    have h_t : Integrable (fun t : ℝ => Real.exp (-2 * π * t)) (volume.restrict (Ici 1)) := by
      have h : -2 * π < 0 := by linarith [Real.pi_pos]
      exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_exp_mul_Ioi h 1)
    -- Product of integrable functions
    exact Integrable.mul_prod h_x h_t
  -- The bound holds a.e. (it actually holds everywhere on the support)
  have h_bound : ∀ᵐ p ∂(volume.prod (volume.restrict (Ici 1))), ‖I₆_integrand p‖ ≤ g p := by
    -- The bound holds for all (x, t) with t ≥ 1
    -- On the restricted measure, t ∈ Ici 1 a.e., so the bound holds a.e.
    -- Rewrite using the measure equality
    have h_eq : (volume : Measure V).prod ((volume : Measure ℝ).restrict (Set.Ici 1)) =
        ((volume : Measure V).prod (volume : Measure ℝ)).restrict (Set.univ ×ˢ Set.Ici 1) := by
      conv_lhs => rw [← Measure.restrict_univ (μ := (volume : Measure V))]
      rw [Measure.prod_restrict]
    rw [h_eq, ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Ici)]
    apply ae_of_all
    intro ⟨x, t⟩ ⟨_, ht⟩
    exact hC x t ht
  exact Integrable.mono' h_g_int h_meas h_bound

end ClassC

/-! ## Class B: Segments approaching real axis (I₁, I₃, I₅)

These segments have Im(z) = t → 0 as t → 0, so φ₀'' is unbounded near the endpoint.
We use `Ioc 0 1` to exclude the problematic endpoint, then apply the substitution s = 1/t.

Under this substitution:
- t → s = 1/t transforms [0,1] → [1,∞)
- φ₀''(-1/(it)) with t small becomes φ₀''(-1/(i/s)) = φ₀''(is) with s large
- The Jacobian dt = -ds/s² introduces the t^{-4} factor seen in the blueprint

This reduces Class B to integrals like `∫_1^∞ φ₀(is)·s^{-4}·e^{-πr/s} ds`
where Cor 7.5 applies since Im(is) = s ≥ 1 > 1/2.
-/

section ClassB

/-! ### Class B Helper Lemmas

For t ∈ (0, 1], the argument -1/(I*t) = I/t has Im = 1/t ≥ 1 > 1/2,
so the Cor 7.5 bound applies. The key fact is that exp(-2π/t) → 0
as t → 0⁺, making the integral converge despite the apparent singularity.
-/

/-- Key identity: -1/(I*t) = I/t for t ≠ 0 -/
lemma neg_one_div_I_mul (t : ℝ) (ht : t ≠ 0) : (-1 : ℂ) / (I * t) = I / t := by
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht
  have hIt : (I : ℂ) * t ≠ 0 := mul_ne_zero hI ht'
  field_simp [hIt, ht']
  ring_nf
  simp only [Complex.I_sq]

/-- For t ∈ (0, 1], the imaginary part of I/t is 1/t ≥ 1 -/
lemma im_I_div_pos (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1) : 1 / 2 < (I / (t : ℂ)).im := by
  simp only [div_ofReal_im, Complex.I_im, one_div]
  have h1t : 1 ≤ t⁻¹ := one_le_inv_iff₀.mpr ⟨ht, ht'⟩
  linarith

/-- The UpperHalfPlane point I/t for t ∈ (0, 1] -/
def uhp_I_div_t (t : ℝ) (ht : 0 < t) : UpperHalfPlane :=
  ⟨I / t, by simp only [div_ofReal_im, I_im, one_div]; positivity⟩

/-- Im(I/t) = 1/t for t > 0 -/
lemma uhp_I_div_t_im (t : ℝ) (ht : 0 < t) : (uhp_I_div_t t ht).im = t⁻¹ := by
  change (I / (t : ℂ)).im = t⁻¹
  simp only [div_ofReal_im, I_im, one_div]

/-- φ₀'' bound for Class B: for t ∈ (0, 1], ‖φ₀''(-1/(It))‖ ≤ C₀ * exp(-2π/t) -/
lemma norm_φ₀''_classB_bound : ∃ C₀ > 0, ∀ t : ℝ, 0 < t → t ≤ 1 →
    ‖φ₀'' (-1 / (I * t))‖ ≤ C₀ * Real.exp (-2 * π / t) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  refine ⟨C₀, hC₀_pos, fun t ht ht' => ?_⟩
  have ht_ne : t ≠ 0 := ne_of_gt ht
  rw [neg_one_div_I_mul t ht_ne]
  -- For t ∈ (0, 1], Im(I/t) = 1/t ≥ 1 > 1/2, so norm_φ₀_le applies
  have him : (I / (t : ℂ)).im = t⁻¹ := by simp only [div_ofReal_im, I_im, one_div]
  have him_pos : 0 < (I / (t : ℂ)).im := by rw [him]; positivity
  have h1t : 1 ≤ t⁻¹ := one_le_inv_iff₀.mpr ⟨ht, ht'⟩
  have him_gt : 1 / 2 < (I / (t : ℂ)).im := by rw [him]; linarith
  -- φ₀'' (I/t) = φ₀(⟨I/t, ...⟩) since Im(I/t) > 0
  rw [φ₀''_eq _ him_pos]
  -- Apply the φ₀ bound
  let z : UpperHalfPlane := ⟨I / t, him_pos⟩
  have hz_im : z.im = t⁻¹ := him
  have hz_gt : 1 / 2 < z.im := him_gt
  have h := hC₀ z hz_gt
  convert h using 2
  rw [hz_im, mul_comm, ← div_eq_mul_inv]

/-- For t ∈ (0, 1], exp(-2π/t) ≤ exp(-2π) since 1/t ≥ 1 implies -2π/t ≤ -2π. -/
lemma exp_neg_two_pi_div_le (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    Real.exp (-2 * π / t) ≤ Real.exp (-2 * π) := by
  apply Real.exp_le_exp.mpr
  have h1 : t ≤ 1 := ht.2
  have h2 : 0 < t := ht.1
  have h3 : 1 ≤ t⁻¹ := one_le_inv_iff₀.mpr ⟨h2, h1⟩
  calc -2 * π / t = -2 * π * t⁻¹ := by ring
    _ ≤ -2 * π * 1 := by nlinarith [Real.pi_pos]
    _ = -2 * π := by ring

/-- For t ∈ (0, 1], exp(-2π/t) * t^{-2} ≤ exp(-2π).
This uses the substitution u = 1/t: the function exp(-2πu) * u² is decreasing on [1, ∞). -/
lemma exp_neg_two_pi_div_mul_inv_sq_le (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    Real.exp (-2 * π / t) * t⁻¹^2 ≤ Real.exp (-2 * π) := by
  have h1 : t ≤ 1 := ht.2
  have h2 : 0 < t := ht.1
  have h3 : 1 ≤ t⁻¹ := one_le_inv_iff₀.mpr ⟨h2, h1⟩
  -- Substitute u = 1/t, so u ≥ 1
  set u := t⁻¹ with hu_def
  have h_u_pos : 0 < u := by positivity
  have h_u_ge_1 : 1 ≤ u := h3
  -- The function is exp(-2πu) * u²
  have h_eq : Real.exp (-2 * π / t) * t⁻¹^2 = Real.exp (-2 * π * u) * u^2 := by
    simp only [hu_def, div_eq_mul_inv]
  rw [h_eq]
  -- For u ≥ 1, we need exp(-2πu) * u² ≤ exp(-2π)
  -- Equivalently: u² ≤ exp(2π(u-1))
  -- This follows from 2*log(u) ≤ 2π(u-1), i.e., log(u) ≤ π(u-1)
  have h_ineq : u^2 ≤ Real.exp (2 * π * (u - 1)) := by
    by_cases hu1 : u = 1
    · simp [hu1]
    · have hu1' : 1 < u := lt_of_le_of_ne h_u_ge_1 (Ne.symm hu1)
      -- log(u) ≤ u - 1 for u > 0, and π(u-1) ≥ u - 1 when π ≥ 1
      have hlog : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos h_u_pos
      have h5 : u - 1 ≤ π * (u - 1) := by
        have hu_sub : 0 < u - 1 := by linarith
        have hpi : 1 ≤ π := le_of_lt (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) Real.two_le_pi)
        calc u - 1 = 1 * (u - 1) := by ring
          _ ≤ π * (u - 1) := mul_le_mul_of_nonneg_right hpi (le_of_lt hu_sub)
      have h6 : Real.log u ≤ π * (u - 1) := le_trans hlog h5
      have h7 : 2 * Real.log u ≤ 2 * π * (u - 1) := by linarith
      calc u^2 = Real.exp (Real.log (u^2)) := by rw [Real.exp_log]; positivity
        _ = Real.exp (2 * Real.log u) := by rw [Real.log_pow]; ring_nf
        _ ≤ Real.exp (2 * π * (u - 1)) := Real.exp_le_exp.mpr h7
  -- Now: exp(-2πu) * u² = exp(-2π) * exp(-2π(u-1)) * u² ≤ exp(-2π) * 1
  have h_split : Real.exp (-2 * π * u) = Real.exp (-2 * π) * Real.exp (-2 * π * (u - 1)) := by
    rw [← Real.exp_add]; ring_nf
  rw [h_split, mul_assoc]
  apply mul_le_of_le_one_right (Real.exp_pos _).le
  -- Need: exp(-2π(u-1)) * u² ≤ 1
  rw [mul_comm]
  have h_exp_pos : 0 < Real.exp (2 * π * (u - 1)) := Real.exp_pos _
  calc u^2 * Real.exp (-2 * π * (u - 1))
      = u^2 / Real.exp (2 * π * (u - 1)) := by
        rw [div_eq_mul_inv, ← Real.exp_neg]; ring_nf
    _ ≤ Real.exp (2 * π * (u - 1)) / Real.exp (2 * π * (u - 1)) :=
        div_le_div_of_nonneg_right h_ineq h_exp_pos.le
    _ = 1 := div_self (ne_of_gt h_exp_pos)

/-- exp(-2π/t) is integrable on (0, 1].
The function is bounded by exp(-2π) on this set, and the set has finite measure. -/
lemma exp_neg_inv_integrableOn :
    IntegrableOn (fun t => Real.exp (-2 * π / t)) (Ioc 0 1) volume := by
  -- Function is bounded by 1 on (0,1], and (0,1] has finite measure 1
  have h_bdd : ∀ t ∈ Ioc (0 : ℝ) 1, ‖Real.exp (-2 * π / t)‖ ≤ 1 := fun t ht => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-2 * π / t) ≤ Real.exp (-2 * π) := exp_neg_two_pi_div_le t ht
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      _ = 1 := Real.exp_zero
  -- Use integrableOn_of_bounded for bounded functions on finite measure sets
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by
    simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact measure_Ioc_lt_top⟩
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · -- Measurability: The function is continuous on (0,1] where t ≠ 0
    have h_contOn : ContinuousOn (fun t => Real.exp (-2 * π / t)) (Ioc 0 1) := by
      apply Real.continuous_exp.comp_continuousOn
      apply ContinuousOn.div continuousOn_const continuousOn_id
      intro t ht; exact ne_of_gt ht.1
    exact h_contOn.aestronglyMeasurable measurableSet_Ioc
  · -- Bound
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact ae_of_all _ fun t ht => h_bdd t ht

/-- The integrand for I₁ over V × (0,1].
Using the simplified form from `I₁'_eq_Ioc`. -/
def I₁_integrand (p : V × ℝ) : ℂ :=
  -I * φ₀'' (-1 / (I * p.2)) * p.2 ^ 2 *
  cexp (-π * I * ‖p.1‖^2) * cexp (-π * ‖p.1‖^2 * p.2)

/-- The integrand for I₃ over V × (0,1].
Using the simplified form from `I₃'_eq_Ioc`. -/
def I₃_integrand (p : V × ℝ) : ℂ :=
  -I * φ₀'' (-1 / (I * p.2)) * p.2 ^ 2 *
  cexp (π * I * ‖p.1‖^2) * cexp (-π * ‖p.1‖^2 * p.2)

/-- The integrand for I₅ over V × (0,1].
Using the simplified form from `I₅'_eq_Ioc`. -/
def I₅_integrand (p : V × ℝ) : ℂ :=
  -I * φ₀'' (-1 / (I * p.2)) * p.2 ^ 2 * cexp (-π * ‖p.1‖^2 * p.2)

/-- I₁ integrand equals I₅ integrand times a unit-modulus phase factor. -/
lemma I₁_integrand_eq_I₅_mul_phase (p : V × ℝ) :
    I₁_integrand p = I₅_integrand p * cexp (-π * I * ‖p.1‖^2) := by
  simp only [I₁_integrand, I₅_integrand]
  ring

/-- I₃ integrand equals I₅ integrand times a unit-modulus phase factor. -/
lemma I₃_integrand_eq_I₅_mul_phase (p : V × ℝ) :
    I₃_integrand p = I₅_integrand p * cexp (π * I * ‖p.1‖^2) := by
  simp only [I₃_integrand, I₅_integrand]
  ring

/-- The phase factor cexp(-πI‖x‖²) has unit modulus. -/
lemma norm_phase_factor_I₁ (x : V) : ‖cexp (-π * I * ‖x‖^2)‖ = 1 := by
  rw [show (-π * I * ‖x‖^2 : ℂ) = ↑(-π * ‖x‖^2) * I from by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The phase factor cexp(πI‖x‖²) has unit modulus. -/
lemma norm_phase_factor_I₃ (x : V) : ‖cexp (π * I * ‖x‖^2)‖ = 1 := by
  rw [show (π * I * ‖x‖^2 : ℂ) = ↑(π * ‖x‖^2) * I from by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- ContinuousOn for the I₅ path: t ↦ φ₀''(-1/(I*t)) is continuous on (0, ∞).
Since -1/(I*t) = I/t and Im(I/t) = 1/t > 0 for t > 0, this factors through φ₀_continuous. -/
lemma continuousOn_φ₀''_classB_path :
    ContinuousOn (fun t : ℝ => φ₀'' (-1 / (I * t))) (Set.Ioi 0) := by
  have h_im_pos : ∀ t : ℝ, 0 < t → 0 < ((-1 : ℂ) / (I * t)).im := fun t ht => by
    rw [neg_one_div_I_mul t (ne_of_gt ht)]
    simp only [div_ofReal_im, I_im, one_div]; positivity
  -- The path t ↦ ⟨-1/(I*t), _⟩ factorizes through UpperHalfPlane
  let path : {s : ℝ // 0 < s} → UpperHalfPlane := fun s => ⟨-1 / (I * s), h_im_pos s s.2⟩
  have h_path_cont : Continuous path := by
    refine Continuous.subtype_mk ?_ _
    apply Continuous.div continuous_const
    · exact continuous_const.mul (continuous_ofReal.comp continuous_subtype_val)
    · intro ⟨s, hs⟩
      simp only [ne_eq, mul_eq_zero, I_ne_zero, ofReal_eq_zero, false_or]
      exact ne_of_gt hs
  have h_comp_cont : Continuous (φ₀ ∘ path) := φ₀_continuous.comp h_path_cont
  -- Transfer to ContinuousOn via the homeomorphism
  intro t ht
  rw [Set.mem_Ioi] at ht
  have h_eq : φ₀'' (-1 / (I * t)) = φ₀ (path ⟨t, ht⟩) := by
    rw [φ₀''_eq _ (h_im_pos t ht)]
  rw [ContinuousWithinAt, h_eq]
  have h_at : ContinuousAt (φ₀ ∘ path) ⟨t, ht⟩ := h_comp_cont.continuousAt
  have h_map_eq : Filter.map (Subtype.val : {s : ℝ // 0 < s} → ℝ) (nhds ⟨t, ht⟩) =
      nhdsWithin t (Set.Ioi 0) := by convert map_nhds_subtype_val ⟨t, ht⟩
  rw [← h_map_eq, Filter.tendsto_map'_iff]
  convert h_at.tendsto using 1
  funext x
  simp only [Function.comp_apply, φ₀''_eq _ (h_im_pos x.val x.prop), path]

/-- The I₅ integrand is continuous on V × (0, 1]. -/
lemma continuousOn_I₅_integrand : ContinuousOn I₅_integrand (Set.univ ×ˢ Set.Ioc 0 1) := by
  unfold I₅_integrand
  refine ContinuousOn.mul ?_ ?_
  · refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.mul ?_ ?_
      · exact continuousOn_const
      · -- φ₀''(-1/(I*t)) is continuous in t
        apply ContinuousOn.comp continuousOn_φ₀''_classB_path
        · exact continuous_snd.continuousOn
        · intro ⟨_, t⟩ ht
          simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioc, true_and] at ht
          exact ht.1
    · -- t² is continuous
      have h : Continuous (fun p : V × ℝ => (p.2 : ℂ) ^ 2) := by
        exact (continuous_pow 2).comp (continuous_ofReal.comp continuous_snd)
      exact h.continuousOn
  · -- cexp(-π‖x‖²*t) is continuous
    have h : Continuous (fun p : V × ℝ => cexp (-π * ‖p.1‖^2 * p.2)) := by
      apply Complex.continuous_exp.comp
      apply Continuous.mul
      · apply Continuous.mul continuous_const
        have h1 : Continuous (fun p : V × ℝ => (‖p.1‖ ^ 2 : ℂ)) :=
          (continuous_pow 2).comp (continuous_ofReal.comp (continuous_norm.comp continuous_fst))
        exact h1
      · exact continuous_ofReal.comp continuous_snd
    exact h.continuousOn

/-- I₅ integrand norm bound for Class B. -/
lemma I₅_integrand_norm_bound : ∃ C > 0, ∀ x : V, ∀ t : ℝ, 0 < t → t ≤ 1 →
    ‖I₅_integrand (x, t)‖ ≤ C * Real.exp (-2 * π / t) * t ^ 2 * Real.exp (-π * ‖x‖^2 * t) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀''_classB_bound
  refine ⟨C₀, hC₀_pos, fun x t ht ht' => ?_⟩
  unfold I₅_integrand
  rw [norm_mul, norm_mul, norm_mul]
  have h_I : ‖(-I : ℂ)‖ = 1 := by rw [norm_neg, Complex.norm_I]
  have h_φ := hC₀ t ht ht'
  -- Gaussian factor
  have h_gauss : ‖cexp ((-π : ℂ) * ‖x‖^2 * t)‖ = Real.exp (-π * ‖x‖^2 * t) := by
    rw [Complex.norm_exp]
    congr 1
    have h1 : (‖x‖^2 : ℂ).re = ‖x‖^2 := by simp [sq]
    have h2 : (‖x‖^2 : ℂ).im = 0 := by simp [sq]
    simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, h1, h2]
  -- t² factor
  have h_t2 : ‖(t : ℂ) ^ 2‖ = t ^ 2 := by
    simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  rw [h_I, h_t2, h_gauss, one_mul]
  calc ‖φ₀'' (-1 / (I * t))‖ * t ^ 2 * Real.exp (-π * ‖x‖^2 * t)
      ≤ (C₀ * Real.exp (-2 * π / t)) * t ^ 2 * Real.exp (-π * ‖x‖^2 * t) := by gcongr
    _ = C₀ * Real.exp (-2 * π / t) * t ^ 2 * Real.exp (-π * ‖x‖^2 * t) := by ring

/-- I₅ integrand is integrable on V × (0,1] (Class B segment).

Route A strategy:
1. Bound: ‖I₅_integrand(x,t)‖ ≤ C * exp(-2π/t) * t² * exp(-π‖x‖²t)
2. Integrate in x first: ∫_V exp(-πt‖x‖²) dx = t^{-4} (Gaussian in 8D)
3. Then t-integral: ∫₀¹ C * exp(-2π/t) * t^{-2} dt converges

The super-exponential decay of exp(-2π/t) as t→0 dominates the polynomial t^{-2}. -/
theorem I₅_integrand_integrable :
    Integrable I₅_integrand (volume.prod (volume.restrict (Ioc 0 1))) := by
  -- Get the pointwise bound constant C from I₅_integrand_norm_bound
  obtain ⟨C, hC_pos, hC_bound⟩ := I₅_integrand_norm_bound
  -- AEStronglyMeasurable is needed for integrable_prod_iff'
  have h_meas : AEStronglyMeasurable I₅_integrand
      (volume.prod (volume.restrict (Ioc 0 1))) := by
    -- Use ContinuousOn.aestronglyMeasurable with the restricted measure
    have hmeas' : AEStronglyMeasurable I₅_integrand
        ((volume.prod volume).restrict (Set.univ ×ˢ Set.Ioc (0 : ℝ) 1)) :=
      continuousOn_I₅_integrand.aestronglyMeasurable
        (MeasurableSet.univ.prod measurableSet_Ioc)
    -- Rewrite the product measure: μ.prod (ν.restrict t) = (μ.prod ν).restrict (univ ×ˢ t)
    have h_eq : (volume : Measure V).prod ((volume : Measure ℝ).restrict (Set.Ioc 0 1)) =
        ((volume : Measure V).prod (volume : Measure ℝ)).restrict (Set.univ ×ˢ Set.Ioc 0 1) := by
      conv_lhs => rw [← Measure.restrict_univ (μ := (volume : Measure V))]
      rw [Measure.prod_restrict]
    rw [h_eq]
    exact hmeas'
  -- Use integrable_prod_iff' to swap order of integration
  rw [MeasureTheory.integrable_prod_iff' h_meas]
  constructor
  -- Goal 1: For a.e. t ∈ (0,1], the x-slice is integrable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine ae_of_all _ fun t ht => ?_
    -- Bound by C·exp(-2π/t)·t² · Gaussian, which is integrable
    have h_gauss := gaussian_integrable_scaled π t Real.pi_pos ht.1
    apply Integrable.mono' (h_gauss.const_mul (C * Real.exp (-2 * π / t) * t^2))
    · -- Measurability of I₅_integrand in x for fixed t
      -- For fixed t ∈ (0, 1], the slice x ↦ I₅_integrand(x, t) is continuous
      -- I₅_integrand (x, t) = -I * φ₀''(-1/(It)) * t² * cexp(-π‖x‖²t) = const * cexp(...)
      have h_cont : Continuous (fun x : V => I₅_integrand (x, t)) := by
        simp only [I₅_integrand]
        apply Continuous.mul
        · exact continuous_const  -- -I * φ₀''(-1/(It)) * t² is constant
        · apply Complex.continuous_exp.comp
          -- The argument is -π * ‖x‖² * t
          refine Continuous.mul ?_ continuous_const
          refine Continuous.mul continuous_const ?_
          exact (continuous_pow 2).comp (continuous_ofReal.comp continuous_norm)
      exact h_cont.aestronglyMeasurable
    · -- Norm bound
      refine ae_of_all _ fun x => ?_
      have h := hC_bound x t ht.1 ht.2
      calc ‖I₅_integrand (x, t)‖
          ≤ C * Real.exp (-2 * π / t) * t ^ 2 * Real.exp (-π * ‖x‖^2 * t) := h
        _ = C * Real.exp (-2 * π / t) * t ^ 2 * Real.exp (-π * t * ‖x‖^2) := by ring_nf
  -- Goal 2: The t-integral of x-integrals converges
  · -- ∫_V ‖I₅(x,t)‖ dx ≤ C·exp(-2π/t)·t^{-2} ≤ C·exp(-2π) for t ∈ (0,1]
    apply Integrable.mono' (integrable_const (C * Real.exp (-2 * π)))
    · -- Measurability of integral of norms
      -- The function t ↦ ∫ x, ‖I₅_integrand (x, t)‖ is AEStronglyMeasurable
      -- We need to integrate over the first variable V, so use the swapped version
      -- First swap the product: (t, x) ↦ ‖I₅_integrand (x, t)‖
      have h_swap : AEStronglyMeasurable (fun p : ℝ × V => ‖I₅_integrand (p.2, p.1)‖)
          ((volume.restrict (Ioc 0 1)).prod (volume : Measure V)) := by
        -- Use that map swap (ν.prod μ) = μ.prod ν
        -- So map swap ((volume.restrict ...).prod volume) = volume.prod (volume.restrict ...)
        have h_map_eq : Measure.map Prod.swap
            (((volume : Measure ℝ).restrict (Ioc 0 1)).prod (volume : Measure V)) =
            (volume : Measure V).prod ((volume : Measure ℝ).restrict (Ioc 0 1)) :=
          Measure.prod_swap
        -- h_meas.norm is AEStronglyMeasurable on volume.prod (volume.restrict ...)
        -- = map swap ((volume.restrict ...).prod volume)
        have h_on_map : AEStronglyMeasurable (fun x => ‖I₅_integrand x‖)
            (Measure.map Prod.swap
              (((volume : Measure ℝ).restrict (Ioc 0 1)).prod (volume : Measure V))) := by
          rw [h_map_eq]; exact h_meas.norm
        -- Apply comp_measurable to get the swapped function
        exact h_on_map.comp_measurable measurable_swap
      -- Now integral_prod_right' integrates over V (now second variable)
      exact h_swap.integral_prod_right'
    · -- Bound on integral
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine ae_of_all _ fun t ht => ?_
      have h_gauss := gaussian_integrable_scaled π t Real.pi_pos ht.1
      have h_int : Integrable (fun x => ‖I₅_integrand (x, t)‖) (volume : Measure V) := by
        apply Integrable.mono' (h_gauss.const_mul (C * Real.exp (-2 * π / t) * t^2))
        · -- For fixed t, x ↦ ‖I₅_integrand(x, t)‖ is continuous (norm of continuous function)
          have h_cont : Continuous (fun x : V => I₅_integrand (x, t)) := by
            simp only [I₅_integrand]
            apply Continuous.mul
            · exact continuous_const
            · apply Complex.continuous_exp.comp
              refine Continuous.mul ?_ continuous_const
              refine Continuous.mul continuous_const ?_
              exact (continuous_pow 2).comp (continuous_ofReal.comp continuous_norm)
          exact (continuous_norm.comp h_cont).aestronglyMeasurable
        · refine ae_of_all _ fun x => ?_
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          have h := hC_bound x t ht.1 ht.2
          calc ‖I₅_integrand (x, t)‖
              ≤ C * Real.exp (-2 * π / t) * t ^ 2 * Real.exp (-π * ‖x‖^2 * t) := h
            _ = C * Real.exp (-2 * π / t) * t ^ 2 * Real.exp (-π * t * ‖x‖^2) := by ring_nf
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      -- Use Gaussian integral formula: ∫_V exp(-πt‖x‖²) = (π/(πt))^4 = t^{-4}
      have h_gauss_val : ∫ x : V, Real.exp (-π * t * ‖x‖^2) = t⁻¹ ^ 4 := by
        have h_pos : 0 < π * t := mul_pos Real.pi_pos ht.1
        have h := @GaussianFourier.integral_rexp_neg_mul_sq_norm V _ _ _ _ _ (π * t) h_pos
        have h_finrank : Module.finrank ℝ V = 8 := finrank_euclideanSpace_fin
        simp only [h_finrank, Nat.cast_ofNat] at h
        convert h using 2
        · ring_nf
        · -- Need: t⁻¹ ^ 4 = (π / (π * t)) ^ (8 / 2)
          -- Note: 8 / 2 = 4 in ℕ, and π / (π * t) = 1/t = t⁻¹
          have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
          have ht_ne : (t : ℝ) ≠ 0 := ne_of_gt ht.1
          -- Simplify π / (π * t) = t⁻¹
          have h_simp : π / (π * t) = t⁻¹ := by field_simp
          -- The exponent (8 : ℕ) / 2 = 4
          norm_num [h_simp]
      calc ∫ x : V, ‖I₅_integrand (x, t)‖
          ≤ ∫ x : V, C * Real.exp (-2 * π / t) * t ^ 2 * Real.exp (-π * t * ‖x‖^2) := by
            apply integral_mono h_int (h_gauss.const_mul _)
            intro x; have h := hC_bound x t ht.1 ht.2
            calc ‖I₅_integrand (x, t)‖ ≤ C * Real.exp (-2 * π / t) * t ^ 2 *
                Real.exp (-π * ‖x‖^2 * t) := h
              _ = C * Real.exp (-2 * π / t) * t ^ 2 * Real.exp (-π * t * ‖x‖^2) := by ring_nf
        _ = C * Real.exp (-2 * π / t) * t ^ 2 * ∫ x : V, Real.exp (-π * t * ‖x‖^2) := by
            rw [← MeasureTheory.integral_const_mul]
        _ = C * Real.exp (-2 * π / t) * t ^ 2 * t⁻¹ ^ 4 := by rw [h_gauss_val]
        _ = C * Real.exp (-2 * π / t) * t⁻¹ ^ 2 := by field_simp
        _ = C * (Real.exp (-2 * π / t) * t⁻¹ ^ 2) := by ring
        _ ≤ C * Real.exp (-2 * π) := mul_le_mul_of_nonneg_left
            (exp_neg_two_pi_div_mul_inv_sq_le t ht) (le_of_lt hC_pos)

/-- I₁ integrand is integrable on V × (0,1] (Class B segment).
Follows from I₅ integrability since I₁ = I₅ * (unit-modulus phase). -/
theorem I₁_integrand_integrable :
    Integrable I₁_integrand (volume.prod (volume.restrict (Ioc 0 1))) := by
  have h_eq : I₁_integrand = fun p => I₅_integrand p * cexp (-π * I * ‖p.1‖^2) := by
    ext p; exact I₁_integrand_eq_I₅_mul_phase p
  rw [h_eq]
  -- I₅ is integrable, and we multiply by a unit-modulus factor
  have h_I₅ := I₅_integrand_integrable
  -- ‖f*g‖ = ‖f‖*‖g‖ = ‖f‖*1 = ‖f‖
  apply Integrable.mono' h_I₅.norm
  · -- Measurability
    have h_cont : Continuous (fun p : V × ℝ => cexp (-π * I * ‖p.1‖^2)) := by fun_prop
    exact h_I₅.aestronglyMeasurable.mul h_cont.aestronglyMeasurable
  · -- Norm bound
    apply ae_of_all
    intro p
    rw [norm_mul, norm_phase_factor_I₁ p.1, mul_one]

/-- I₃ integrand is integrable on V × (0,1] (Class B segment).
Follows from I₅ integrability since I₃ = I₅ * (unit-modulus phase). -/
theorem I₃_integrand_integrable :
    Integrable I₃_integrand (volume.prod (volume.restrict (Ioc 0 1))) := by
  have h_eq : I₃_integrand = fun p => I₅_integrand p * cexp (π * I * ‖p.1‖^2) := by
    ext p; exact I₃_integrand_eq_I₅_mul_phase p
  rw [h_eq]
  have h_I₅ := I₅_integrand_integrable
  apply Integrable.mono' h_I₅.norm
  · have h_cont : Continuous (fun p : V × ℝ => cexp (π * I * ‖p.1‖^2)) := by fun_prop
    exact h_I₅.aestronglyMeasurable.mul h_cont.aestronglyMeasurable
  · apply ae_of_all
    intro p
    rw [norm_mul, norm_phase_factor_I₃ p.1, mul_one]

end ClassB

/-! ## Level 3: Fubini Swap Lemmas

Once we have product integrability, Fubini's theorem allows swapping
the order of integration: ∫_{ℝ⁸} ∫_{contour} = ∫_{contour} ∫_{ℝ⁸}.

The connection between `Iⱼ x` and `∫ t, Iⱼ_integrand (x, t)` follows from
the `Iⱼ'_eq_Ioc` lemmas in Basic.lean. Note that some have prefactors:
- I₁, I₃: factor 1 (direct integral)
- I₅: factor -2
- I₆: factor 2
-/

section FubiniSwap

/-- Connection: I₁ x = ∫ t, I₁_integrand (x, t) -/
lemma I₁_eq_integral (x : V) :
    I₁ x = ∫ t in Ioc (0 : ℝ) 1, I₁_integrand (x, t) := by
  -- I₁ x = I₁' (‖x‖²) by definition
  -- I₁'_eq_Ioc gives the integral form with r = ‖x‖²
  rw [I₁, I₁'_eq_Ioc]
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Ioc
  refine ae_of_all _ fun t _ => ?_
  simp only [I₁_integrand, ofReal_pow]

/-- Connection: I₂ x = ∫ t, I₂_integrand (x, t) over [0,1].
Note: Uses Icc because the integrand is continuous (no singularity at 0). -/
lemma I₂_eq_integral (x : V) :
    I₂ x = ∫ t in Icc (0 : ℝ) 1, I₂_integrand (x, t) := by
  rw [I₂, I₂'_eq]
  -- Convert interval integral to Ioc, then Ioc to Icc (NoAtoms)
  rw [intervalIntegral_eq_integral_uIoc, if_pos (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), one_smul]
  rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Icc
  refine ae_of_all _ fun t _ => ?_
  simp only [I₂_integrand, ofReal_pow]

/-- Connection: I₃ x = ∫ t, I₃_integrand (x, t) -/
lemma I₃_eq_integral (x : V) :
    I₃ x = ∫ t in Ioc (0 : ℝ) 1, I₃_integrand (x, t) := by
  rw [I₃, I₃'_eq_Ioc]
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Ioc
  refine ae_of_all _ fun t _ => ?_
  simp only [I₃_integrand, ofReal_pow]

/-- Connection: I₄ x = ∫ t, I₄_integrand (x, t) over [0,1].
Note: Uses Icc because the integrand is continuous (no singularity at 0). -/
lemma I₄_eq_integral (x : V) :
    I₄ x = ∫ t in Icc (0 : ℝ) 1, I₄_integrand (x, t) := by
  rw [I₄, I₄'_eq]
  rw [intervalIntegral_eq_integral_uIoc, if_pos (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), one_smul]
  rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Icc
  refine ae_of_all _ fun t _ => ?_
  simp only [I₄_integrand, ofReal_pow]

/-- Connection: I₅ x = -2 * ∫ t, I₅_integrand (x, t) -/
lemma I₅_eq_integral (x : V) :
    I₅ x = -2 * ∫ t in Ioc (0 : ℝ) 1, I₅_integrand (x, t) := by
  rw [I₅, I₅'_eq_Ioc]
  congr 1
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Ioc
  refine ae_of_all _ fun t _ => ?_
  simp only [I₅_integrand, ofReal_pow]

/-- Connection: I₆ x = 2 * ∫ t, I₆_integrand (x, t) -/
lemma I₆_eq_integral (x : V) :
    I₆ x = 2 * ∫ t in Ici (1 : ℝ), I₆_integrand (x, t) := by
  rw [I₆, I₆'_eq]
  congr 1
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Ici
  refine ae_of_all _ fun t _ => ?_
  simp only [I₆_integrand, ofReal_pow]

/-- Fubini for I₁: swap ∫_{ℝ⁸} and ∫_{(0,1]} -/
theorem I₁_integral_swap :
    ∫ x : V, I₁ x = ∫ t in Ioc (0 : ℝ) 1, ∫ x : V, I₁_integrand (x, t) := by
  simp_rw [I₁_eq_integral]
  exact MeasureTheory.integral_integral_swap I₁_integrand_integrable

/-- Fubini for I₂: swap ∫_{ℝ⁸} and ∫_{[0,1]} -/
theorem I₂_integral_swap :
    ∫ x : V, I₂ x = ∫ t in Icc (0 : ℝ) 1, ∫ x : V, I₂_integrand (x, t) := by
  simp_rw [I₂_eq_integral]
  exact MeasureTheory.integral_integral_swap I₂_integrand_integrable

/-- Fubini for I₃: swap ∫_{ℝ⁸} and ∫_{(0,1]} -/
theorem I₃_integral_swap :
    ∫ x : V, I₃ x = ∫ t in Ioc (0 : ℝ) 1, ∫ x : V, I₃_integrand (x, t) := by
  simp_rw [I₃_eq_integral]
  exact MeasureTheory.integral_integral_swap I₃_integrand_integrable

/-- Fubini for I₄: swap ∫_{ℝ⁸} and ∫_{[0,1]} -/
theorem I₄_integral_swap :
    ∫ x : V, I₄ x = ∫ t in Icc (0 : ℝ) 1, ∫ x : V, I₄_integrand (x, t) := by
  simp_rw [I₄_eq_integral]
  exact MeasureTheory.integral_integral_swap I₄_integrand_integrable

/-- Fubini for I₅: swap ∫_{ℝ⁸} and ∫_{(0,1]}
Note: includes factor of -2 from I₅ definition. -/
theorem I₅_integral_swap :
    ∫ x : V, I₅ x = -2 * ∫ t in Ioc (0 : ℝ) 1, ∫ x : V, I₅_integrand (x, t) := by
  simp_rw [I₅_eq_integral]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact MeasureTheory.integral_integral_swap I₅_integrand_integrable

/-- Fubini for I₆: swap ∫_{ℝ⁸} and ∫_{[1,∞)}
Note: includes factor of 2 from I₆ definition. -/
theorem I₆_integral_swap :
    ∫ x : V, I₆ x = 2 * ∫ t in Ici (1 : ℝ), ∫ x : V, I₆_integrand (x, t) := by
  simp_rw [I₆_eq_integral]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact MeasureTheory.integral_integral_swap I₆_integrand_integrable

end FubiniSwap

/-! ## Level 1: Basic Integrability

Each Iⱼ is integrable over ℝ⁸. These follow from the product integrability results
via Tonelli's theorem (integrating out the t parameter).

Note: These may alternatively follow from `a : 𝓢(V, ℂ)` being Schwartz (in Schwartz.lean),
since Schwartz functions are integrable. The proofs here provide a more direct path.
-/

section BasicIntegrability

/-- I₁ is integrable over ℝ⁸ (from Schwartz structure). -/
theorem I₁_integrable : Integrable (I₁ : V → ℂ) :=
  MagicFunction.a.SchwartzIntegrals.I₁.integrable

/-- I₂ is integrable over ℝ⁸ (from Schwartz structure). -/
theorem I₂_integrable : Integrable (I₂ : V → ℂ) :=
  MagicFunction.a.SchwartzIntegrals.I₂.integrable

/-- I₃ is integrable over ℝ⁸ (from Schwartz structure). -/
theorem I₃_integrable : Integrable (I₃ : V → ℂ) :=
  MagicFunction.a.SchwartzIntegrals.I₃.integrable

/-- I₄ is integrable over ℝ⁸ (from Schwartz structure). -/
theorem I₄_integrable : Integrable (I₄ : V → ℂ) :=
  MagicFunction.a.SchwartzIntegrals.I₄.integrable

/-- I₅ is integrable over ℝ⁸ (from Schwartz structure). -/
theorem I₅_integrable : Integrable (I₅ : V → ℂ) :=
  MagicFunction.a.SchwartzIntegrals.I₅.integrable

/-- I₆ is integrable over ℝ⁸ (from Schwartz structure). -/
theorem I₆_integrable : Integrable (I₆ : V → ℂ) :=
  MagicFunction.a.SchwartzIntegrals.I₆.integrable

/-- The magic function `a` is integrable over ℝ⁸. -/
theorem a_integrable : Integrable (a : V → ℂ) := by
  have h : a = I₁ + I₂ + I₃ + I₄ + I₅ + I₆ := by
    ext x
    simp only [Pi.add_apply]
    exact a_eq x
  rw [h]
  exact ((((I₁_integrable.add I₂_integrable).add I₃_integrable).add I₄_integrable).add
    I₅_integrable).add I₆_integrable

end BasicIntegrability

end

