/-
Copyright (c) 2025 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/

import SpherePacking.MagicFunction.a.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

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

open MeasureTheory Complex Real Set

local notation "V" => EuclideanSpace ℝ (Fin 8)

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions

noncomputable section

/-! ## Workhorse Lemmas

These lemmas are used across multiple integrability proofs.
-/

/-- The norm of `cexp (π * I * r * z)` equals `exp(-π * r * Im(z))` for r ≥ 0.
This is the key decay factor in all our integrands. -/
lemma norm_cexp_pi_I_mul_eq (r : ℝ) (z : ℂ) (_hr : 0 ≤ r) :
    ‖cexp (π * I * r * z)‖ = Real.exp (-π * r * z.im) := by
  rw [Complex.norm_exp]
  congr 1
  -- Goal: (π * I * r * z).re = -(π * r * z.im)
  have h1 : ((π : ℂ) * I * r).im = π * r := by
    simp only [mul_im, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, zero_add, add_zero]
  simp only [mul_re, h1, ofReal_im, mul_zero, sub_zero]
  ring

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

/-- For t ≥ 1, we have `e^{-c·t·r} ≤ e^{-c·r}` when c, r ≥ 0.
Key domination for Class C (I₆) integrability. -/
lemma exp_neg_mul_le_of_one_le (c r t : ℝ) (hc : 0 ≤ c) (hr : 0 ≤ r) (ht : 1 ≤ t) :
    Real.exp (-c * t * r) ≤ Real.exp (-c * r) := by
  apply Real.exp_le_exp.mpr
  have h1 : c * r ≤ c * t * r := by
    have : 1 * (c * r) ≤ t * (c * r) := by
      apply mul_le_mul_of_nonneg_right ht (mul_nonneg hc hr)
    linarith
  linarith

/-- For t^{-1} decay bounds: `∫_1^∞ t^{-4} e^{-c·t} dt` converges for c > 0.
Used in the s = 1/t substitution for Class B segments.
Strategy: On [1,∞), t^{-4} ≤ 1, so dominated by exp(-c*t) which is integrable. -/
lemma integral_inv_pow_four_exp_converges (c : ℝ) (hc : 0 < c) :
    Integrable (fun t : ℝ => t^(-(4:ℝ)) * Real.exp (-c * t)) (volume.restrict (Ici 1)) := by
  sorry

/-! ## Class A: Safe segments (I₂, I₄)

For these segments, Im(z) = 1 throughout, so φ₀'' is bounded on the compact parameter
range [0,1], and the Gaussian factor `e^{-π·r·Im(z)} = e^{-π·r}` provides integrability.
-/

section ClassA

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

/-- I₂ integrand is integrable on V × [0,1] (Class A segment).
Strategy: φ₀'' bounded on compact, Gaussian decay `e^{-π‖x‖²}` dominates. -/
theorem I₂_integrand_integrable :
    Integrable I₂_integrand (volume.prod (volume.restrict (Icc 0 1))) := by
  sorry

/-- I₄ integrand is integrable on V × [0,1] (Class A segment).
Strategy: Same as I₂ - φ₀'' bounded on compact, Gaussian decay dominates. -/
theorem I₄_integrand_integrable :
    Integrable I₄_integrand (volume.prod (volume.restrict (Icc 0 1))) := by
  sorry

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

/-- I₆ integrand is integrable on V × [1,∞) (Class C tail).
Strategy: φ₀ decay (Cor 7.5) + domination `e^{-πrt} ≤ e^{-πr}` for t ≥ 1. -/
theorem I₆_integrand_integrable :
    Integrable I₆_integrand (volume.prod (volume.restrict (Ici 1))) := by
  sorry

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

/-- I₁ integrand is integrable on V × (0,1] (Class B segment).
Strategy: Substitute s = 1/t, use Cor 7.5 for φ₀ decay at large s. -/
theorem I₁_integrand_integrable :
    Integrable I₁_integrand (volume.prod (volume.restrict (Ioc 0 1))) := by
  sorry

/-- I₃ integrand is integrable on V × (0,1] (Class B segment).
Strategy: Same as I₁ - substitute s = 1/t, use Cor 7.5. -/
theorem I₃_integrand_integrable :
    Integrable I₃_integrand (volume.prod (volume.restrict (Ioc 0 1))) := by
  sorry

/-- I₅ integrand is integrable on V × (0,1] (Class B segment).
Strategy: Same as I₁, I₃ - substitute s = 1/t, use Cor 7.5. -/
theorem I₅_integrand_integrable :
    Integrable I₅_integrand (volume.prod (volume.restrict (Ioc 0 1))) := by
  sorry

end ClassB

/-! ## Level 3: Fubini Swap Lemmas

Once we have product integrability, Fubini's theorem allows swapping
the order of integration: ∫_{ℝ⁸} ∫_{contour} = ∫_{contour} ∫_{ℝ⁸}.
-/

section FubiniSwap

/-- Fubini for I₁: swap ∫_{ℝ⁸} and ∫_{(0,1]} -/
theorem I₁_integral_swap :
    ∫ x : V, I₁ x = ∫ t in Ioc (0 : ℝ) 1, ∫ x : V, I₁_integrand (x, t) := by
  sorry

/-- Fubini for I₂: swap ∫_{ℝ⁸} and ∫_{[0,1]} -/
theorem I₂_integral_swap :
    ∫ x : V, I₂ x = ∫ t in Icc (0 : ℝ) 1, ∫ x : V, I₂_integrand (x, t) := by
  sorry

/-- Fubini for I₃: swap ∫_{ℝ⁸} and ∫_{(0,1]} -/
theorem I₃_integral_swap :
    ∫ x : V, I₃ x = ∫ t in Ioc (0 : ℝ) 1, ∫ x : V, I₃_integrand (x, t) := by
  sorry

/-- Fubini for I₄: swap ∫_{ℝ⁸} and ∫_{[0,1]} -/
theorem I₄_integral_swap :
    ∫ x : V, I₄ x = ∫ t in Icc (0 : ℝ) 1, ∫ x : V, I₄_integrand (x, t) := by
  sorry

/-- Fubini for I₅: swap ∫_{ℝ⁸} and ∫_{(0,1]} -/
theorem I₅_integral_swap :
    ∫ x : V, I₅ x = ∫ t in Ioc (0 : ℝ) 1, ∫ x : V, I₅_integrand (x, t) := by
  sorry

/-- Fubini for I₆: swap ∫_{ℝ⁸} and ∫_{[1,∞)} -/
theorem I₆_integral_swap :
    ∫ x : V, I₆ x = ∫ t in Ici (1 : ℝ), ∫ x : V, I₆_integrand (x, t) := by
  sorry

end FubiniSwap

/-! ## Level 1: Basic Integrability

Each Iⱼ is integrable over ℝ⁸. These follow from the product integrability results
via Tonelli's theorem (integrating out the t parameter).

Note: These may alternatively follow from `a : 𝓢(V, ℂ)` being Schwartz (in Schwartz.lean),
since Schwartz functions are integrable. The proofs here provide a more direct path.
-/

section BasicIntegrability

/-- I₁ is integrable over ℝ⁸. -/
theorem I₁_integrable : Integrable (I₁ : V → ℂ) := by
  sorry

/-- I₂ is integrable over ℝ⁸. -/
theorem I₂_integrable : Integrable (I₂ : V → ℂ) := by
  sorry

/-- I₃ is integrable over ℝ⁸. -/
theorem I₃_integrable : Integrable (I₃ : V → ℂ) := by
  sorry

/-- I₄ is integrable over ℝ⁸. -/
theorem I₄_integrable : Integrable (I₄ : V → ℂ) := by
  sorry

/-- I₅ is integrable over ℝ⁸. -/
theorem I₅_integrable : Integrable (I₅ : V → ℂ) := by
  sorry

/-- I₆ is integrable over ℝ⁸. -/
theorem I₆_integrable : Integrable (I₆ : V → ℂ) := by
  sorry

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

