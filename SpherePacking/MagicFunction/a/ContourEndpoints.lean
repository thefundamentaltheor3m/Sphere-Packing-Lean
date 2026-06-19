/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import SpherePacking.ModularForms.PhiTransform
public import SpherePacking.MagicFunction.a.Integrability.RealDecay
public import SpherePacking.MagicFunction.a.Integrability.CuspPath
public import SpherePacking.MagicFunction.a.PhiBounds
public import Mathlib.MeasureTheory.Integral.IntegrableOn

@[expose] public section

/-!
# Contour Endpoint Bounds for Vertical Rays

This file provides endpoint bounds and integrability lemmas for vertical contour rays,
as needed for the Cauchy-Goursat applications in the double zeroes proof (#229).

## Blueprint references

- **Corollary 7.5-7.7**: Bounds on φ₀, φ₋₂, φ₋₄ for Im(z) > 1/2
- **Corollary 7.13**: φ₀(i/t) = O(t⁻² e^{2πt}) as t → ∞
- **Proposition 7.14**: Vertical integrand → 0 as Im(z) → ∞ for r > 2

## Main results

- `norm_φ₀''_I_div_t_le`: Corollary 7.13 (3-term S-transform bound)
- `verticalIntegrandX`: Integrand for vertical edges at any x position
- `integrableOn_verticalIntegrandX`: Integrability for r > 2
- `tendsto_verticalIntegrandX_atTop`: Integrand → 0 as t → ∞

## Notes

We use `Im(z) ≥ 1` (stronger than the blueprint's `Im(z) > 1/2`) as a convenient
safe strip that covers all rectangle contour points.
-/

open MeasureTheory Set Filter Real UpperHalfPlane TopologicalSpace
open MagicFunction.a

open scoped Interval Real NNReal ENNReal Topology BigOperators

noncomputable section

namespace MagicFunction.ContourEndpoints

/-! ## Filter for imaginary part tending to infinity on ℂ -/

/-- The filter on ℂ of sets containing { z | M ≤ z.im } for some M.
    This is the preimage of `atTop` under `Complex.im`. -/
def atImInfty_ℂ : Filter ℂ := Filter.comap Complex.im atTop

/-- Characterization of membership in `atImInfty_ℂ`. -/
lemma mem_atImInfty_ℂ {s : Set ℂ} : s ∈ atImInfty_ℂ ↔ ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → z ∈ s := by
  simp only [atImInfty_ℂ, Filter.mem_comap, Filter.mem_atTop_sets]
  exact ⟨fun ⟨_, ⟨a, ha⟩, hts⟩ => ⟨a, fun z hz => hts (ha z.im hz)⟩,
         fun ⟨M, hM⟩ => ⟨Ici M, ⟨M, fun _ hb => hb⟩, fun z hz => hM z hz⟩⟩

/-- Tendsto characterization for `atImInfty_ℂ` to `𝓝 0`. -/
lemma tendsto_zero_atImInfty_ℂ_iff {f : ℂ → ℂ} :
    Tendsto f atImInfty_ℂ (𝓝 0) ↔ ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖f z‖ < ε := by
  simp [Metric.tendsto_nhds, dist_zero_right, Filter.eventually_iff, mem_atImInfty_ℂ]

/-- Tendsto characterization for `atImInfty_ℂ` to `𝓝 0` (real-valued version). -/
lemma tendsto_zero_atImInfty_ℂ_iff' {f : ℂ → ℝ} :
    Tendsto f atImInfty_ℂ (𝓝 0) ↔ ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → |f z| < ε := by
  simp [Metric.tendsto_nhds, dist_zero_right, Real.norm_eq_abs, Filter.eventually_iff,
    mem_atImInfty_ℂ]

/-! ## Corollary 7.13 - S-transform bound for φ₀''(I/t) -/

/-- The point it as an element of ℍ for t > 0. -/
def mkI_mul_t (t : ℝ) (ht : 0 < t) : ℍ :=
  ⟨Complex.I * t, by simp; exact ht⟩

/-- S action on it gives i/t. -/
lemma S_smul_I_mul_t (t : ℝ) (ht : 0 < t) :
    (↑(ModularGroup.S • mkI_mul_t t ht) : ℂ) = Complex.I / t := by
  rw [modular_S_smul]
  simp [mkI_mul_t, div_eq_mul_inv, mul_comm]

/-- im(it) = t when viewed as element of ℍ. -/
lemma mkI_mul_t_im (t : ℝ) (ht : 0 < t) : (mkI_mul_t t ht).im = t := by
  simp [mkI_mul_t]

/-- φ₀''(I/t) equals φ₀ applied to S•(I*t). -/
lemma φ₀''_I_div_t_eq (t : ℝ) (ht : 0 < t) :
    φ₀'' (Complex.I / t) = φ₀ (ModularGroup.S • mkI_mul_t t ht) := by
  rw [φ₀''_def (by rw [Complex.div_ofReal_im, Complex.I_im]; positivity)]
  simpa using congrArg φ₀ (UpperHalfPlane.ext (S_smul_I_mul_t t ht).symm)

/-- Norm of I*t equals t for t > 0. -/
lemma norm_I_mul_t (t : ℝ) (ht : 0 < t) : ‖(Complex.I * t : ℂ)‖ = t := by
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]

/-- The coefficient (12I)/(πz) has norm 12/(π|z|). -/
lemma norm_coeff_12I_div (z : ℂ) :
    ‖(12 * Complex.I) / (↑π * z)‖ = 12 / (π * ‖z‖) := by
  rw [norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat]
  simp only [mul_one, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- The coefficient 36/(π²z²) has norm 36/(π²|z|²). -/
lemma norm_coeff_36_div_sq (z : ℂ) :
    ‖36 / (↑π ^ 2 * z ^ 2)‖ = 36 / (π^2 * ‖z‖^2) := by
  rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real]
  simp only [Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat]

/-- General S-transform bound for any z with im(z) ≥ 1.
    This is the generalized Corollary 7.13. -/
lemma norm_φ₀_S_smul_le (z : ℍ) (hz : 1 ≤ z.im) :
    ‖φ₀ (ModularGroup.S • z)‖ ≤ C_φ₀ * Real.exp (-2 * π * z.im)
        + (12 / (π * ‖(z : ℂ)‖)) * C_φ₂'
        + (36 / (π^2 * ‖(z : ℂ)‖^2)) * C_φ₄'
            * Real.exp (2 * π * z.im) := by
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
  -- Derive 1/2 < z.im from 1 ≤ z.im for the φ-bound lemmas
  have hz' : 1/2 < z.im := by linarith
  -- Bound (i): ‖φ₀ z‖ ≤ C₀ * exp(-2πt)  [from φ₀_bound]
  have hbound1 : ‖φ₀ z‖ ≤ C_φ₀ * exp (-2 * π * z.im) := φ₀_bound z hz'
  -- Bound (ii): ‖(12I)/(πz) * φ₂' z‖ ≤ (12/(π‖z‖)) * C₂
  have hbound2 : ‖(12 * Complex.I) / (↑π * z) * φ₂' z‖ ≤ (12 / (π * ‖(z : ℂ)‖)) * C_φ₂' := by
    rw [norm_mul, norm_coeff_12I_div (z : ℂ)]
    exact mul_le_mul_of_nonneg_left (φ₂'_bound z hz') (by positivity)
  -- Bound (iii): ‖36/(π²z²) * φ₄' z‖ ≤ (36/(π²‖z‖²)) * C₄ * exp(2πt)
  have hbound3 : ‖36 / (↑π ^ 2 * ↑z ^ 2) * φ₄' z‖ ≤
      (36 / (π^2 * ‖(z : ℂ)‖^2)) * C_φ₄' * exp (2 * π * z.im) := by
    rw [norm_mul, norm_coeff_36_div_sq (z : ℂ)]
    calc 36 / (π ^ 2 * ‖(z : ℂ)‖ ^ 2) * ‖φ₄' z‖
        ≤ 36 / (π ^ 2 * ‖(z : ℂ)‖ ^ 2) * (C_φ₄' * exp (2 * π * z.im)) :=
          mul_le_mul_of_nonneg_left (φ₄'_bound z hz') (by positivity)
      _ = 36 / (π ^ 2 * ‖(z : ℂ)‖ ^ 2) * C_φ₄' * exp (2 * π * z.im) := by ring
  -- Combine bounds
  linarith

/-- Corollary 7.13: S-transform bound for φ₀(i/t) at large t.
    Specializes norm_φ₀_S_smul_le to z = I*t where z.im = ‖z‖ = t. -/
lemma norm_φ₀''_I_div_t_le (t : ℝ) (ht : 1 ≤ t) :
    ‖φ₀'' (Complex.I / t)‖ ≤ C_φ₀ * Real.exp (-2 * π * t)
                    + (12 / (π * t)) * C_φ₂'
                    + (36 / (π^2 * t^2)) * C_φ₄' * Real.exp (2 * π * t) := by
  have ht_pos : 0 < t := by linarith
  rw [φ₀''_I_div_t_eq t ht_pos]
  have h := norm_φ₀_S_smul_le (mkI_mul_t t ht_pos) (by simpa [mkI_mul_t_im] using ht)
  simp only [mkI_mul_t_im] at h
  rwa [show ‖(↑(mkI_mul_t t ht_pos) : ℂ)‖ = t from norm_I_mul_t t ht_pos] at h

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
  ring_nf
  simp

/-! ## Integrability (complex-valued) -/

/-- Norm of the vertical integrand. -/
lemma norm_verticalIntegrandX (x r t : ℝ) (_ht : 0 < t) :
    ‖verticalIntegrandX x r t‖ = t^2 * ‖φ₀'' (Complex.I / t)‖ * Real.exp (-π * r * t) := by
  simp [verticalIntegrandX, norm_cexp_verticalPhase, sq]
  ring

/-- Bounding function for the vertical integrand norm.
    Uses the 3-term Cor 7.13 bound with t² · exp(-πrt) distributed. -/
def verticalBound (r t : ℝ) : ℝ :=
  C_φ₀ * t^2 * Real.exp (-(2 * π + π * r) * t)
  + (12 * C_φ₂' / π) * t * Real.exp (-π * r * t)
  + (36 * C_φ₄' / π^2) * Real.exp (-(π * r - 2 * π) * t)

/-- The vertical bound dominates the integrand norm for t ≥ 1. -/
lemma norm_verticalIntegrandX_le (x r t : ℝ) (ht : 1 ≤ t) :
    ‖verticalIntegrandX x r t‖ ≤ verticalBound r t := by
  have ht_pos : 0 < t := one_pos.trans_le ht
  rw [norm_verticalIntegrandX x r t ht_pos]
  -- Apply Cor 7.13 bound: ‖φ₀''(I/t)‖ ≤ 3-term bound
  have hbound := norm_φ₀''_I_div_t_le t ht
  -- Need: t² * ‖φ₀''(I/t)‖ * exp(-πrt) ≤ verticalBound
  calc t^2 * ‖φ₀'' (Complex.I / ↑t)‖ * Real.exp (-π * r * t)
      ≤ t^2 * (C_φ₀ * Real.exp (-2 * π * t)
               + (12 / (π * t)) * C_φ₂'
               + (36 / (π^2 * t^2)) * C_φ₄' * Real.exp (2 * π * t))
          * Real.exp (-π * r * t) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbound (sq_nonneg t)) (Real.exp_pos _).le
    _ = verticalBound r t := by
        simp only [verticalBound]
        have ht_ne : t ≠ 0 := ne_of_gt ht_pos
        have hexp1 : Real.exp (-2 * π * t) * Real.exp (-π * r * t) =
            Real.exp (-(2 * π + π * r) * t) := by rw [← Real.exp_add]; ring_nf
        have hexp3 : Real.exp (2 * π * t) * Real.exp (-π * r * t) =
            Real.exp (-(π * r - 2 * π) * t) := by rw [← Real.exp_add]; ring_nf
        calc t^2 * (C_φ₀ * Real.exp (-2 * π * t) + (12 / (π * t)) * C_φ₂'
               + (36 / (π^2 * t^2)) * C_φ₄' * Real.exp (2 * π * t))
             * Real.exp (-π * r * t)
           = C_φ₀ * t^2 * (Real.exp (-2 * π * t) * Real.exp (-π * r * t))
             + (12 * C_φ₂' / π) * t * Real.exp (-π * r * t)
             + (36 * C_φ₄' / π^2) * (Real.exp (2 * π * t) * Real.exp (-π * r * t)) := by
               field_simp
         _ = C_φ₀ * t^2 * Real.exp (-(2 * π + π * r) * t)
             + (12 * C_φ₂' / π) * t * Real.exp (-π * r * t)
             + (36 * C_φ₄' / π^2) * Real.exp (-(π * r - 2 * π) * t) := by
               rw [hexp1, hexp3]

/-- The vertical bound is integrable on [1,∞) for r > 2. -/
lemma integrableOn_verticalBound (r : ℝ) (hr : 2 < r) :
    IntegrableOn (verticalBound r) (Ici 1) volume := by
  -- Sum of three integrable functions
  have h1 : 0 < 2 * π + π * r := by nlinarith [Real.pi_pos]
  have h2 : 0 < π * r := by nlinarith [Real.pi_pos]
  have h3 : 0 < π * r - 2 * π := by nlinarith [Real.pi_pos]
  -- Define integrable components (note: const_mul applies on the left as c * f(x))
  have i1 : IntegrableOn (fun s => C_φ₀ * (s^2 * Real.exp (-(2 * π + π * r) * s)))
      (Ici 1) volume :=
    (_root_.integrableOn_sq_mul_exp_neg_Ici (2 * π + π * r) h1).const_mul _
  have i2 : IntegrableOn (fun s => (12 * C_φ₂' / π) * (s * Real.exp (-(π * r) * s)))
      (Ici 1) volume :=
    (_root_.integrableOn_mul_exp_neg_Ici (π * r) h2).const_mul _
  have i3 : IntegrableOn (fun s => (36 * C_φ₄' / π^2) * Real.exp (-(π * r - 2 * π) * s))
      (Ici 1) volume :=
    (_root_.integrableOn_exp_mul_Ici (-(π * r - 2 * π)) (by linarith)).const_mul _
  convert (i1.add i2).add i3 using 1
  funext s
  simp [verticalBound]
  ring_nf

/-- Vertical ray integrand is integrable on [1,∞) for r > 2. -/
lemma integrableOn_verticalIntegrandX (x r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t => verticalIntegrandX x r t) (Ici 1) volume := by
  -- Bound by verticalBound and use integrability of the bound
  apply MeasureTheory.Integrable.mono' (integrableOn_verticalBound r hr)
  · -- Measurability: verticalIntegrandX is continuous on Ici 1 → AEStronglyMeasurable
    -- I/t = -1/(I*t) via div_mul_eq_div_div + NormNumI
    have h_cont_phi : ContinuousOn (fun t : ℝ => φ₀'' (Complex.I / t)) (Ici 1) := by
      have h1 := continuousOn_φ₀''_cusp_path.mono
        (fun t ht => lt_of_lt_of_le zero_lt_one (mem_Ici.mp ht))
      refine h1.congr (fun t ht => congrArg φ₀'' ?_)
      simp [div_mul_eq_div_div, Complex.div_I]
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
    exact norm_verticalIntegrandX_le x r t ht

/-- Corollary: norm is also integrable. -/
lemma integrableOn_norm_verticalIntegrandX (x r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t => ‖verticalIntegrandX x r t‖) (Ici 1) volume :=
  (integrableOn_verticalIntegrandX x r hr).norm

/-! ## Tendsto at Infinity (Proposition 7.14) -/

/-- The vertical bound → 0 as t → ∞ for r > 2. -/
lemma tendsto_verticalBound_atTop (r : ℝ) (hr : 2 < r) :
    Tendsto (verticalBound r) atTop (𝓝 0) := by
  have h1 : 0 < 2 * π + π * r := by nlinarith [Real.pi_pos]
  have h2 : 0 < π * r := by nlinarith [Real.pi_pos]
  have h3 : 0 < π * r - 2 * π := by nlinarith [Real.pi_pos]
  -- Each term tends to 0
  have t1 : Tendsto (fun s => C_φ₀ * s^2 * Real.exp (-(2 * π + π * r) * s))
      atTop (𝓝 0) := by
    have := (_root_.tendsto_sq_mul_exp_neg_atTop (2 * π + π * r) h1).const_mul C_φ₀
    simp only [mul_zero] at this
    convert this using 1; funext s; ring
  have t2 : Tendsto (fun s => (12 * C_φ₂' / π) * s * Real.exp (-(π * r) * s))
      atTop (𝓝 0) := by
    have := (_root_.tendsto_mul_exp_neg_atTop (π * r) h2).const_mul (12 * C_φ₂' / π)
    simp only [mul_zero] at this
    convert this using 1; funext s; ring
  have t3 : Tendsto (fun s => (36 * C_φ₄' / π^2) * Real.exp (-(π * r - 2 * π) * s))
      atTop (𝓝 0) := by
    simpa [mul_zero] using
      (_root_.tendsto_exp_neg_atTop (π * r - 2 * π) h3).const_mul (36 * C_φ₄' / π^2)
  have hsum := (t1.add t2).add t3
  simp only [add_zero] at hsum
  convert hsum using 1
  funext s
  simp only [verticalBound]
  ring_nf

/-- The vertical bound is nonnegative for t ≥ 1. -/
lemma verticalBound_nonneg (r t : ℝ) (ht : 1 ≤ t) : 0 ≤ verticalBound r t := by
  simp only [verticalBound]
  have := C_φ₀_pos; have := C_φ₂'_pos; have := C_φ₄'_pos
  positivity

/-- Vertical integrand → 0 as t → ∞ for r > 2. -/
lemma tendsto_verticalIntegrandX_atTop (x r : ℝ) (hr : 2 < r) :
    Tendsto (fun t => verticalIntegrandX x r t) atTop (𝓝 0) := by
  -- Use squeeze theorem: ‖f(t)‖ ≤ g(t) → 0 implies f(t) → 0
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (tendsto_verticalBound_atTop r hr) ε hε
  -- Use max(N₁, 1) to ensure we can apply norm_verticalIntegrandX_le
  use max N₁ 1
  intro t ht
  have ht_ge_1 : 1 ≤ t := le_of_max_le_right ht
  have ht_ge_N₁ : t ≥ N₁ := le_of_max_le_left ht
  simp only [dist_zero_right]
  -- ‖integrand‖ ≤ bound < ε
  calc ‖verticalIntegrandX x r t‖
      ≤ verticalBound r t := norm_verticalIntegrandX_le x r t ht_ge_1
    _ < ε := by
        have := hN₁ t ht_ge_N₁
        simp only [dist_zero_right, Real.norm_eq_abs] at this
        rwa [abs_of_nonneg (verticalBound_nonneg r t ‹_›)] at this

/-- Uniform vanishing: the vertical integrand is arbitrarily small for all z
    with sufficiently large imaginary part. This is the form needed by Cauchy-Goursat. -/
lemma uniform_vanishing_verticalIntegrandX (r : ℝ) (hr : 2 < r) :
    ∀ ε > 0, ∃ M : ℝ, ∀ x t : ℝ, M ≤ t → ‖verticalIntegrandX x r t‖ < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_verticalBound_atTop r hr) ε hε
  refine ⟨max N 1, fun x t ht => ?_⟩
  have ht1 : 1 ≤ t := le_trans (le_max_right N 1) ht
  have htN : N ≤ t := le_trans (le_max_left N 1) ht
  exact lt_of_le_of_lt (norm_verticalIntegrandX_le x r t ht1)
    (by simpa [abs_of_nonneg (verticalBound_nonneg r t ‹_›)] using hN t htN)

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
  · have hsq : T^2 ≤ ‖(↑x + Complex.I * ↑T : ℂ)‖^2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp
      nlinarith [sq_nonneg x]
    exact (sq_le_sq₀ (by linarith : 0 ≤ T) (norm_nonneg _)).mp hsq
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
  simp only [modular_S_smul, UpperHalfPlane.coe_mk]
  rw [← neg_inv]; ring

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
  rw [φ₀''_def hneg_inv_im]
  exact congrArg φ₀ (UpperHalfPlane.ext (S_smul_x_add_I_mul_T x T hT).symm)

/-- Bounding function for top edge integrand norm.
    For z = x + iT with x ∈ [-1,1] and T ≥ 1, this bounds ‖topEdgeIntegrand r x T‖. -/
def topEdgeBound (r T : ℝ) : ℝ :=
  (1 + T)^2 * Real.exp (-π * r * T) *
    (C_φ₀ * Real.exp (-2 * π * T) + (12 * C_φ₂' / (π * T))
        + (36 * C_φ₄' / (π^2 * T^2)) * Real.exp (2 * π * T))

/-- The top edge bound → 0 as T → ∞ for r > 2. -/
lemma tendsto_topEdgeBound_atTop (r : ℝ) (hr : 2 < r) :
    Tendsto (topEdgeBound r) atTop (𝓝 0) := by
  unfold topEdgeBound
  have hπ := Real.pi_pos
  have h1 : 0 < π * r + 2 * π := by nlinarith
  have h2 : 0 < π * r := by nlinarith
  have h3 : 0 < π * r - 2 * π := by nlinarith
  -- Strategy: Expand (1+T)² = 1 + 2T + T² and use individual tendsto lemmas
  -- Term 1: C₀ * (1+T)² * exp(-(πr+2π)T) → 0
  have t1 : Tendsto (fun T => C_φ₀ * (1 + T)^2 * Real.exp (-(π * r + 2 * π) * T))
      atTop (𝓝 0) := by
    -- Expand: (1+T)² = 1 + 2T + T²
    have t1a : Tendsto (fun T => C_φ₀ * Real.exp (-(π * r + 2 * π) * T)) atTop (𝓝 0) := by
      have h := (_root_.tendsto_exp_neg_atTop (π * r + 2 * π) h1).const_mul C_φ₀
      simp only [mul_zero] at h; exact h
    have t1b : Tendsto (fun T => 2 * C_φ₀ * T * Real.exp (-(π * r + 2 * π) * T))
        atTop (𝓝 0) := by
      have h := (_root_.tendsto_mul_exp_neg_atTop (π * r + 2 * π) h1).const_mul (2 * C_φ₀)
      simp only [mul_zero] at h
      convert h using 1; funext T; ring
    have t1c : Tendsto (fun T => C_φ₀ * T^2 * Real.exp (-(π * r + 2 * π) * T))
        atTop (𝓝 0) := by
      have h := (_root_.tendsto_sq_mul_exp_neg_atTop (π * r + 2 * π) h1).const_mul C_φ₀
      simp only [mul_zero] at h
      convert h using 1; funext T; ring
    have hsum := (t1a.add t1b).add t1c
    simp only [add_zero] at hsum
    convert hsum using 1
    funext T; ring
  -- Term 2: (12C₂/(πT)) * (1+T)² * exp(-πrT) → 0
  -- Use squeeze: (1+T)²/T ≤ 4T for T ≥ 1
  have t2 : Tendsto (fun T => (12 * C_φ₂' / (π * T)) * (1 + T)^2 * Real.exp (-π * r * T))
      atTop (𝓝 0) := by
    have hbound : Tendsto (fun T => (48 * C_φ₂' / π) * T * Real.exp (-π * r * T))
        atTop (𝓝 0) := by
      have h := (_root_.tendsto_mul_exp_neg_atTop (π * r) h2).const_mul (48 * C_φ₂' / π)
      simp only [mul_zero] at h
      convert h using 1; funext T; ring_nf
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop 1] with T hT
      have hT_pos : 0 < T := by linarith
      apply mul_nonneg (mul_nonneg _ (sq_nonneg _)) (le_of_lt (Real.exp_pos _))
      exact div_nonneg (by linarith [C_φ₂'_pos]) (by positivity)
    · filter_upwards [eventually_ge_atTop 1] with T hT
      have hT_pos : 0 < T := by linarith
      have hπT_pos : 0 < π * T := by positivity
      have h1 : (12 * C_φ₂' / (π * T)) * (1 + T)^2 =
          (12 * C_φ₂' / π) * ((1 + T)^2 / T) := by
        field_simp
      have h2 : (1 + T)^2 / T = 1 / T + 2 + T := by field_simp; ring
      have h3 : 1 / T + 2 + T ≤ 4 * T := by
        have : 1 / T ≤ 1 := (div_le_one hT_pos).mpr hT
        linarith
      calc (12 * C_φ₂' / (π * T)) * (1 + T)^2 * Real.exp (-π * r * T)
          = (12 * C_φ₂' / π) * (1 / T + 2 + T) * Real.exp (-π * r * T) := by
              rw [h1, h2]
        _ ≤ (12 * C_φ₂' / π) * (4 * T) * Real.exp (-π * r * T) := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3
              (div_nonneg (by linarith [C_φ₂'_pos]) hπ.le)) (Real.exp_pos _).le
        _ = (48 * C_φ₂' / π) * T * Real.exp (-π * r * T) := by ring
    · exact hbound
  -- Term 3: (36C₄/(π²T²)) * (1+T)² * exp(2πT-πrT) → 0
  -- Use squeeze: (1+T)²/T² ≤ 4 for T ≥ 1
  have t3 : Tendsto (fun T => (36 * C_φ₄' / (π^2 * T^2)) * (1 + T)^2 *
      Real.exp (2 * π * T) * Real.exp (-π * r * T)) atTop (𝓝 0) := by
    have hbound : Tendsto (fun T => (144 * C_φ₄' / π^2) * Real.exp (-(π * r - 2 * π) * T))
        atTop (𝓝 0) := by
      simpa using (_root_.tendsto_exp_neg_atTop (π * r - 2 * π) h3).const_mul
        (144 * C_φ₄' / π^2)
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop 1] with T hT
      have hT_pos : 0 < T := by linarith
      apply mul_nonneg (mul_nonneg (mul_nonneg _ (sq_nonneg _)) (le_of_lt (Real.exp_pos _)))
          (le_of_lt (Real.exp_pos _))
      exact div_nonneg (by linarith [C_φ₄'_pos]) (by positivity)
    · filter_upwards [eventually_ge_atTop 1] with T hT
      have hT_pos : 0 < T := by linarith
      have hexp_comb : Real.exp (2 * π * T) * Real.exp (-π * r * T) =
          Real.exp (-(π * r - 2 * π) * T) := by rw [← Real.exp_add]; ring_nf
      have h1 : (1 + T)^2 / T^2 = (1 / T + 1)^2 := by field_simp
      have hle2 : 1 / T + 1 ≤ 2 := by
        have : 1 / T ≤ 1 := (div_le_one hT_pos).mpr hT
        linarith
      have h2 : (1 / T + 1)^2 ≤ 4 := by
        have h0 : 0 ≤ 1 / T + 1 := by positivity
        calc (1 / T + 1)^2 ≤ 2^2 := sq_le_sq' (by linarith) hle2
          _ = 4 := by norm_num
      -- Combine the exponentials and rearrange
      calc (36 * C_φ₄' / (π^2 * T^2)) * (1 + T)^2 * Real.exp (2 * π * T) *
               Real.exp (-π * r * T)
          = (36 * C_φ₄' / π^2) * ((1 + T)^2 / T^2) *
              (Real.exp (2 * π * T) * Real.exp (-π * r * T)) := by field_simp
        _ = (36 * C_φ₄' / π^2) * (1 / T + 1)^2 * Real.exp (-(π * r - 2 * π) * T) := by
              rw [h1, hexp_comb]
        _ ≤ (36 * C_φ₄' / π^2) * 4 * Real.exp (-(π * r - 2 * π) * T) := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2
              (div_nonneg (by linarith [C_φ₄'_pos]) (sq_nonneg π))) (Real.exp_pos _).le
        _ = (144 * C_φ₄' / π^2) * Real.exp (-(π * r - 2 * π) * T) := by ring
    · exact hbound
  simpa [pow_two, topEdgeBound, mul_add, add_mul, left_distrib, right_distrib,
    mul_assoc, mul_left_comm, mul_comm, Real.exp_add] using (t1.add t2).add t3

/-- The top edge bound is nonnegative for T ≥ 1. -/
lemma topEdgeBound_nonneg (r T : ℝ) (hT : 1 ≤ T) : 0 ≤ topEdgeBound r T := by
  simp only [topEdgeBound]
  have := C_φ₀_pos; have := C_φ₂'_pos; have := C_φ₄'_pos
  positivity

/-- Uniform bound on top edge integrand for x ∈ [-1,1], T ≥ 1.
    Uses S-transform bound (norm_φ₀_S_smul_le) with ‖z‖ ≥ T.

    Proof strategy:
    1. Show φ₀''(-1/z) = φ₀(S•w) where w = x + iT ∈ ℍ
    2. Apply norm_φ₀_S_smul_le to get 3-term bound
    3. Use ‖z‖ ≥ T to bound 1/‖z‖ terms by 1/T
    4. Combine with ‖z²‖ ≤ (1+T)² and exponential phase norm -/
lemma norm_topEdgeIntegrand_le (r : ℝ) (x T : ℝ)
    (hx : x ∈ Icc (-1 : ℝ) 1) (hT : 1 ≤ T) :
    ‖topEdgeIntegrand r x T‖ ≤ topEdgeBound r T := by
  have hT_pos : 0 < T := lt_of_lt_of_le one_pos hT
  let z : ℂ := ↑x + Complex.I * ↑T
  have hz_im : z.im = T := by simp [z]
  let w : ℍ := ⟨z, hz_im ▸ hT_pos⟩
  rcases norm_x_add_I_mul_T_bounds x T hx hT with ⟨hz_norm_ge, hz_norm_le⟩
  have hφ₀_eq : φ₀'' (-1 / z) = φ₀ (ModularGroup.S • w) := by
    simpa [w, z] using φ₀''_neg_inv_eq_φ₀_S_smul x T hT_pos
  have hS_bound := norm_φ₀_S_smul_le w (by simpa [w, z] using hT)
  have hz_sq_norm : ‖z^2‖ ≤ (1 + T)^2 := by
    rw [norm_pow]
    exact sq_le_sq' (by linarith) hz_norm_le
  have hexp_norm : ‖Complex.exp (Complex.I * π * r * z)‖ = Real.exp (-π * r * T) := by
    simpa [z] using norm_cexp_verticalPhase x r T
  unfold topEdgeIntegrand topEdgeBound
  simp only [z] at *
  rw [norm_mul, norm_mul, hφ₀_eq, hexp_norm]
  -- Replace ‖z‖ with T in the S-transform bound (‖z‖ ≥ T → 1/‖z‖ ≤ 1/T)
  have hS_bound' : ‖φ₀ (ModularGroup.S • w)‖ ≤
      C_φ₀ * Real.exp (-2 * π * T) + 12 * C_φ₂' / (π * T) +
        36 * C_φ₄' / (π^2 * T^2) * Real.exp (2 * π * T) := by
    rw [show w.im = T from hz_im] at hS_bound
    calc ‖φ₀ (ModularGroup.S • w)‖
        ≤ C_φ₀ * Real.exp (-2 * π * T) + 12 / (π * ‖(w : ℂ)‖) * C_φ₂' +
            36 / (π^2 * ‖(w : ℂ)‖^2) * C_φ₄' * Real.exp (2 * π * T) := hS_bound
      _ ≤ C_φ₀ * Real.exp (-2 * π * T) + 12 / (π * T) * C_φ₂' +
            36 / (π^2 * T^2) * C_φ₄' * Real.exp (2 * π * T) := by
          apply add_le_add
          · apply add_le_add le_rfl
            apply mul_le_mul_of_nonneg_right _ (le_of_lt C_φ₂'_pos)
            exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
              (mul_le_mul_of_nonneg_left hz_norm_ge (le_of_lt Real.pi_pos))
          · apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
            apply mul_le_mul_of_nonneg_right _ (le_of_lt C_φ₄'_pos)
            exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
              (mul_le_mul_of_nonneg_left
                ((sq_le_sq₀ (by linarith : 0 ≤ T) (norm_nonneg _)).mpr hz_norm_ge) (sq_nonneg π))
      _ = _ := by ring
  calc ‖φ₀ (ModularGroup.S • w)‖ * ‖(↑x + Complex.I * ↑T)^2‖ * Real.exp (-π * r * T)
      ≤ (C_φ₀ * Real.exp (-2 * π * T) + 12 * C_φ₂' / (π * T) +
          36 * C_φ₄' / (π^2 * T^2) * Real.exp (2 * π * T)) * (1 + T)^2 *
            Real.exp (-π * r * T) := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
        apply mul_le_mul hS_bound' hz_sq_norm (norm_nonneg _)
        have := C_φ₀_pos; have := C_φ₂'_pos; have := C_φ₄'_pos
        positivity
    _ = _ := by ring

/-- Uniform vanishing: the top edge integrand is arbitrarily small for all z = x + iT
    with x ∈ [-1,1] and sufficiently large T. This is the form needed by Cauchy-Goursat. -/
lemma uniform_vanishing_topEdgeIntegrand (r : ℝ) (hr : 2 < r) :
    ∀ ε > 0, ∃ M : ℝ, ∀ x T : ℝ, x ∈ Icc (-1 : ℝ) 1 → M ≤ T →
      ‖topEdgeIntegrand r x T‖ < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_topEdgeBound_atTop r hr) ε hε
  refine ⟨max N 1, fun x T hx hT => ?_⟩
  have hT1 : 1 ≤ T := le_trans (le_max_right N 1) hT
  have hTN : N ≤ T := le_trans (le_max_left N 1) hT
  exact lt_of_le_of_lt (norm_topEdgeIntegrand_le r x T hx hT1)
    (by simpa [abs_of_nonneg (topEdgeBound_nonneg r T hT1)] using hN T hTN)

/-! ## Filter-based uniform vanishing (alternative formulation)

These lemmas express uniform vanishing using the `atImInfty_ℂ` filter,
providing a filter-theoretic interface that composes well with other lemmas.

Note: The bounds `topEdgeBound` require `x ∈ [-1,1]` because `‖z‖ ≤ 1+T` is used.
For the full Cauchy-Goursat application, the rectangle contour has bounded real part,
so this restriction is acceptable.
-/

/-- Filter version of uniform_vanishing_verticalIntegrandX.
    The vertical integrand tends to 0 under the `atImInfty_ℂ` filter
    (composed with the embedding t ↦ x + it for any fixed x). -/
lemma tendsto_verticalIntegrandX_atImInfty_ℂ (x r : ℝ) (hr : 2 < r) :
    Tendsto (fun t : ℝ => verticalIntegrandX x r t) atTop (𝓝 0) :=
  tendsto_verticalIntegrandX_atTop x r hr

/-- Filter version of uniform_vanishing_topEdgeIntegrand for a fixed x ∈ [-1,1].
    The top edge integrand tends to 0 under `atTop` filter on T. -/
lemma tendsto_topEdgeIntegrand_atTop (r : ℝ) (hr : 2 < r) (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun T : ℝ => topEdgeIntegrand r x T) atTop (𝓝 0) := by
  simpa [Metric.tendsto_atTop] using fun ε hε =>
    (uniform_vanishing_topEdgeIntegrand r hr ε hε).imp fun M hM T hT => hM x T hx hT

/-- The uniform vanishing property expressed as: eventually, the integrand norm
    is bounded by any positive ε, uniformly in x. -/
lemma eventually_norm_topEdgeIntegrand_lt (r : ℝ) (hr : 2 < r) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T in atTop, ∀ x ∈ Icc (-1 : ℝ) 1, ‖topEdgeIntegrand r x T‖ < ε := by
  obtain ⟨M, hM⟩ := uniform_vanishing_topEdgeIntegrand r hr ε hε
  filter_upwards [eventually_ge_atTop M] with T hT x hx
  exact hM x T hx hT

/-- Top horizontal edge integral vanishes as height T → ∞.
    This is the "integrand at i∞ disappears" fact from Proposition 7.14.

    The integrand involves φ₀(-1/z) = φ₀(S•z), not φ₀(z) directly.
    For z = x + iT with T large, the S-transform bound gives exponential decay.

    Strategy: Use squeeze theorem with topEdgeBound
    ‖∫₋₁¹ f(x,T) dx‖ ≤ ∫₋₁¹ ‖f(x,T)‖ dx ≤ 2 * topEdgeBound(T) → 0 -/
lemma tendsto_topEdgeIntegral_zero (r : ℝ) (hr : 2 < r) :
    Tendsto (fun (T : ℝ) => ∫ x : ℝ in Icc (-1 : ℝ) 1, topEdgeIntegrand r x T)
    atTop (𝓝 0) := by
  -- Strategy: Use tendsto_zero_iff_norm_tendsto_zero + squeeze_zero'
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with T hT
    calc ‖∫ x in Icc (-1 : ℝ) 1, topEdgeIntegrand r x T‖
        ≤ topEdgeBound r T * volume.real (Icc (-1 : ℝ) 1) :=
          norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top
            (fun x hx => norm_topEdgeIntegrand_le r x T hx hT)
      _ = 2 * topEdgeBound r T := by
          norm_num [Measure.real, Real.volume_Icc, mul_comm]
  · simpa using (tendsto_topEdgeBound_atTop r hr).const_mul 2

end MagicFunction.ContourEndpoints

end
