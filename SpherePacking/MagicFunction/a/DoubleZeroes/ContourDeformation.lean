/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module


public import SpherePacking.MagicFunction.a.DoubleZeroes.CuspBounds
public import SpherePacking.MagicFunction.a.Integrability.CuspPath
public import SpherePacking.MagicFunction.a.Integrability.RealDecay
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Contour Deformation for the Double-Zeroes Argument

The double-zeroes argument deforms the contour defining `a` out to infinity, replacing the
bounded rectangle by unbounded vertical rays. This file supplies what the deformation needs:
the vertical rays are integrable, the integrand along them vanishes at infinity, and the
closing top edge contributes nothing in the limit. Everything here assumes `r > 2`, which is
exactly the range in which `exp(-πrt)` beats the `e^{2πt}` growth of `φ₀(i/t)` from
`CuspBounds`.

## Main results

### The central estimate

* `norm_shiftedMobiusIntegrand_le` — for `t ≥ 1` the shifted-Möbius integrand
  `φ₀''(-1/(a+it)) · (a+it)² · exp(iπr(b+it))` is dominated by `(a²+1) · verticalBound r t`.
  Every decay statement below is a specialisation of this single bound.

### Vertical rays

* `verticalIntegrandX x r t` — the integrand along the vertical ray at horizontal position
  `x`; the case `a = 0` of the central estimate gives its majorant
  (`norm_verticalIntegrandX_le`);
* `integrableOn_verticalIntegrandX` — integrability on `[1, ∞)` for `r > 2`;
* `tendsto_verticalIntegrandX_atTop` and `uniform_vanishing_verticalIntegrandX` — vanishing
  as `t → ∞`, uniformly in `x`.

### Top edge

* `topEdgeIntegrand r x T` — the integrand along the closing edge at height `T`; the case
  `a = b = x ∈ [-1,1]` of the central estimate bounds it by `2 · verticalBound r T`
  (`norm_topEdgeIntegrand_le_two_mul`);
* `uniform_vanishing_topEdgeIntegrand` and `tendsto_topEdgeIntegral_zero` — the top edge
  contributes nothing as `T → ∞`.

### The seven integrability goals

Proposition 4.4.6 of the thesis needs seven vertical-ray integrands to be integrable. They
fall into two families:

* the *unshifted* rays (`integrableOn_centreRay`, `integrableOn_leftRay_Ioi`,
  `integrableOn_rightRay_Ioi`, `integrableOn_leftRay_Ici`, `integrableOn_rightRay_Ici`), which
  are scalar multiples of `verticalIntegrandX`;
* the *shifted-Möbius* rays (`integrableOn_leftShiftedRay`, `integrableOn_rightShiftedRay`),
  where the Möbius argument is `-1/(a + it)` with `a = ±1`; these go through the unified
  `integrableOn_φ₀_shifted_Möbius`.

## References

- Sid's M4R thesis, Section 4.4.1 (Proposition 4.4.6)
- Blueprint, Proposition 7.14
-/

@[expose] public section

open MeasureTheory Set Filter Real Complex UpperHalfPlane TopologicalSpace
open MagicFunction.a MagicFunction.a.ComplexIntegrands

open scoped Interval Real Topology

noncomputable section

namespace MagicFunction.a.DoubleZeroes

/-! ## Normalising the Möbius argument -/

/-- `-1/(I·z) = I/z`. Marked `@[simp]` so the `φ₀''` arguments of the goal integrands
normalise to the `verticalIntegrandX` form automatically. -/
@[simp]
lemma neg_one_div_I_mul (z : ℂ) : (-1 : ℂ) / (Complex.I * z) = Complex.I / z := by
  rw [div_mul_eq_div_div, Complex.div_I]
  ring

/-- `-1/(z·I) = I/z` (other multiplication order). -/
@[simp]
lemma neg_one_div_mul_I (z : ℂ) : (-1 : ℂ) / (z * Complex.I) = Complex.I / z := by
  rw [mul_comm z Complex.I]
  exact neg_one_div_I_mul z

/-! ## Vertical Ray Integrand -/

/-- Vertical ray integrand at horizontal position x.
    Covers #229's edges at x = -1, 0, 1.

    Note: The integrand for vertical contours in the rectangle proof uses
    φ₀''(i/t) rather than φ₀''(it) due to the parameterization. -/
def verticalIntegrandX (x r t : ℝ) : ℂ :=
  Complex.I * φ₀'' (Complex.I / t) * (Complex.I * t)^2 *
    Complex.exp (Complex.I * π * r * (x + Complex.I * t))

/-- The exponential phase factor has norm independent of x. -/
lemma norm_cexp_verticalPhase (x r t : ℝ) :
    ‖Complex.exp (Complex.I * π * r * (x + Complex.I * t))‖ = Real.exp (-π * r * t) := by
  rw [Complex.norm_exp]
  norm_num

/-- Bounding function for the vertical integrand norm.
    Uses the 3-term Cor 7.13 bound with t² · exp(-πrt) distributed. -/
def verticalBound (r t : ℝ) : ℝ :=
  C_φ₀ * t^2 * Real.exp (-(2 * π + π * r) * t)
  + (12 * C_φ₂' / π) * t * Real.exp (-π * r * t)
  + (36 * C_φ₄' / π^2) * Real.exp (-(π * r - 2 * π) * t)

/-! ## The Central Shifted-Möbius Estimate

For `z = a + it` in the upper half-plane, `φ₀''(-1/z) = φ₀(S•z)`, so `norm_φ₀_S_smul_le`
bounds `φ₀''(-1/(a+it)) · (a+it)² · exp(iπr(b+it))` by `(a²+1) · verticalBound r t`. All the
decay estimates in this file specialise this bound.
-/

/-- For z = a + I*t with t > 0, we have Im(-1/z) = t/(a² + t²) > 0.
    This ensures the Möbius-transformed argument stays in the upper half-plane. -/
lemma im_neg_inv_pos (a t : ℝ) (ht : 0 < t) :
    0 < ((-1 : ℂ) / (a + Complex.I * t)).im := by
  -- -1/(a+I·t) = (-(a+I·t))⁻¹, and a+I·t ∈ ℍ, so apply `im_inv_neg_coe_pos`.
  simpa [neg_div, one_div, neg_inv] using
    UpperHalfPlane.im_inv_neg_coe_pos
      (⟨a + Complex.I * t, by simp [Complex.add_im]; exact ht⟩ : UpperHalfPlane)

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

/-- Pointwise norm bound for the shifted-Möbius integrand: for `t ≥ 1` it is dominated by
`(a²+1)·verticalBound r t`. This is the analytic core reused by the integrability goals. -/
lemma norm_shiftedMobiusIntegrand_le (a b r t : ℝ) (ht : 1 ≤ t) :
    ‖φ₀'' (-1 / ((a : ℂ) + Complex.I * t)) * ((a : ℂ) + Complex.I * t) ^ 2 *
        Complex.exp (Complex.I * π * r * ((b : ℂ) + Complex.I * t))‖ ≤
      (a ^ 2 + 1) * verticalBound r t := by
  have ht_pos : 0 < t := lt_of_lt_of_le one_pos ht
  let z : ℂ := a + Complex.I * t
  have hz_im : z.im = t := by simp [z]
  have hz_im_pos : 0 < z.im := by rw [hz_im]; exact ht_pos
  let w : UpperHalfPlane := ⟨z, hz_im_pos⟩
  have hw_im : w.im = t := hz_im
  have hw_im_ge : 1 ≤ w.im := by rw [hw_im]; exact ht
  have hφ₀_eq : φ₀'' (-1 / z) = φ₀ (ModularGroup.S • w) :=
    φ₀''_neg_inv_eq_φ₀_S_smul a t ht_pos
  have hS_bound := norm_φ₀_S_smul_le w hw_im_ge
  have hz_sq_bound : ‖z ^ 2‖ ≤ (a ^ 2 + 1) * t ^ 2 := by
    simp only [z, norm_pow, ← Complex.normSq_eq_norm_sq, mul_comm Complex.I,
      Complex.normSq_add_mul_I]
    nlinarith [sq_nonneg a, sq_nonneg (t - 1), sq_nonneg (a * (t - 1))]
  have hexp_norm : ‖Complex.exp (Complex.I * π * r * (b + Complex.I * t))‖ =
      Real.exp (-π * r * t) := norm_cexp_verticalPhase b r t
  calc ‖φ₀'' (-1 / z) * z ^ 2 * Complex.exp (Complex.I * π * r * (b + Complex.I * t))‖
      = ‖φ₀'' (-1 / z)‖ * ‖z ^ 2‖ * Real.exp (-π * r * t) := by
        rw [norm_mul, norm_mul, hexp_norm]
    _ ≤ ‖φ₀'' (-1 / z)‖ * ((a ^ 2 + 1) * t ^ 2) * Real.exp (-π * r * t) := by
        gcongr
    _ = (a ^ 2 + 1) * (‖φ₀'' (-1 / z)‖ * t ^ 2 * Real.exp (-π * r * t)) := by ring
    _ = (a ^ 2 + 1) * (‖φ₀ (ModularGroup.S • w)‖ * t ^ 2 * Real.exp (-π * r * t)) := by
        rw [hφ₀_eq]
    _ ≤ (a ^ 2 + 1) * verticalBound r t := by
        apply mul_le_mul_of_nonneg_left _ (by nlinarith)
        have hw_norm_ge : t ≤ ‖(w : ℂ)‖ := by
          simpa [hw_im, abs_of_pos ht_pos] using abs_im_le_norm (w : ℂ)
        have hS_bound' : ‖φ₀ (ModularGroup.S • w)‖ ≤
            C_φ₀ * Real.exp (-2 * π * t) + (12 / (π * t)) * C_φ₂'
            + (36 / (π ^ 2 * t ^ 2)) * C_φ₄' * Real.exp (2 * π * t) := by
          rw [hw_im] at hS_bound
          refine hS_bound.trans ?_
          gcongr <;> [exact C_φ₂'_pos.le; exact C_φ₄'_pos.le]
        calc ‖φ₀ (ModularGroup.S • w)‖ * t ^ 2 * Real.exp (-π * r * t)
            ≤ (C_φ₀ * Real.exp (-2 * π * t) + (12 / (π * t)) * C_φ₂'
                + (36 / (π ^ 2 * t ^ 2)) * C_φ₄' * Real.exp (2 * π * t))
              * t ^ 2 * Real.exp (-π * r * t) := by gcongr
          _ = C_φ₀ * t ^ 2 * (Real.exp (-2 * π * t) * Real.exp (-π * r * t))
              + (12 * C_φ₂' / π) * t * Real.exp (-π * r * t)
              + (36 * C_φ₄' / π ^ 2) * (Real.exp (2 * π * t) * Real.exp (-π * r * t)) := by
                field_simp
          _ = verticalBound r t := by
                simp only [verticalBound, ← Real.exp_add]; ring_nf

/-! ## Integrability (complex-valued) -/

/-- Norm of the vertical integrand. -/
lemma norm_verticalIntegrandX (x r t : ℝ) (_ht : 0 < t) :
    ‖verticalIntegrandX x r t‖ = t^2 * ‖φ₀'' (Complex.I / t)‖ * Real.exp (-π * r * t) := by
  simp [verticalIntegrandX, norm_cexp_verticalPhase, sq]
  ring

/-- The vertical bound dominates the integrand norm for t ≥ 1.
    This is the `a = 0` case of `norm_shiftedMobiusIntegrand_le`, since `-1/(it) = i/t`. -/
lemma norm_verticalIntegrandX_le (x r t : ℝ) (ht : 1 ≤ t) :
    ‖verticalIntegrandX x r t‖ ≤ verticalBound r t := by
  have h := norm_shiftedMobiusIntegrand_le 0 x r t ht
  simp only [Complex.ofReal_zero, zero_add, neg_one_div_I_mul] at h
  norm_num at h
  simpa [verticalIntegrandX] using h

/-- For `r > 2` the three exponential rates occurring in `verticalBound` are positive. -/
private lemma pi_rate_pos (r : ℝ) (hr : 2 < r) :
    0 < 2 * π + π * r ∧ 0 < π * r ∧ 0 < π * r - 2 * π :=
  have hπ := Real.pi_pos
  ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- The vertical bound is integrable on [1,∞) for r > 2. -/
lemma integrableOn_verticalBound (r : ℝ) (hr : 2 < r) :
    IntegrableOn (verticalBound r) (Ici 1) volume := by
  -- Sum of three integrable functions
  obtain ⟨h1, h2, h3⟩ := pi_rate_pos r hr
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
  have heq : verticalBound r = fun s => C_φ₀ * (s ^ 2 * Real.exp (-(2 * π + π * r) * s))
      + (12 * C_φ₂' / π) * (s * Real.exp (-(π * r) * s))
      + (36 * C_φ₄' / π ^ 2) * Real.exp (-(π * r - 2 * π) * s) := by
    funext s
    simp only [verticalBound]
    ring_nf
  rw [heq]
  exact (i1.add i2).add i3

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
      fun_prop
    exact h_cont.aestronglyMeasurable measurableSet_Ici
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact norm_verticalIntegrandX_le x r t ht

/-! ## Tendsto at Infinity (Proposition 7.14) -/

/-- The vertical bound → 0 as t → ∞ for r > 2. -/
lemma tendsto_verticalBound_atTop (r : ℝ) (hr : 2 < r) :
    Tendsto (verticalBound r) atTop (𝓝 0) := by
  obtain ⟨h1, h2, h3⟩ := pi_rate_pos r hr
  -- Each term tends to 0
  have t1 : Tendsto (fun s => C_φ₀ * s^2 * Real.exp (-(2 * π + π * r) * s)) atTop (𝓝 0) := by
    simpa [Real.rpow_two] using
      tendsto_const_mul_rpow_mul_exp_neg_atTop C_φ₀ (2 * π + π * r) 2 h1
  have t2 : Tendsto (fun s => (12 * C_φ₂' / π) * s * Real.exp (-π * r * s))
      atTop (𝓝 0) := by
    simpa [neg_mul] using tendsto_const_mul_rpow_mul_exp_neg_atTop (12 * C_φ₂' / π) (π * r) 1 h2
  have t3 : Tendsto (fun s => (36 * C_φ₄' / π^2) * Real.exp (-(π * r - 2 * π) * s))
      atTop (𝓝 0) := by
    simpa using tendsto_const_mul_rpow_mul_exp_neg_atTop (36 * C_φ₄' / π^2) (π * r - 2 * π) 0 h3
  unfold verticalBound
  tendsto_cont

/-- The vertical bound is nonnegative for t ≥ 1. -/
lemma verticalBound_nonneg (r t : ℝ) (ht : 1 ≤ t) : 0 ≤ verticalBound r t := by
  simp only [verticalBound]
  have := C_φ₀_pos; have := C_φ₂'_pos; have := C_φ₄'_pos
  positivity

/-- Vertical integrand → 0 as t → ∞ for r > 2. -/
lemma tendsto_verticalIntegrandX_atTop (x r : ℝ) (hr : 2 < r) :
    Tendsto (fun t => verticalIntegrandX x r t) atTop (𝓝 0) :=
  -- Squeeze: ‖verticalIntegrandX x r t‖ ≤ verticalBound r t → 0
  squeeze_zero_norm'
    (by filter_upwards [eventually_ge_atTop 1] with t ht using norm_verticalIntegrandX_le x r t ht)
    (tendsto_verticalBound_atTop r hr)

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
    The actual integrand in the rectangle deformation is φ₀(-1/z) · z² · exp(πirz)
    where z = x + iT. Note: φ₀''(-1/z) = φ₀(S•z) when z is in ℍ. -/
def topEdgeIntegrand (r x T : ℝ) : ℂ :=
  φ₀'' (-1 / (↑x + Complex.I * ↑T)) * (↑x + Complex.I * ↑T)^2 *
    Complex.exp (Complex.I * π * r * (↑x + Complex.I * ↑T))

/-- Uniform bound on the top edge integrand for x ∈ [-1,1], T ≥ 1: the shifted-Möbius
    estimate `norm_shiftedMobiusIntegrand_le` with `a = b = x`, together with `x² + 1 ≤ 2`. -/
lemma norm_topEdgeIntegrand_le_two_mul (r : ℝ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) {T : ℝ}
    (hT : 1 ≤ T) : ‖topEdgeIntegrand r x T‖ ≤ 2 * verticalBound r T := by
  have hx2 : x ^ 2 + 1 ≤ 2 := by nlinarith [hx.1, hx.2]
  unfold topEdgeIntegrand
  exact (norm_shiftedMobiusIntegrand_le x x r T hT).trans
    (mul_le_mul_of_nonneg_right hx2 (verticalBound_nonneg r T hT))

/-- Uniform vanishing: the top edge integrand is arbitrarily small for all z = x + iT
    with x ∈ [-1,1] and sufficiently large T. This is the form needed by Cauchy-Goursat. -/
lemma uniform_vanishing_topEdgeIntegrand (r : ℝ) (hr : 2 < r) :
    ∀ ε > 0, ∃ M : ℝ, ∀ x T : ℝ, x ∈ Icc (-1 : ℝ) 1 → M ≤ T →
      ‖topEdgeIntegrand r x T‖ < ε := by
  intro ε hε
  have h2 : Tendsto (fun T => 2 * verticalBound r T) atTop (𝓝 0) := by
    simpa using (tendsto_verticalBound_atTop r hr).const_mul 2
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h2 ε hε
  refine ⟨max N 1, fun x T hx hT => ?_⟩
  have hT1 : 1 ≤ T := le_trans (le_max_right N 1) hT
  have hTN : N ≤ T := le_trans (le_max_left N 1) hT
  refine lt_of_le_of_lt (norm_topEdgeIntegrand_le_two_mul r hx hT1) ?_
  simpa [abs_of_nonneg (verticalBound_nonneg r T hT1)] using hN T hTN

/-! ## Filter formulations

Note: the top-edge bound requires `x ∈ [-1,1]`, since `norm_shiftedMobiusIntegrand_le` gives
the constant `x² + 1 ≤ 2`. The rectangle contour of the Cauchy–Goursat application has
bounded real part, so this is no restriction.
-/

/-- Filter version of `uniform_vanishing_topEdgeIntegrand` for a fixed `x ∈ [-1,1]`.
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

    Strategy: Squeeze against the constant-in-x bound of `norm_topEdgeIntegrand_le_two_mul`:
    ‖∫₋₁¹ f(x,T) dx‖ ≤ 2 * (2 * verticalBound r T) → 0 -/
lemma tendsto_topEdgeIntegral_zero (r : ℝ) (hr : 2 < r) :
    Tendsto (fun (T : ℝ) => ∫ x : ℝ in Icc (-1 : ℝ) 1, topEdgeIntegrand r x T)
    atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with T hT
    calc ‖∫ x in Icc (-1 : ℝ) 1, topEdgeIntegrand r x T‖
        ≤ 2 * verticalBound r T * volume.real (Icc (-1 : ℝ) 1) :=
          norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top
            (fun x hx => norm_topEdgeIntegrand_le_two_mul r hx hT)
      _ = 4 * verticalBound r T := by
          have h2 : volume.real (Icc (-1 : ℝ) 1) = 2 := by
            norm_num [Measure.real, Real.volume_Icc]
          rw [h2]; ring
  · simpa using (tendsto_verticalBound_atTop r hr).const_mul 4

/-- The top-edge limit in the interval-integral form used by rectangular contour deformation. -/
lemma tendsto_topEdgeIntervalIntegral_zero (r : ℝ) (hr : 2 < r) :
    Tendsto (fun T : ℝ ↦ ∫ x : ℝ in (-1 : ℝ)..1, topEdgeIntegrand r x T)
      atTop (𝓝 0) := by
  simpa only [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc] using tendsto_topEdgeIntegral_zero r hr

/-! ## General Shifted Möbius Integrability

A unified lemma that handles all six integrability goals via parameter instantiation.
The dominating bound is `norm_shiftedMobiusIntegrand_le`.
-/

/-- General integrability for φ₀''(-1/(a + I*t)) * (a + I*t)² * cexp(I*π*r*(b + I*t)) on Ioi 1.

    This unified lemma covers all six integrability goals from Proposition 4.4.6:
    - Goals 1, 2, 4, 6: Use a = 0 (Category A, reduces to verticalIntegrandX)
    - Goals 3, 5: Use a = ±1 (Category B, shifted Möbius)

    The proof reduces to `norm_shiftedMobiusIntegrand_le` for the dominating bound. -/
lemma integrableOn_φ₀_shifted_Möbius (a b r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => φ₀'' (-1 / ((a : ℂ) + Complex.I * t)) *
      ((a : ℂ) + Complex.I * t)^2 *
      Complex.exp (Complex.I * π * r * ((b : ℂ) + Complex.I * t)))
                 (Ioi 1) volume := by
  -- Strategy: Bound by C * verticalBound r t where C = a² + 1
  -- Key steps:
  -- 1. For t > 1, z = a + I*t has Im(z) = t > 1
  -- 2. Apply φ₀''_neg_inv_eq_φ₀_S_smul to get φ₀(S•w)
  -- 3. Use norm_φ₀_S_smul_le to bound the φ₀ term (uses ‖z‖ ≥ t)
  -- 4. |z²| = a² + t² ≤ (a² + 1) * t² for t ≥ 1
  -- 5. |exp(...)| = exp(-πrt) independent of b
  -- 6. Combined bound ≤ (a² + 1) * verticalBound
  have hbound_integ : IntegrableOn (fun t => (a^2 + 1) * verticalBound r t)
      (Ioi 1) volume := by
    refine IntegrableOn.mono_set ?_ (Ioi_subset_Ici_self (a := 1))
    exact (integrableOn_verticalBound r hr).const_mul (a^2 + 1)
  apply MeasureTheory.Integrable.mono' hbound_integ
  · -- AEStronglyMeasurable: The integrand is continuous on Ioi 1
    -- For t > 0, Im(a + I*t) = t > 0 so -1/(a+I*t) stays in the upper half plane
    -- `φ₀''` is continuous on `ℍ₀`, and `t ↦ -1/(a+I·t)` maps `Ioi 0` into `ℍ₀`
    -- (`im_neg_inv_pos`), so the composition is continuous on `Ioi 0`.
    have h_cont_phi : ContinuousOn (fun t : ℝ => φ₀'' (-1 / (a + Complex.I * t))) (Ioi 0) :=
      φ₀''_holo.continuousOn.comp
        (continuousOn_const.div
          ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousOn)
          (fun t ht h => (ne_of_gt ht) (by simpa using congrArg Complex.im h)))
        (fun t ht => im_neg_inv_pos a t ht)
    have h_cont : ContinuousOn (fun t : ℝ => φ₀'' (-1 / (a + Complex.I * t)) *
        (a + Complex.I * t)^2 * Complex.exp (Complex.I * π * r * (b + Complex.I * t))) (Ioi 1) := by
      have hφ := h_cont_phi.mono (Ioi_subset_Ioi (by linarith : (0:ℝ) ≤ 1))
      fun_prop
    exact h_cont.aestronglyMeasurable measurableSet_Ioi
  · -- Norm bound: dominated by `(a²+1)·verticalBound` (see `norm_shiftedMobiusIntegrand_le`)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_shiftedMobiusIntegrand_le a b r t (le_of_lt ht)

/-! ## Relationship to verticalIntegrandX

The Category A goals (1, 2, 4, 6) are scalar multiples of `verticalIntegrandX`.
-/

/-- Goal 1 integrand equals verticalIntegrandX 0 r t. -/
lemma centreRay_eq_verticalIntegrandX (r t : ℝ) :
    Complex.I * φ₀'' (-1 / (Complex.I * t)) * (Complex.I * t)^2 *
      Complex.exp (Complex.I * π * r * (Complex.I * t)) =
    verticalIntegrandX 0 r t := by
  simp only [verticalIntegrandX, neg_one_div_I_mul, Complex.ofReal_zero, zero_add]

/-- Goal 2 integrand equals -I * verticalIntegrandX (-1) r t.

Proof sketch: Both sides reduce to φ₀''(I/t) * (-t²) * cexp(I*π*r*(-1 + I*t))
after using -1/(I*t) = I/t and (I*t)² = -t². -/
lemma leftRay_eq_neg_I_verticalIntegrandX (r t : ℝ) :
    φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
      Complex.exp (π * Complex.I * r * (-1 + t * Complex.I)) =
    -Complex.I * verticalIntegrandX (-1) r t := by
  simp only [verticalIntegrandX, neg_one_div_mul_I, mul_pow, Complex.ofReal_neg,
    Complex.ofReal_one, neg_mul]
  conv_rhs => rw [Complex.I_sq]
  ring_nf

/-- Goal 4 integrand equals -I * verticalIntegrandX 1 r t.

Proof sketch: Same as Goal 2 but with +1 in the exponential phase. -/
lemma rightRay_eq_neg_I_verticalIntegrandX (r t : ℝ) :
    φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
      Complex.exp (π * Complex.I * r * (1 + t * Complex.I)) =
    -Complex.I * verticalIntegrandX 1 r t := by
  simp only [verticalIntegrandX, neg_one_div_mul_I, mul_pow, Complex.ofReal_one, neg_mul]
  conv_rhs => rw [Complex.I_sq]
  ring_nf

/-- Goal 6 integrand equals verticalIntegrandX (-1) r t.

Proof sketch: Goal 6 = I * Goal 2 = I * (-I) * verticalIntegrandX (-1) r t
= verticalIntegrandX (-1) r t since I * (-I) = 1. -/
lemma leftRay_Ici_eq_verticalIntegrandX (r t : ℝ) :
    Complex.I * (φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
      Complex.exp (π * Complex.I * r * (-1 + t * Complex.I))) =
    verticalIntegrandX (-1) r t := by
  simp only [verticalIntegrandX, neg_one_div_mul_I]
  ring_nf
  simp [pow_two]

/-- Goal 7 integrand equals verticalIntegrandX 1 r t.

Proof sketch: Goal 7 = I * Goal 4 = I * (-I) * verticalIntegrandX 1 r t
= verticalIntegrandX 1 r t since I * (-I) = 1. -/
lemma rightRay_Ici_eq_verticalIntegrandX (r t : ℝ) :
    Complex.I * (φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
      Complex.exp (π * Complex.I * r * (1 + t * Complex.I))) =
    verticalIntegrandX 1 r t := by
  simp only [verticalIntegrandX, neg_one_div_mul_I]
  ring_nf
  simp [pow_two]

/-! ## Helper lemmas for integrability proofs -/

/-- Wrapper for integrability on Ioi 1 (avoids repeated mono_set). -/
lemma integrableOn_verticalIntegrandX_Ioi (x r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t => verticalIntegrandX x r t) (Ioi 1) volume :=
  (integrableOn_verticalIntegrandX x r hr).mono_set Ioi_subset_Ici_self

/-- Integrability of verticalIntegrandX on Ioc 0 1.
    For t ∈ (0, 1], Im(I/t) = 1/t ≥ 1, so the cusp bound ‖φ₀(z)‖ ≤ C₀ exp(-2π·Im(z)) applies.
    Combined with t² ≤ 1 and exp(-πrt) ≤ 1, we get ‖integrand‖ ≤ C₀ exp(-2π). -/
lemma integrableOn_verticalIntegrandX_Ioc (x r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t => verticalIntegrandX x r t) (Ioc 0 1) volume := by
  -- Continuity on (0, 1] for AEStronglyMeasurable
  have hcont : ContinuousOn (fun t => verticalIntegrandX x r t) (Ioc 0 1) := by
    apply ContinuousOn.mono _ (Ioc_subset_Ioi_self)
    unfold verticalIntegrandX
    have h_cont_phi : ContinuousOn (fun t : ℝ => φ₀'' (Complex.I / t)) (Ioi 0) := by
      have h1 := continuousOn_φ₀''_cusp_path
      refine h1.congr fun t ht =>
        congrArg φ₀'' (neg_one_div_I_mul (t : ℂ)).symm
    fun_prop
  have hmeas : AEStronglyMeasurable (fun t => verticalIntegrandX x r t)
      (volume.restrict (Ioc 0 1)) := hcont.aestronglyMeasurable measurableSet_Ioc
  -- Pointwise bound: for t ∈ (0, 1], ‖verticalIntegrandX x r t‖ ≤ C₀ * exp(-2π)
  have hbound : ∀ t ∈ Ioc 0 1, ‖verticalIntegrandX x r t‖ ≤
      C_φ₀ * Real.exp (-2 * π) := by
    intro t ⟨ht_pos, ht_le⟩
    rw [norm_verticalIntegrandX x r t ht_pos]
    have hφ₀_bound : ‖φ₀'' (Complex.I / t)‖ ≤ C_φ₀ * Real.exp (-2 * π / t) :=
      norm_φ₀_I_div_t_small t ⟨ht_pos, by linarith⟩
    have hr_pos : 0 < r := lt_trans (by norm_num : (0:ℝ) < 2) hr
    have ht2_le : t^2 ≤ 1 := by nlinarith [sq_nonneg t, sq_nonneg (t - 1)]
    have hexp_neg : Real.exp (-π * r * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have := mul_pos (mul_pos Real.pi_pos hr_pos) ht_pos; linarith
    have hexp_bound : Real.exp (-2 * π / t) ≤ Real.exp (-2 * π) :=
      Real.exp_le_exp_of_le <| by
        rw [div_le_iff₀ ht_pos]
        nlinarith [Real.pi_pos]
    calc t^2 * ‖φ₀'' (Complex.I / ↑t)‖ * Real.exp (-π * r * t)
        ≤ 1 * (C_φ₀ * Real.exp (-2 * π / t)) * 1 := by
          have h1 : t^2 * ‖φ₀'' (Complex.I / ↑t)‖ ≤ 1 * (C_φ₀ * Real.exp (-2 * π / t)) :=
            mul_le_mul ht2_le hφ₀_bound (norm_nonneg _) zero_le_one
          have h2 : 0 ≤ 1 * (C_φ₀ * Real.exp (-2 * π / t)) :=
            mul_nonneg (by norm_num) (mul_nonneg C_φ₀_pos.le (Real.exp_pos _).le)
          exact mul_le_mul h1 hexp_neg (Real.exp_pos _).le h2
      _ ≤ C_φ₀ * Real.exp (-2 * π) := by
          simp only [one_mul, mul_one]
          exact mul_le_mul_of_nonneg_left hexp_bound C_φ₀_pos.le
  -- Construct IntegrableOn from AEStronglyMeasurable + bounded + finite measure
  exact IntegrableOn.of_bound measure_Ioc_lt_top hmeas (C_φ₀ * Real.exp (-2 * π)) <| by
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact ae_of_all _ hbound

/-- Integrability on [0,∞) for functions equal to verticalIntegrandX on (0,∞).
    Factors out the common proof pattern from Goals 1, 6, and 7. -/
lemma integrableOn_Ici_of_eqOn_verticalIntegrandX (x r : ℝ) (hr : 2 < r) {f : ℝ → ℂ}
    (hEq : EqOn f (fun t => verticalIntegrandX x r t) (Ioi 0)) :
    IntegrableOn f (Ici 0) volume := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi, ← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · exact (integrableOn_verticalIntegrandX_Ioc x r hr).congr_fun
      (hEq.mono Ioc_subset_Ioi_self).symm measurableSet_Ioc
  · exact (integrableOn_verticalIntegrandX_Ioi x r hr).congr_fun
      (hEq.mono (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))).symm measurableSet_Ioi

/-- Integrability on (1,∞) for functions equal to -I * verticalIntegrandX on (1,∞).
    Factors out the common proof pattern from Goals 2 and 4. -/
lemma integrableOn_Ioi_of_eqOn_neg_I_verticalIntegrandX (x r : ℝ) (hr : 2 < r) {f : ℝ → ℂ}
    (hEq : EqOn f (fun t => -Complex.I * verticalIntegrandX x r t) (Ioi 1)) :
    IntegrableOn f (Ioi 1) volume :=
  IntegrableOn.congr_fun ((integrableOn_verticalIntegrandX_Ioi x r hr).const_mul (-Complex.I))
    (fun _ ht => (hEq ht).symm) measurableSet_Ioi

/-- Integrability for shifted Möbius integrands with exponential phase t*I.
    Factors out the common proof pattern from Goals 3 and 5. -/
lemma integrableOn_shiftedMöbius (a r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => φ₀'' (-1 / (t * Complex.I + a)) * (t * Complex.I + a)^2 *
                          Complex.exp (π * Complex.I * r * (t * Complex.I)))
                 (Ioi 1) volume := by
  simpa [mul_comm, add_comm, sub_eq_add_neg] using
    integrableOn_φ₀_shifted_Möbius a 0 r hr

/-! ## Specific Instantiations

The seven integrability goals from Proposition 4.4.6.
-/

/-- Goal 1: Integrability of I * φ₀''(-1/(I*t)) * (I*t)² * cexp(I*π*r*(I*t)) on [0,∞).
    Note: -1/(I*t) = I/t, so this is verticalIntegrandX 0 r t. -/
lemma integrableOn_centreRay (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => Complex.I * φ₀'' (-1 / (Complex.I * t)) * (Complex.I * t)^2 *
                          Complex.exp (Complex.I * π * r * (Complex.I * t)))
                 (Ici (0 : ℝ)) volume :=
  integrableOn_Ici_of_eqOn_verticalIntegrandX 0 r hr fun t _ =>
    centreRay_eq_verticalIntegrandX r t

/-- Goal 2: Integrability of φ₀''(-1/(t*I)) * (t*I)² * cexp(π*I*r*(-1 + t*I)) on (1,∞).
    By leftRay_eq_neg_I_verticalIntegrandX, this is -I * verticalIntegrandX (-1) r t. -/
lemma integrableOn_leftRay_Ioi (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
                          Complex.exp (π * Complex.I * r * (-1 + t * Complex.I)))
                 (Ioi (1 : ℝ)) volume :=
  integrableOn_Ioi_of_eqOn_neg_I_verticalIntegrandX (-1) r hr fun {t} _ =>
    leftRay_eq_neg_I_verticalIntegrandX r t

/-- Goal 3: Integrability of φ₀''(-1/(t*I + 1)) * (t*I+1)² * cexp(π*I*r*(t*I)) on (1,∞).
    Category B: Shifted Möbius argument at +1. Derived from integrableOn_shiftedMöbius. -/
lemma integrableOn_rightShiftedRay (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => φ₀'' (-1 / (t * Complex.I + 1)) * (t * Complex.I + 1)^2 *
                          Complex.exp (π * Complex.I * r * (t * Complex.I)))
                 (Ioi (1 : ℝ)) volume :=
  integrableOn_shiftedMöbius 1 r hr

/-- Goal 4: Integrability of φ₀''(-1/(t*I)) * (t*I)² * cexp(π*I*r*(1 + t*I)) on (1,∞).
    By rightRay_eq_neg_I_verticalIntegrandX, this is -I * verticalIntegrandX 1 r t. -/
lemma integrableOn_rightRay_Ioi (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
                          Complex.exp (π * Complex.I * r * (1 + t * Complex.I)))
                 (Ioi (1 : ℝ)) volume :=
  integrableOn_Ioi_of_eqOn_neg_I_verticalIntegrandX 1 r hr fun {t} _ =>
    rightRay_eq_neg_I_verticalIntegrandX r t

/-- Goal 5: Integrability of φ₀''(-1/(t*I - 1)) * (t*I-1)² * cexp(π*I*r*(t*I)) on (1,∞).
    Category B: Shifted Möbius argument at -1. Derived from integrableOn_shiftedMöbius. -/
lemma integrableOn_leftShiftedRay (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => φ₀'' (-1 / (t * Complex.I - 1)) * (t * Complex.I - 1)^2 *
                          Complex.exp (π * Complex.I * r * (t * Complex.I)))
                 (Ioi (1 : ℝ)) volume := by
  simpa [sub_eq_add_neg] using integrableOn_shiftedMöbius (-1) r hr

/-- Goal 6: Integrability of I * (φ₀''(-1/(t*I)) * (t*I)² * cexp(π*I*r*(-1 + t*I))) on [0,∞).
    By leftRay_Ici_eq_verticalIntegrandX, this is verticalIntegrandX (-1) r t. -/
lemma integrableOn_leftRay_Ici (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => Complex.I * (φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
                          Complex.exp (π * Complex.I * r * (-1 + t * Complex.I))))
                 (Ici (0 : ℝ)) volume :=
  integrableOn_Ici_of_eqOn_verticalIntegrandX (-1) r hr fun t _ =>
    leftRay_Ici_eq_verticalIntegrandX r t

/-- Goal 7: Integrability of I * (φ₀''(-1/(t*I)) * (t*I)² * cexp(π*I*r*(1 + t*I))) on [0,∞).
    By rightRay_Ici_eq_verticalIntegrandX, this is verticalIntegrandX 1 r t. -/
lemma integrableOn_rightRay_Ici (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => Complex.I * (φ₀'' (-1 / (t * Complex.I)) * (t * Complex.I)^2 *
                          Complex.exp (π * Complex.I * r * (1 + t * Complex.I))))
                 (Ici (0 : ℝ)) volume :=
  integrableOn_Ici_of_eqOn_verticalIntegrandX 1 r hr fun t _ =>
    rightRay_Ici_eq_verticalIntegrandX r t


end MagicFunction.a.DoubleZeroes

end
