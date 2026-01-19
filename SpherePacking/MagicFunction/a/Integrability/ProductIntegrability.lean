/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import SpherePacking.MagicFunction.a.Basic
import SpherePacking.MagicFunction.a.Schwartz
import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.MagicFunction.RealDecay
import SpherePacking.MagicFunction.CuspPath
import SpherePacking.ModularForms.Derivative
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Product Integrability for Contour Segment Integrands

This file defines the integrand functions I₁_integrand through I₆_integrand for the
contour integral components in the magic function decomposition, and proves they are
integrable on V × (contour parameter) where V = ℝ⁸.

## Main definitions

- `I₁_integrand` through `I₆_integrand` : Integrands on V × ℝ

## Main results

- `Φ₁_prod_integrable` through `Φ₆_prod_integrable` : Product integrability

See `MagicFunction/Fubini.lean` for the Fubini swap lemmas that use these results.
-/

open MeasureTheory Complex Real Set intervalIntegral

local notation "V" => EuclideanSpace ℝ (Fin 8)

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
open MagicFunction.a.RealIntegrands MagicFunction.a.ComplexIntegrands

noncomputable section

/-! ## Workhorse Lemmas

These lemmas are used across multiple integrability proofs.
-/

/-- Norm of cexp(-π * ‖x‖²) equals exp(-π * ‖x‖²). -/
lemma norm_cexp_neg_pi_norm_sq (x : V) : ‖cexp ((-π : ℂ) * ‖x‖^2)‖ = Real.exp (-π * ‖x‖^2) := by
  simp only [← ofReal_neg, ← ofReal_pow, ← ofReal_mul, norm_exp_ofReal]

/-- Norm of cexp(-π * ‖x‖² * t) equals exp(-π * ‖x‖² * t). -/
lemma norm_cexp_neg_pi_norm_sq_mul (x : V) (t : ℝ) :
    ‖cexp (-π * ‖x‖^2 * t)‖ = Real.exp (-π * ‖x‖^2 * t) := by
  simp only [← ofReal_neg, ← ofReal_pow, ← ofReal_mul, norm_exp_ofReal]

/-- ‖x‖² is continuous on V × ℝ (projecting to first component). -/
lemma continuous_norm_sq_fst : Continuous (fun p : V × ℝ => (‖p.1‖^2 : ℂ)) := by
  simp_rw [← ofReal_pow]
  exact continuous_ofReal.comp ((continuous_norm.comp continuous_fst).pow 2)

/-- Product measure with restricted second component equals restricted product measure. -/
lemma volume_prod_restrict_eq (s : Set ℝ) :
    (volume : Measure V).prod ((volume : Measure ℝ).restrict s) =
    ((volume : Measure V).prod (volume : Measure ℝ)).restrict (Set.univ ×ˢ s) := by
  conv_lhs => rw [← Measure.restrict_univ (μ := (volume : Measure V))]
  rw [Measure.prod_restrict]

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

/-! ## Horizontal Segments (I₂, I₄)

For I₂ and I₄, the argument to φ₀'' has Im ≥ 1/2 throughout:
- I₂: z = -1/(t + I) has Im = 1/(t² + 1) ≥ 1/2 for t ∈ [0,1]
- I₄: z = -1/(-t + I) has Im = 1/(t² + 1) ≥ 1/2 for t ∈ [0,1]

So `norm_φ₀_le` applies, giving uniform bounds on φ₀''.
-/

section HorizontalSegments

/-- normSq(s + I) = s² + 1 for any s ∈ ℝ. -/
lemma normSq_add_I (s : ℝ) : normSq (s + I) = s^2 + 1 := by simp [normSq, sq]

/-- Core formula: Im(-1/(s + I)) = 1/(s² + 1) for any s ∈ ℝ. -/
lemma im_neg_inv_add_I_eq (s : ℝ) : (-1 / (s + I)).im = 1 / (s^2 + 1) := by
  simp [neg_div, inv_im, normSq_add_I]

/-- Alias for normSq_add_I with t. -/
lemma normSq_t_add_I (t : ℝ) : normSq (t + I) = t^2 + 1 := normSq_add_I t

/-- Alias for im_neg_inv_add_I_eq with t. -/
lemma im_neg_inv_t_add_I_eq (t : ℝ) : (-1 / (t + I)).im = 1 / (t^2 + 1) := im_neg_inv_add_I_eq t

/-- For t ∈ [0,1], Im(-1/(t + I)) ≥ 1/2. -/
lemma im_neg_inv_t_add_I (t : ℝ) (ht : t ∈ Icc 0 1) : 1/2 ≤ (-1 / (t + I)).im := by
  rw [im_neg_inv_t_add_I_eq]
  have ht2 : t^2 ≤ 1 := by nlinarith [ht.1, ht.2, sq_nonneg t]
  rw [one_div_le_one_div (by positivity) (by positivity : (0 : ℝ) < t^2 + 1)]
  linarith

/-- For t ∈ [0,1], Im(-1/(-t + I)) ≥ 1/2. Same formula as im_neg_inv_t_add_I since (-t)² = t². -/
lemma im_neg_inv_neg_t_add_I (t : ℝ) (ht : t ∈ Icc 0 1) : 1/2 ≤ (-1 / (-t + I)).im := by
  rw [show (-↑t : ℂ) + I = ↑(-t) + I by simp, im_neg_inv_add_I_eq (-t), neg_sq,
    one_div_le_one_div (by positivity) (by positivity : (0 : ℝ) < t^2 + 1)]
  nlinarith [ht.1, ht.2, sq_nonneg t]

/-- For t ∈ [0,1], |(t + I)²| ≤ 2. -/
lemma norm_sq_t_add_I_le (t : ℝ) (ht : t ∈ Icc 0 1) : ‖(t + I) ^ 2‖ ≤ 2 := by
  rw [norm_pow, ← normSq_eq_norm_sq, normSq_t_add_I]
  nlinarith [sq_nonneg t, ht.1, ht.2]

/-- For t ∈ [0,1], |(-t + I)²| ≤ 2. -/
lemma norm_sq_neg_t_add_I_le (t : ℝ) (ht : t ∈ Icc 0 1) : ‖(-t + I) ^ 2‖ ≤ 2 := by
  rw [norm_pow, ← normSq_eq_norm_sq, show normSq (-↑t + I) = t^2 + 1 by simp [normSq, sq]]
  nlinarith [sq_nonneg t, ht.1, ht.2]

/-- For t ∈ [0,1], the positive imaginary part of -1/(t+I). -/
lemma im_neg_inv_t_add_I_pos (t : ℝ) (ht : t ∈ Icc 0 1) : 0 < (-1 / (t + I)).im :=
  lt_of_lt_of_le (by norm_num) (im_neg_inv_t_add_I t ht)

/-- For t ∈ [0,1], the positive imaginary part of -1/(-t+I). -/
lemma im_neg_inv_neg_t_add_I_pos (t : ℝ) (ht : t ∈ Icc 0 1) : 0 < (-1 / (-t + I)).im :=
  lt_of_lt_of_le (by norm_num) (im_neg_inv_neg_t_add_I t ht)

/-- For any t ∈ ℝ, Im(-1/(t+I)) = 1/(t² + 1) > 0. -/
lemma im_neg_inv_t_add_I_pos_general (t : ℝ) : 0 < (-1 / (t + I)).im := by
  rw [im_neg_inv_t_add_I_eq]
  positivity

/-- The path t ↦ -1/(t+I) is continuous on ℝ. -/
lemma continuous_neg_inv_t_add_I : Continuous (fun t : ℝ => -1 / (t + I)) := by
  refine Continuous.div continuous_const (continuous_ofReal.add continuous_const) ?_
  intro t h
  have him : (t + I).im = 0 := by rw [h]; simp
  simp at him

/-- Generic helper: φ₀'' ∘ g is continuous when g is continuous and Im(g t) > 0 for all t. -/
lemma continuous_φ₀''_comp {g : ℝ → ℂ} (hg : Continuous g) (h_im : ∀ t, 0 < (g t).im) :
    Continuous (fun t => φ₀'' (g t)) := by
  have h_lift : Continuous (fun t => (⟨g t, h_im t⟩ : UpperHalfPlane)) :=
    Continuous.subtype_mk hg h_im
  exact (φ₀_continuous.comp h_lift).congr fun t => (φ₀''_eq _ (h_im t)).symm

/-- The map t ↦ φ₀''(-1/(t+I)) is continuous. -/
lemma continuous_φ₀''_I₂_param : Continuous (fun t : ℝ => φ₀'' (-1 / (t + I))) :=
  continuous_φ₀''_comp continuous_neg_inv_t_add_I im_neg_inv_t_add_I_pos_general

/-- For t ∈ [0,1), Im(-1/(t+I)) > 1/2. Uses t² < 1 when t < 1. -/
lemma im_neg_inv_t_add_I_gt_half (t : ℝ) (ht : t ∈ Ico 0 1) : 1/2 < (-1 / (t + I)).im := by
  rw [im_neg_inv_t_add_I_eq]
  have ht2 : t^2 < 1 := by nlinarith [sq_nonneg t, ht.1, ht.2]
  have h_lt : t^2 + 1 < 2 := by linarith
  exact (one_div_lt_one_div (by positivity) (by positivity : (0 : ℝ) < t^2 + 1)).mpr h_lt

/-- Bound on φ₀'' for I₂/I₄ segments: given Im > 1/2, we get |φ₀''(z)| ≤ C₀ * e^{-π}. -/
lemma norm_φ₀''_bound_of_im_gt_half {z : ℂ} (him_pos : 0 < z.im) (him_ge : 1 / 2 < z.im) :
    ∃ C₀ > 0, ‖φ₀'' z‖ ≤ C₀ * Real.exp (-π) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  refine ⟨C₀, hC₀_pos, ?_⟩
  let w : UpperHalfPlane := ⟨z, him_pos⟩
  rw [φ₀''_eq _ him_pos]
  calc ‖φ₀ w‖ ≤ C₀ * Real.exp (-2 * π * w.im) := hC₀ w him_ge
    _ ≤ C₀ * Real.exp (-π) := by
        gcongr
        have : 2 * π * w.im > 2 * π * (1/2) := mul_lt_mul_of_pos_left him_ge (by positivity)
        linarith [Real.pi_pos]

/-- Bound on φ₀'' for I₂ segment: |φ₀''(-1/(t+I))| ≤ C₀ * e^{-π} for t ∈ [0,1). -/
lemma norm_φ₀''_I₂_bound_Ico : ∃ C₀ > 0, ∀ t : ℝ, t ∈ Ico 0 1 →
    ‖φ₀'' (-1 / (t + I))‖ ≤ C₀ * Real.exp (-π) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  refine ⟨C₀, hC₀_pos, fun t ht => ?_⟩
  have him_pos := im_neg_inv_t_add_I_pos t (Ico_subset_Icc_self ht)
  have him_ge := im_neg_inv_t_add_I_gt_half t ht
  let z : UpperHalfPlane := ⟨-1 / (t + I), him_pos⟩
  rw [φ₀''_eq _ him_pos]
  calc ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im) := hC₀ z him_ge
    _ ≤ C₀ * Real.exp (-π) := by
        gcongr; have : 2 * π * z.im > 2 * π * (1/2) := mul_lt_mul_of_pos_left him_ge (by positivity)
        linarith [Real.pi_pos]

/-- For any t ∈ ℝ, Im(-1/(-t+I)) = 1/(t² + 1) > 0. -/
lemma im_neg_inv_neg_t_add_I_pos_general (t : ℝ) : 0 < (-1 / (-t + I)).im := by
  have hns : normSq (-t + I) = t^2 + 1 := by simp [normSq, sq]
  simp only [neg_div, neg_im, one_div, inv_im, add_im, neg_im, ofReal_im, I_im, neg_neg, hns]
  positivity

/-- The path t ↦ -1/(-t+I) is continuous on ℝ. -/
lemma continuous_neg_inv_neg_t_add_I : Continuous (fun t : ℝ => -1 / (-t + I)) := by
  refine Continuous.div continuous_const (continuous_ofReal.neg.add continuous_const) ?_
  intro t h
  have him : (-t + I).im = 0 := by rw [h]; simp
  simp at him

/-- The map t ↦ φ₀''(-1/(-t+I)) is continuous. -/
lemma continuous_φ₀''_I₄_param : Continuous (fun t : ℝ => φ₀'' (-1 / (-t + I))) :=
  continuous_φ₀''_comp continuous_neg_inv_neg_t_add_I im_neg_inv_neg_t_add_I_pos_general

/-- For t ∈ [0,1), Im(-1/(-t+I)) > 1/2. -/
lemma im_neg_inv_neg_t_add_I_gt_half (t : ℝ) (ht : t ∈ Ico 0 1) : 1/2 < (-1 / (-t + I)).im := by
  have hns : normSq (-t + I) = t^2 + 1 := by simp [normSq, sq]
  simp only [neg_div, neg_im, one_div, inv_im, add_im, neg_im, ofReal_im, I_im, neg_neg, hns]
  have ht2 : t^2 < 1 := by nlinarith [sq_nonneg t, ht.1, ht.2]
  have h_lt : t^2 + 1 < 2 := by linarith
  have h_pos : 0 < t^2 + 1 := by positivity
  calc 2⁻¹ = (2 : ℝ)⁻¹ := rfl
    _ < (t^2 + 1)⁻¹ := by rwa [inv_lt_inv₀ (by positivity) h_pos]
    _ = (-0 + 1) / (t^2 + 1) := by ring

/-- Bound on φ₀'' for I₄ segment: |φ₀''(-1/(-t+I))| ≤ C₀ * e^{-π} for t ∈ [0,1). -/
lemma norm_φ₀''_I₄_bound_Ico : ∃ C₀ > 0, ∀ t : ℝ, t ∈ Ico 0 1 →
    ‖φ₀'' (-1 / (-t + I))‖ ≤ C₀ * Real.exp (-π) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  refine ⟨C₀, hC₀_pos, fun t ht => ?_⟩
  have him_pos := im_neg_inv_neg_t_add_I_pos t (Ico_subset_Icc_self ht)
  have him_ge := im_neg_inv_neg_t_add_I_gt_half t ht
  let z : UpperHalfPlane := ⟨-1 / (-t + I), him_pos⟩
  rw [φ₀''_eq _ him_pos]
  calc ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im) := hC₀ z him_ge
    _ ≤ C₀ * Real.exp (-π) := by
        gcongr; have : 2 * π * z.im > 2 * π * (1/2) := mul_lt_mul_of_pos_left him_ge (by positivity)
        linarith [Real.pi_pos]

/-- Continuity of exponential factor cexp(π·I·‖x‖²·z(t)) on V × ℝ.
    This is the common exponential factor in I₂ and I₄ integrands. -/
lemma continuous_cexp_norm_sq_mul_path {z : ℝ → ℂ} (hz : Continuous z) :
    Continuous (fun p : V × ℝ => cexp (π * I * ((‖p.1‖^2 : ℝ) : ℂ) * z p.2)) := by
  refine Complex.continuous_exp.comp ?_
  have h_norm : Continuous (fun p : V × ℝ => ((‖p.1‖^2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_norm.comp continuous_fst).pow 2)
  exact (continuous_const.mul h_norm).mul (hz.comp continuous_snd)

/-- Helper for paths where w(t).im = 1: the function -1/w(t) has positive imaginary part. -/
lemma im_neg_inv_pos_of_im_one {w : ℝ → ℂ} (him : ∀ t, (w t).im = 1) (t : ℝ) :
    0 < (-1 / w t).im := by
  simp only [neg_div, neg_im, one_div, inv_im, him, neg_neg]
  have hns : 0 < normSq (w t) := normSq_pos.mpr fun h => by
    have : (w t).im = 0 := by rw [h]; simp
    rw [him] at this; exact one_ne_zero this
  positivity

/-- Continuity of φ₀''(-1/w(t)) when w is continuous and w(t).im = 1 for all t.
    This is the common φ₀'' factor in I₂ and I₄ integrands. -/
lemma continuous_φ₀''_neg_inv_im_one {w : ℝ → ℂ} (hw : Continuous w) (him : ∀ t, (w t).im = 1) :
    Continuous (fun t => φ₀'' (-1 / w t)) := by
  have h_im := im_neg_inv_pos_of_im_one him
  have h_ne : ∀ t, w t ≠ 0 := fun t h => by
    have : (w t).im = 0 := by rw [h]; simp
    rw [him] at this; exact one_ne_zero this
  exact continuous_φ₀''_comp (Continuous.div continuous_const hw h_ne) h_im

/-- The integrand for I₂ over V × [0,1]. Uses the canonical Φ₂ from Basic.lean. -/
def I₂_integrand (p : V × ℝ) : ℂ := Φ₂ (‖p.1‖^2) p.2

/-- The integrand for I₄ over V × [0,1]. Uses the canonical Φ₄ from Basic.lean. -/
def I₄_integrand (p : V × ℝ) : ℂ := Φ₄ (‖p.1‖^2) p.2

/-- The I₂ integrand is continuous as a function V × ℝ → ℂ.
Follows from: continuity of φ₀''(-1/(t+I)), polynomial in t, and cexp compositions.

Note: We unfold through Φ₂ to the explicit formula and use z₂'_add_one_eq to relate
z₂' t + 1 to t + I (on [0,1]) or its IccExtend clamping (outside [0,1]). -/
lemma Φ₂_prod_continuous : Continuous I₂_integrand := by
  unfold I₂_integrand Φ₂ Φ₂'
  have hz : Continuous z₂' := continuous_z₂'
  -- Key: Im(z₂' t + 1) = 1 for all t (IccExtend clamps t to [0,1], where z₂ s = -1 + s + I)
  have him_one : ∀ t : ℝ, (z₂' t + 1).im = 1 := fun t => by
    simp only [add_im, one_im, add_zero, z₂', IccExtend, Function.comp_apply, z₂, neg_im, neg_zero,
      ofReal_im, I_im, zero_add]
  have h1 : Continuous (fun p : V × ℝ => φ₀'' (-1 / (z₂' p.2 + 1))) :=
    (continuous_φ₀''_neg_inv_im_one (hz.add continuous_const) him_one).comp continuous_snd
  have h2 : Continuous (fun p : V × ℝ => (z₂' p.2 + 1) ^ 2) :=
    ((hz.comp continuous_snd).add continuous_const).pow 2
  have h3 : Continuous (fun p : V × ℝ => cexp (π * I * ((‖p.1‖^2 : ℝ) : ℂ) * z₂' p.2)) :=
    continuous_cexp_norm_sq_mul_path hz
  exact (h1.mul h2).mul h3

/-- The norm of I₂_integrand is bounded by C * exp(-π‖x‖²) for all (x, t) ∈ V × [0,1].
Uses continuity of φ₀'' on [0,1] to get a uniform bound. -/
lemma Φ₂_prod_norm_bound : ∃ C > 0, ∀ x : V, ∀ t ∈ Icc (0 : ℝ) 1,
    ‖I₂_integrand (x, t)‖ ≤ C * Real.exp (-π * ‖x‖^2) := by
  -- Get a bound on |φ₀''(-1/(t+I))| for t ∈ [0,1] using continuity
  -- Since φ₀''(-1/(t+I)) is continuous on the compact set [0,1], it's bounded
  have h_bdd : BddAbove ((fun t : ℝ => ‖φ₀'' (-1 / (t + I))‖) '' Icc (0 : ℝ) 1) :=
    IsCompact.bddAbove_image isCompact_Icc
      (continuous_norm.comp continuous_φ₀''_I₂_param).continuousOn
  obtain ⟨M, hM_nonneg, hM_le⟩ := h_bdd.exists_ge (0 : ℝ)
  refine ⟨2 * (M + 1), by positivity, fun x t ht => ?_⟩
  -- Unfold I₂_integrand to Φ₂, then use z₂'_eq_of_mem for t ∈ [0,1]
  simp only [I₂_integrand, Φ₂, Φ₂', z₂'_eq_of_mem ht]
  -- Now goal is: ‖φ₀''(-1/((-1+t+I)+1)) * ((-1+t+I)+1)² * cexp(π*I*‖x‖²*(-1+t+I))‖ ≤ ...
  -- Simplify: -1 + t + I + 1 = t + I
  have h_simp : (-1 : ℂ) + ↑t + I + 1 = ↑t + I := by ring
  simp only [h_simp]
  rw [norm_mul, norm_mul]
  -- |φ₀''(-1/(t+I))| ≤ M
  have h_φ : ‖φ₀'' (-1 / (t + I))‖ ≤ M := by apply hM_le; exact ⟨t, ht, rfl⟩
  -- |(t + I)²| ≤ 2
  have h_sq : ‖(↑t + I) ^ 2‖ ≤ 2 := norm_sq_t_add_I_le t ht
  -- Exponential factor: cexp(π*I*r*(-1+t+I)) = exp(-πr) * phase
  have h_exp : ‖cexp (↑π * I * ↑(‖x‖ ^ 2) * (-1 + ↑t + I))‖ = Real.exp (-π * ‖x‖^2) := by
    have h_eq : (↑π * I * ↑(‖x‖ ^ 2) * (-1 + ↑t + I) : ℂ) =
        (π * ‖x‖^2 * (t - 1) : ℝ) * I + ↑(-π * ‖x‖^2) := by apply Complex.ext <;> simp <;> ring
    simp only [h_eq, Complex.exp_add, Complex.norm_mul, Complex.norm_exp_ofReal_mul_I,
      norm_exp_ofReal, one_mul]
  have h1 : ‖φ₀'' (-1 / (↑t + I))‖ * ‖(↑t + I) ^ 2‖ ≤ M * 2 := by
    calc ‖φ₀'' (-1 / (↑t + I))‖ * ‖(↑t + I) ^ 2‖
        ≤ M * ‖(↑t + I) ^ 2‖ := mul_le_mul_of_nonneg_right h_φ (norm_nonneg _)
      _ ≤ M * 2 := mul_le_mul_of_nonneg_left h_sq hM_nonneg
  calc ‖φ₀'' (-1 / (↑t + I))‖ * ‖(↑t + I) ^ 2‖ * ‖cexp (↑π * I * ↑(‖x‖ ^ 2) * (-1 + ↑t + I))‖
      = ‖φ₀'' (-1 / (↑t + I))‖ * ‖(↑t + I) ^ 2‖ * Real.exp (-π * ‖x‖^2) := by rw [h_exp]
    _ ≤ M * 2 * Real.exp (-π * ‖x‖^2) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ ≤ 2 * (M + 1) * Real.exp (-π * ‖x‖^2) := by nlinarith [Real.exp_pos (-π * ‖x‖^2), hM_nonneg]

/-- I₂ integrand is integrable on V × [0,1] (Class A segment).

Proof: Continuous, bounded by C * exp(-π‖x‖²), and Gaussian is integrable on V. -/
theorem Φ₂_prod_integrable :
    Integrable I₂_integrand (volume.prod (volume.restrict (Icc 0 1))) := by
  -- Use Integrable.mono' with dominating function C * exp(-π‖x‖²) ∘ fst
  obtain ⟨C, hC_pos, hC⟩ := Φ₂_prod_norm_bound
  -- The dominating function
  let g : V × ℝ → ℝ := fun p => C * Real.exp (-π * ‖p.1‖^2)
  -- Step 1: I₂_integrand is AEStronglyMeasurable (it's continuous)
  have h_meas : AEStronglyMeasurable I₂_integrand (volume.prod (volume.restrict (Icc 0 1))) :=
    Φ₂_prod_continuous.aestronglyMeasurable
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
  have h_bound : ∀ᵐ p ∂(volume.prod (volume.restrict (Icc 0 1))), ‖I₂_integrand p‖ ≤ g p := by
    rw [volume_prod_restrict_eq, ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Icc)]
    exact ae_of_all _ (fun ⟨x, t⟩ ⟨_, ht⟩ => hC x t ht)
  exact Integrable.mono' h_g_int h_meas h_bound

/-- The I₄ integrand is continuous as a function V × ℝ → ℂ.
Im(z₄' t) = 1 for all t (via IccExtend), so -1/(z₄' t - 1) has positive Im. -/
lemma Φ₄_prod_continuous : Continuous I₄_integrand := by
  unfold I₄_integrand Φ₄ Φ₄'
  have hz : Continuous z₄' := continuous_z₄'
  -- Key: Im(z₄' t - 1) = 1 for all t (IccExtend clamps t to [0,1], where z₄ s = 1 - s + I)
  have him_one : ∀ t : ℝ, (z₄' t - 1).im = 1 := fun t => by
    simp only [sub_im, one_im, sub_zero, z₄', IccExtend, Function.comp_apply, z₄, add_im, ofReal_im,
      I_im, zero_add]
  have h1 : Continuous (fun p : V × ℝ => φ₀'' (-1 / (z₄' p.2 - 1))) :=
    (continuous_φ₀''_neg_inv_im_one (hz.sub continuous_const) him_one).comp continuous_snd
  have h2 : Continuous (fun p : V × ℝ => (z₄' p.2 - 1) ^ 2) :=
    ((hz.comp continuous_snd).sub continuous_const).pow 2
  have h3 : Continuous (fun p : V × ℝ => cexp (π * I * ((‖p.1‖^2 : ℝ) : ℂ) * z₄' p.2)) :=
    continuous_cexp_norm_sq_mul_path hz
  exact (continuous_const.mul ((h1.mul h2).mul h3))

/-- The norm of I₄_integrand is bounded by C * exp(-π‖x‖²) for all (x, t) ∈ V × [0,1].
Uses z₄'_eq_of_mem to relate z₄' t to 1 - t + I for t ∈ [0,1]. -/
lemma Φ₄_prod_norm_bound : ∃ C > 0, ∀ x : V, ∀ t ∈ Icc (0 : ℝ) 1,
    ‖I₄_integrand (x, t)‖ ≤ C * Real.exp (-π * ‖x‖^2) := by
  have h_bdd : BddAbove ((fun t : ℝ => ‖φ₀'' (-1 / (-t + I))‖) '' Icc (0 : ℝ) 1) :=
    IsCompact.bddAbove_image isCompact_Icc
      (continuous_norm.comp continuous_φ₀''_I₄_param).continuousOn
  obtain ⟨M, hM_nonneg, hM_le⟩ := h_bdd.exists_ge (0 : ℝ)
  refine ⟨2 * (M + 1), by positivity, fun x t ht => ?_⟩
  -- Unfold I₄_integrand through Φ₄ and use z₄'_eq_of_mem for t ∈ [0,1]
  simp only [I₄_integrand, Φ₄, Φ₄', z₄'_eq_of_mem ht]
  -- Now goal involves z₄' t = 1 - t + I, so z₄' t - 1 = -t + I
  have h_simp : (1 : ℂ) - ↑t + I - 1 = -↑t + I := by ring
  simp only [h_simp]
  rw [norm_mul, norm_mul, norm_mul]
  have h_neg1 : ‖(-1 : ℂ)‖ = 1 := by simp
  have h_φ : ‖φ₀'' (-1 / (-t + I))‖ ≤ M := by apply hM_le; exact ⟨t, ht, rfl⟩
  have h_sq : ‖(-↑t + I) ^ 2‖ ≤ 2 := norm_sq_neg_t_add_I_le t ht
  -- Exponential factor: cexp(π*I*r*(1-t+I)) = exp(-πr) * phase
  have h_exp : ‖cexp (↑π * I * ↑(‖x‖ ^ 2) * (1 - ↑t + I))‖ = Real.exp (-π * ‖x‖^2) := by
    have h_eq : (↑π * I * ↑(‖x‖ ^ 2) * (1 - ↑t + I) : ℂ) =
        (π * ‖x‖^2 * (1 - t) : ℝ) * I + ↑(-π * ‖x‖^2) := by apply Complex.ext <;> simp <;> ring
    simp only [h_eq, Complex.exp_add, Complex.norm_mul, Complex.norm_exp_ofReal_mul_I,
      norm_exp_ofReal, one_mul]
  have h1 : ‖φ₀'' (-1 / (-↑t + I))‖ * ‖(-↑t + I) ^ 2‖ ≤ M * 2 := by
    calc ‖φ₀'' (-1 / (-↑t + I))‖ * ‖(-↑t + I) ^ 2‖
        ≤ M * ‖(-↑t + I) ^ 2‖ := mul_le_mul_of_nonneg_right h_φ (norm_nonneg _)
      _ ≤ M * 2 := mul_le_mul_of_nonneg_left h_sq hM_nonneg
  calc ‖(-1 : ℂ)‖ * (‖φ₀'' (-1 / (-↑t + I))‖ * ‖(-↑t + I) ^ 2‖ *
          ‖cexp (↑π * I * ↑(‖x‖ ^ 2) * (1 - ↑t + I))‖)
      = 1 * (‖φ₀'' (-1 / (-↑t + I))‖ * ‖(-↑t + I) ^ 2‖ * Real.exp (-π * ‖x‖^2)) := by
        rw [h_neg1, h_exp]
    _ = ‖φ₀'' (-1 / (-↑t + I))‖ * ‖(-↑t + I) ^ 2‖ * Real.exp (-π * ‖x‖^2) := by ring
    _ ≤ M * 2 * Real.exp (-π * ‖x‖^2) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ ≤ 2 * (M + 1) * Real.exp (-π * ‖x‖^2) := by nlinarith [Real.exp_pos (-π * ‖x‖^2), hM_nonneg]

/-- I₄ integrand is integrable on V × [0,1] (Class A segment).
Strategy: Same as I₂ - φ₀'' bounded via Im ≥ 1/2, Gaussian decay dominates. -/
theorem Φ₄_prod_integrable :
    Integrable I₄_integrand (volume.prod (volume.restrict (Icc 0 1))) := by
  obtain ⟨C, hC_pos, hC⟩ := Φ₄_prod_norm_bound
  let g : V × ℝ → ℝ := fun p => C * Real.exp (-π * ‖p.1‖^2)
  have h_meas : AEStronglyMeasurable I₄_integrand (volume.prod (volume.restrict (Icc 0 1))) :=
    Φ₄_prod_continuous.aestronglyMeasurable
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
    rw [volume_prod_restrict_eq, ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Icc)]
    exact ae_of_all _ (fun ⟨x, t⟩ ⟨_, ht⟩ => hC x t ht)
  exact Integrable.mono' h_g_int h_meas h_bound

end HorizontalSegments

/-! ## Imaginary Ray (I₆)

For I₆, we integrate over t ∈ [1,∞) with z = it on the positive imaginary axis.
Since Im(z) = t ≥ 1, `norm_φ₀_le` gives `|φ₀(z)| ≤ C₀·e^{-2πt}`.
-/

section ImaginaryRay

/-- The integrand for I₆ over V × [1,∞). Uses the canonical Φ₆ from Basic.lean. -/
def I₆_integrand (p : V × ℝ) : ℂ := Φ₆ (‖p.1‖^2) p.2

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
lemma Φ₆_prod_continuousOn :
    ContinuousOn I₆_integrand (Set.univ ×ˢ Set.Ici (1 : ℝ)) := by
  unfold I₆_integrand Φ₆ Φ₆'
  -- After unfolding: fun p => I * (φ₀'' (z₆' p.2) * cexp (π * I * (‖p.1‖^2) * z₆' p.2))
  -- Since z₆' t = I * t for t ≥ 1, and I² = -1, the exp becomes cexp (-π * ‖p.1‖^2 * t)
  -- φ₀''(z₆' t) = φ₀''(I * t) is ContinuousOn via continuousOn_φ₀''_I₆_param
  have h1 : ContinuousOn (fun p : V × ℝ => φ₀'' (z₆' p.2)) (Set.univ ×ˢ Set.Ici 1) := by
    -- For t ≥ 1, z₆' t = I * t by IciExtend
    have h_eq : ∀ t ∈ Set.Ici (1 : ℝ), z₆' t = I * t := fun t ht =>
      by rw [z₆', IciExtend_of_mem z₆ ht, z₆]
    have h : ContinuousOn (fun t : ℝ => φ₀'' (z₆' t)) (Set.Ici 1) := by
      refine continuousOn_φ₀''_I₆_param.congr ?_
      intro t ht
      exact congrArg φ₀'' (h_eq t ht)
    exact h.comp continuous_snd.continuousOn (fun ⟨_, t⟩ ht => ht.2)
  have h3 : Continuous (fun p : V × ℝ => cexp (π * I * ((‖p.1‖^2 : ℝ) : ℂ) * z₆' p.2)) :=
    continuous_cexp_norm_sq_mul_path continuous_z₆'
  exact (continuous_const.continuousOn.mul (h1.mul h3.continuousOn))

/-- The norm of I₆_integrand is bounded by C * exp(-2πt) * exp(-π‖x‖²) for t ≥ 1. -/
lemma Φ₆_prod_norm_bound : ∃ C > 0, ∀ x : V, ∀ t : ℝ, 1 ≤ t →
    ‖I₆_integrand (x, t)‖ ≤ C * Real.exp (-2 * π * t) * Real.exp (-π * ‖x‖^2) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀''_I₆_bound
  refine ⟨C₀, hC₀_pos, fun x t ht => ?_⟩
  unfold I₆_integrand Φ₆ Φ₆'
  -- Convert z₆' t to I * t for t ≥ 1
  have hz₆ : z₆' t = I * t := z₆'_eq_of_mem ht
  -- Simplify the exponential: π * I * r * (I * t) = -π * r * t
  have h_exp_eq : π * I * ((‖x‖^2 : ℝ) : ℂ) * (I * t) = -π * ‖x‖^2 * t := by
    have h_I_sq : (I : ℂ) ^ 2 = -1 := I_sq
    ring_nf
    rw [h_I_sq]
    simp only [ofReal_pow]
    ring
  simp only [hz₆, h_exp_eq, norm_mul]
  have h_I : ‖(I : ℂ)‖ = 1 := Complex.norm_I
  have h_φ : ‖φ₀'' (I * t)‖ ≤ C₀ * Real.exp (-2 * π * t) := hC₀ t ht
  have h_gauss_norm := norm_cexp_neg_pi_norm_sq_mul x t
  have h_gauss_le : Real.exp (-π * ‖x‖^2 * t) ≤ Real.exp (-π * ‖x‖^2) := by
    apply Real.exp_le_exp.mpr
    have h1 : -π * ‖x‖^2 * t ≤ -π * ‖x‖^2 * 1 := by
      have hpi : -π * ‖x‖^2 ≤ 0 := by nlinarith [Real.pi_pos, sq_nonneg ‖x‖]
      nlinarith
    linarith
  calc ‖(I : ℂ)‖ * (‖φ₀'' (I * t)‖ * ‖cexp (-π * ‖x‖^2 * t)‖)
      = 1 * (‖φ₀'' (I * t)‖ * Real.exp (-π * ‖x‖^2 * t)) := by rw [h_I, h_gauss_norm]
    _ ≤ 1 * (C₀ * Real.exp (-2 * π * t) * Real.exp (-π * ‖x‖^2)) := by gcongr
    _ = C₀ * Real.exp (-2 * π * t) * Real.exp (-π * ‖x‖^2) := by ring

/-- I₆ integrand is integrable on V × [1,∞) (Class C tail).
Strategy: φ₀ decay (Cor 7.5) + domination `e^{-πrt} ≤ e^{-πr}` for t ≥ 1. -/
theorem Φ₆_prod_integrable :
    Integrable I₆_integrand (volume.prod (volume.restrict (Ici 1))) := by
  obtain ⟨C, hC_pos, hC⟩ := Φ₆_prod_norm_bound
  -- Dominating function: C * exp(-2πt) * exp(-π‖x‖²) = (C * exp(-π‖x‖²)) * exp(-2πt)
  let g : V × ℝ → ℝ := fun p => C * Real.exp (-2 * π * p.2) * Real.exp (-π * ‖p.1‖^2)
  -- Use ContinuousOn.aestronglyMeasurable with the restricted measure
  have h_meas : AEStronglyMeasurable I₆_integrand (volume.prod (volume.restrict (Ici 1))) := by
    have hmeas' : AEStronglyMeasurable I₆_integrand
        ((volume.prod volume).restrict (Set.univ ×ˢ Set.Ici (1 : ℝ))) :=
      Φ₆_prod_continuousOn.aestronglyMeasurable
        (MeasurableSet.univ.prod measurableSet_Ici)
    rw [volume_prod_restrict_eq]
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
    have h_t : Integrable (fun t : ℝ => Real.exp (-2 * π * t)) (volume.restrict (Ici 1)) :=
      integrableOn_exp_mul_Ici (-2 * π) (by linarith [Real.pi_pos])
    -- Product of integrable functions
    exact Integrable.mul_prod h_x h_t
  -- The bound holds a.e. (it actually holds everywhere on the support)
  have h_bound : ∀ᵐ p ∂(volume.prod (volume.restrict (Ici 1))), ‖I₆_integrand p‖ ≤ g p := by
    rw [volume_prod_restrict_eq, ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Ici)]
    exact ae_of_all _ fun ⟨x, t⟩ ⟨_, ht⟩ => hC x t ht
  exact Integrable.mono' h_g_int h_meas h_bound

end ImaginaryRay

/-! ## Cusp-Approaching Segments (I₁, I₃, I₅)

For I₁, I₃, I₅ we integrate over (0,1] with z = -1/(it), where Im(z) = 1/t → ∞ as t → 0.
The exponential decay exp(-2π/t) dominates any polynomial singularity at t = 0.
-/

section CuspApproachingSegments

/-- φ₀'' bound for cusp-approaching segments: for t ∈ (0, 1], ‖φ₀''(-1/(It))‖ ≤ C₀ * exp(-2π/t) -/
lemma norm_φ₀''_cusp_bound : ∃ C₀ > 0, ∀ t : ℝ, 0 < t → t ≤ 1 →
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

/-- Exponential simplification: cexp(π*I*r*(I*t)) = cexp(-π*r*t) since I² = -1. -/
lemma cexp_pi_I_mul_I (r t : ℂ) : cexp (π * I * r * (I * t)) = cexp (-π * r * t) := by
  congr 1
  calc π * I * r * (I * t) = π * (I * I) * r * t := by ring
    _ = -π * r * t := by rw [I_mul_I]; ring

/-- (I * t)² = -t² -/
lemma I_mul_sq (t : ℂ) : (I * t) ^ 2 = -t ^ 2 := by rw [mul_pow, I_sq]; ring

/-- The integrand for I₁ over V × (0,1]. Uses the canonical Φ₁ from Basic.lean. -/
def I₁_integrand (p : V × ℝ) : ℂ := Φ₁ (‖p.1‖^2) p.2

/-- The integrand for I₃ over V × (0,1]. Uses the canonical Φ₃ from Basic.lean. -/
def I₃_integrand (p : V × ℝ) : ℂ := Φ₃ (‖p.1‖^2) p.2

/-- The integrand for I₅ over V × (0,1]. Uses the canonical Φ₅ from Basic.lean. -/
def I₅_integrand (p : V × ℝ) : ℂ := Φ₅ (‖p.1‖^2) p.2

/-- I₁ integrand equals I₅ integrand times a unit-modulus phase factor (on the domain).

The key insight is that z₁' t + 1 = I*t = z₅' t, so the φ₀'' and z² factors
are identical, and only the exponential differs by the phase cexp(-πIr). -/
lemma Φ₁_prod_eq_Φ₅_mul_phase {p : V × ℝ} (ht : p.2 ∈ Icc 0 1) :
    I₁_integrand p = I₅_integrand p * cexp (-π * I * ‖p.1‖^2) := by
  simp only [I₁_integrand, I₅_integrand, Φ₁, Φ₅, Φ₁', Φ₅', z₁'_eq_of_mem ht, z₅'_eq_of_mem ht]
  have h_add : (-1 : ℂ) + I * ↑p.2 + 1 = I * ↑p.2 := by ring
  rw [h_add]
  -- cexp(π*I*r*(-1 + I*t)) = cexp(-π*I*r) * cexp(-π*r*t)
  have h_exp1 : cexp (↑π * I * ↑(‖p.1‖^2) * (-1 + I * ↑p.2)) =
      cexp (-↑π * I * ↑(‖p.1‖^2)) * cexp (-↑π * ↑(‖p.1‖^2) * ↑p.2) := by
    rw [← Complex.exp_add]; congr 1
    calc _ = -↑π * I * ↑(‖p.1‖^2) + ↑π * (I * I) * ↑(‖p.1‖^2) * ↑p.2 := by ring
      _ = _ := by rw [I_mul_I]; ring
  have h_exp5 : cexp (↑π * I * ↑(‖p.1‖^2) * (I * ↑p.2)) = cexp (-↑π * ↑(‖p.1‖^2) * ↑p.2) :=
    cexp_pi_I_mul_I ↑(‖p.1‖^2) ↑p.2
  rw [h_exp1, h_exp5]; ring_nf; simp only [ofReal_pow]; rw [mul_right_comm]

/-- I₃ integrand equals I₅ integrand times a unit-modulus phase factor (on the domain).

The key insight is that z₃' t - 1 = I*t = z₅' t, so the φ₀'' and z² factors
are identical, and only the exponential differs by the phase cexp(πIr). -/
lemma Φ₃_prod_eq_Φ₅_mul_phase {p : V × ℝ} (ht : p.2 ∈ Icc 0 1) :
    I₃_integrand p = I₅_integrand p * cexp (π * I * ‖p.1‖^2) := by
  simp only [I₃_integrand, I₅_integrand, Φ₃, Φ₅, Φ₃', Φ₅', z₃'_eq_of_mem ht, z₅'_eq_of_mem ht]
  have h_sub : (1 : ℂ) + I * ↑p.2 - 1 = I * ↑p.2 := by ring
  rw [h_sub]
  -- cexp(π*I*r*(1 + I*t)) = cexp(π*I*r) * cexp(-π*r*t)
  have h_exp3 : cexp (↑π * I * ↑(‖p.1‖^2) * (1 + I * ↑p.2)) =
      cexp (↑π * I * ↑(‖p.1‖^2)) * cexp (-↑π * ↑(‖p.1‖^2) * ↑p.2) := by
    rw [← Complex.exp_add]; congr 1
    calc _ = ↑π * I * ↑(‖p.1‖^2) + ↑π * (I * I) * ↑(‖p.1‖^2) * ↑p.2 := by ring
      _ = _ := by rw [I_mul_I]; ring
  have h_exp5 : cexp (↑π * I * ↑(‖p.1‖^2) * (I * ↑p.2)) = cexp (-↑π * ↑(‖p.1‖^2) * ↑p.2) :=
    cexp_pi_I_mul_I ↑(‖p.1‖^2) ↑p.2
  rw [h_exp3, h_exp5]; ring_nf; simp only [ofReal_pow]
  rw [mul_right_comm]

/-- The phase factor cexp(-πI‖x‖²) has unit modulus. -/
lemma norm_phase_factor_I₁ (x : V) : ‖cexp (-π * I * ‖x‖^2)‖ = 1 := by
  rw [show (-π * I * ‖x‖^2 : ℂ) = ↑(-π * ‖x‖^2) * I from by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The phase factor cexp(πI‖x‖²) has unit modulus. -/
lemma norm_phase_factor_I₃ (x : V) : ‖cexp (π * I * ‖x‖^2)‖ = 1 := by
  rw [show (π * I * ‖x‖^2 : ℂ) = ↑(π * ‖x‖^2) * I from by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _
/-- The I₅ integrand is continuous on V × (0, 1]. -/
lemma Φ₅_prod_continuousOn : ContinuousOn I₅_integrand (Set.univ ×ˢ Set.Ioc 0 1) := by
  unfold I₅_integrand Φ₅ Φ₅'
  have hz₅ : Continuous z₅' := by
    unfold z₅' z₅; simp only [IccExtend, Function.comp_apply]
    exact continuous_const.mul
      (continuous_ofReal.comp (continuous_subtype_val.comp continuous_projIcc))
  have h1 : ContinuousOn (fun p : V × ℝ => φ₀'' (-1 / z₅' p.2)) (Set.univ ×ˢ Set.Ioc 0 1) := by
    have h_eq : ∀ p : V × ℝ, p ∈ Set.univ ×ˢ Set.Ioc 0 1 →
        φ₀'' (-1 / z₅' p.2) = φ₀'' (-1 / (I * p.2)) := fun ⟨_, t⟩ ht => by
      simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioc, true_and] at ht
      rw [z₅'_eq_of_mem (mem_Icc_of_Ioc ht)]
    exact (continuousOn_φ₀''_cusp_path.comp continuous_snd.continuousOn
      (fun ⟨_, t⟩ ht => by simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioc, true_and,
                                     Set.mem_Ioi] at ht ⊢; exact ht.1)).congr h_eq
  have h2 : Continuous (fun p : V × ℝ => (z₅' p.2) ^ 2) := (hz₅.comp continuous_snd).pow 2
  have h3 : Continuous (fun p : V × ℝ => cexp (π * I * ↑(‖p.1‖^2) * z₅' p.2)) :=
    continuous_cexp_norm_sq_mul_path hz₅
  exact continuousOn_const.mul ((h1.mul h2.continuousOn).mul h3.continuousOn)

/-- I₅ integrand norm bound for Class B. -/
lemma Φ₅_prod_norm_bound : ∃ C > 0, ∀ x : V, ∀ t : ℝ, 0 < t → t ≤ 1 →
    ‖I₅_integrand (x, t)‖ ≤ C * Real.exp (-2 * π / t) * t ^ 2 * Real.exp (-π * ‖x‖^2 * t) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀''_cusp_bound
  refine ⟨C₀, hC₀_pos, fun x t ht ht' => ?_⟩
  simp only [I₅_integrand, Φ₅, Φ₅', z₅'_eq_of_mem ⟨le_of_lt ht, ht'⟩, I_mul_sq, cexp_pi_I_mul_I,
    neg_mul, mul_neg, norm_neg, norm_mul, Complex.norm_I, one_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  -- Simplify Gaussian norm
  have h_gauss : ‖cexp (-(↑π * ↑(‖x‖^2) * ↑t))‖ = Real.exp (-π * ‖x‖^2 * t) := by
    simp only [← ofReal_neg, ← ofReal_mul, norm_exp_ofReal]; ring_nf
  rw [h_gauss, show -(π * ‖x‖^2 * t) = -π * ‖x‖^2 * t by ring,
    show -(2 * π) / t = -2 * π / t by ring]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC₀ t ht ht') (sq_nonneg t))
    (Real.exp_pos _).le

/-- For fixed t, the x-slice of I₅_integrand is continuous.
I₅_integrand (x, t) = I * (φ₀''(-1/(z₅' t)) * (z₅' t)² * cexp(π*I*‖x‖²*(z₅' t)))
The only x-dependence is in the exponential argument ‖x‖², which is continuous. -/
lemma Φ₅_slice_continuous (t : ℝ) : Continuous (fun x : V => I₅_integrand (x, t)) := by
  simp only [I₅_integrand, Φ₅, Φ₅']
  apply Continuous.mul
  · exact continuous_const  -- I
  · apply Continuous.mul
    · exact continuous_const  -- φ₀''(-1/(z₅' t)) * (z₅' t)^2
    · apply Complex.continuous_exp.comp
      refine (Continuous.mul ?_ continuous_const)
      refine (Continuous.mul ?_ ?_)
      · exact continuous_const  -- π * I
      · exact continuous_ofReal.comp ((continuous_norm).pow 2)

/-- I₅ integrand is integrable on V × (0,1] (Class B segment).

Route A strategy:
1. Bound: ‖I₅_integrand(x,t)‖ ≤ C * exp(-2π/t) * t² * exp(-π‖x‖²t)
2. Integrate in x first: ∫_V exp(-πt‖x‖²) dx = t^{-4} (Gaussian in 8D)
3. Then t-integral: ∫₀¹ C * exp(-2π/t) * t^{-2} dt converges

The super-exponential decay of exp(-2π/t) as t→0 dominates the polynomial t^{-2}. -/
theorem Φ₅_prod_integrable :
    Integrable I₅_integrand (volume.prod (volume.restrict (Ioc 0 1))) := by
  -- Get the pointwise bound constant C from Φ₅_prod_norm_bound
  obtain ⟨C, hC_pos, hC_bound⟩ := Φ₅_prod_norm_bound
  -- AEStronglyMeasurable is needed for integrable_prod_iff'
  have h_meas : AEStronglyMeasurable I₅_integrand
      (volume.prod (volume.restrict (Ioc 0 1))) := by
    -- Use ContinuousOn.aestronglyMeasurable with the restricted measure
    have hmeas' : AEStronglyMeasurable I₅_integrand
        ((volume.prod volume).restrict (Set.univ ×ˢ Set.Ioc (0 : ℝ) 1)) :=
      Φ₅_prod_continuousOn.aestronglyMeasurable
        (MeasurableSet.univ.prod measurableSet_Ioc)
    rw [volume_prod_restrict_eq]
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
    · exact (Φ₅_slice_continuous t).aestronglyMeasurable
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
        · exact (continuous_norm.comp (Φ₅_slice_continuous t)).aestronglyMeasurable
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
        _ ≤ C * Real.exp (-2 * π) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC_pos)
            have := exp_neg_div_mul_inv_sq_le (2 * π) t (by linarith [Real.two_le_pi]) ht.1 ht.2
            convert this using 2 <;> ring_nf

/-- I₁ integrand is integrable on V × (0,1] (Class B segment).
Follows from I₅ integrability since I₁ = I₅ * (unit-modulus phase). -/
theorem Φ₁_prod_integrable :
    Integrable I₁_integrand (volume.prod (volume.restrict (Ioc 0 1))) := by
  -- On the domain (univ ×ˢ Ioc 0 1), I₁_integrand = I₅_integrand * phase
  have h_eq : ∀ p : V × ℝ, p.2 ∈ Ioc 0 1 →
      I₁_integrand p = I₅_integrand p * cexp (-π * I * ‖p.1‖^2) := fun p ht =>
    Φ₁_prod_eq_Φ₅_mul_phase (mem_Icc_of_Ioc ht)
  -- Use congr to transfer integrability
  have h_I₅ := Φ₅_prod_integrable
  rw [volume_prod_restrict_eq]
  have h_integrable : Integrable (fun p => I₅_integrand p * cexp (-π * I * (‖p.1‖^2 : ℂ)))
      ((volume.prod volume).restrict (Set.univ ×ˢ Ioc 0 1)) := by
    rw [← volume_prod_restrict_eq]
    apply Integrable.mono' h_I₅.norm
    · have h_cont : Continuous (fun p : V × ℝ => cexp (-π * I * ‖p.1‖^2)) := by fun_prop
      exact h_I₅.aestronglyMeasurable.mul h_cont.aestronglyMeasurable
    · apply ae_of_all; intro p
      rw [norm_mul, norm_phase_factor_I₁ p.1, mul_one]
  refine h_integrable.congr ?_
  -- Show f =ᶠ[ae μ] g by showing equality on the support set
  refine Filter.eventually_of_mem
    (self_mem_ae_restrict (MeasurableSet.univ.prod measurableSet_Ioc)) ?_
  intro ⟨x, t⟩ ⟨_, ht⟩
  exact (h_eq (x, t) ht).symm

/-- I₃ integrand is integrable on V × (0,1] (Class B segment).
Follows from I₅ integrability since I₃ = I₅ * (unit-modulus phase). -/
theorem Φ₃_prod_integrable :
    Integrable I₃_integrand (volume.prod (volume.restrict (Ioc 0 1))) := by
  -- On the domain (univ ×ˢ Ioc 0 1), I₃_integrand = I₅_integrand * phase
  have h_eq : ∀ p : V × ℝ, p.2 ∈ Ioc 0 1 →
      I₃_integrand p = I₅_integrand p * cexp (π * I * ‖p.1‖^2) := fun p ht =>
    Φ₃_prod_eq_Φ₅_mul_phase (mem_Icc_of_Ioc ht)
  have h_I₅ := Φ₅_prod_integrable
  rw [volume_prod_restrict_eq]
  have h_integrable : Integrable (fun p => I₅_integrand p * cexp (π * I * (‖p.1‖^2 : ℂ)))
      ((volume.prod volume).restrict (Set.univ ×ˢ Ioc 0 1)) := by
    rw [← volume_prod_restrict_eq]
    apply Integrable.mono' h_I₅.norm
    · have h_cont : Continuous (fun p : V × ℝ => cexp (π * I * ‖p.1‖^2)) := by fun_prop
      exact h_I₅.aestronglyMeasurable.mul h_cont.aestronglyMeasurable
    · apply ae_of_all; intro p
      rw [norm_mul, norm_phase_factor_I₃ p.1, mul_one]
  refine h_integrable.congr ?_
  -- Show f =ᶠ[ae μ] g by showing equality on the support set
  refine Filter.eventually_of_mem
    (self_mem_ae_restrict (MeasurableSet.univ.prod measurableSet_Ioc)) ?_
  intro ⟨x, t⟩ ⟨_, ht⟩
  exact (h_eq (x, t) ht).symm

end CuspApproachingSegments

/-! ## Fubini Swap Lemmas

Once we have product integrability, Fubini's theorem allows swapping
the order of integration: ∫_{ℝ⁸} ∫_{contour} = ∫_{contour} ∫_{ℝ⁸}.
-/

section FubiniSwap

/-- Connection: I₁ x = ∫ t, I₁_integrand (x, t) -/
lemma I₁_eq_integral (x : V) :
    I₁ x = ∫ t in Ioc (0 : ℝ) 1, I₁_integrand (x, t) := by
  rw [I₁, I₁'_eq_Ioc]
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Ioc
  refine ae_of_all _ fun t ht => ?_
  simp only [I₁_integrand, Φ₁, Φ₁', z₁'_eq_of_mem (mem_Icc_of_Ioc ht), ofReal_pow]
  have h_exp : ∀ r : ℂ, cexp (↑π * I * r * (-1 + I * ↑t)) =
      cexp (-↑π * I * r) * cexp (-↑π * r * ↑t) := fun r => by
    rw [← Complex.exp_add]; congr 1
    rw [show ↑π * I * r * (-1 + I * ↑t) = -↑π * I * r + ↑π * (I * I) * r * ↑t by ring, I_mul_I]
    ring
  simp only [show (-1 : ℂ) + I * ↑t + 1 = I * ↑t by ring, I_mul_sq, h_exp]
  ring

/-- Connection: I₂ x = ∫ t, I₂_integrand (x, t) over [0,1].
Note: Uses Icc because the integrand is continuous (no singularity at 0). -/
lemma I₂_eq_integral (x : V) :
    I₂ x = ∫ t in Icc (0 : ℝ) 1, I₂_integrand (x, t) := by
  rw [I₂, I₂'_eq]
  rw [intervalIntegral_eq_integral_uIoc, if_pos (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), one_smul]
  rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Icc
  refine ae_of_all _ fun t ht => ?_
  simp only [I₂_integrand, Φ₂, Φ₂', z₂'_eq_of_mem ht, ofReal_pow]
  -- z₂' t + 1 = -1 + t + I + 1 = t + I
  have h_add : (-1 : ℂ) + ↑t + I + 1 = ↑t + I := by ring
  -- cexp(π*I*r*(-1 + t + I)) = cexp(-π*I*r) * cexp(π*I*r*t) * cexp(-π*r)
  have h_exp : ∀ r : ℂ, cexp (↑π * I * r * (-1 + ↑t + I)) =
      cexp (-↑π * I * r) * cexp (↑π * I * r * ↑t) * cexp (-↑π * r) := fun r => by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1
    calc ↑π * I * r * (-1 + ↑t + I)
        = -↑π * I * r + ↑π * I * r * ↑t + ↑π * (I * I) * r := by ring
      _ = -↑π * I * r + ↑π * I * r * ↑t + ↑π * (-1) * r := by rw [I_mul_I]
      _ = -↑π * I * r + ↑π * I * r * ↑t + -↑π * r := by ring
  simp only [h_add, h_exp]
  ring

/-- Connection: I₃ x = ∫ t, I₃_integrand (x, t) -/
lemma I₃_eq_integral (x : V) :
    I₃ x = ∫ t in Ioc (0 : ℝ) 1, I₃_integrand (x, t) := by
  rw [I₃, I₃'_eq_Ioc]
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Ioc
  refine ae_of_all _ fun t ht => ?_
  simp only [I₃_integrand, Φ₃, Φ₃', z₃'_eq_of_mem (mem_Icc_of_Ioc ht), ofReal_pow]
  have h_exp : ∀ r : ℂ, cexp (↑π * I * r * (1 + I * ↑t)) =
      cexp (↑π * I * r) * cexp (-↑π * r * ↑t) := fun r => by
    rw [← Complex.exp_add]; congr 1
    rw [show ↑π * I * r * (1 + I * ↑t) = ↑π * I * r + ↑π * (I * I) * r * ↑t by ring, I_mul_I]
    ring
  simp only [show (1 : ℂ) + I * ↑t - 1 = I * ↑t by ring, I_mul_sq, h_exp]
  ring

/-- Connection: I₄ x = ∫ t, I₄_integrand (x, t) over [0,1].
Note: Uses Icc because the integrand is continuous (no singularity at 0). -/
lemma I₄_eq_integral (x : V) :
    I₄ x = ∫ t in Icc (0 : ℝ) 1, I₄_integrand (x, t) := by
  rw [I₄, I₄'_eq]
  rw [intervalIntegral_eq_integral_uIoc, if_pos (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), one_smul]
  rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Icc
  refine ae_of_all _ fun t ht => ?_
  simp only [I₄_integrand, Φ₄, Φ₄', z₄'_eq_of_mem ht, ofReal_pow]
  -- z₄' t - 1 = 1 - t + I - 1 = -t + I
  have h_sub : (1 : ℂ) - ↑t + I - 1 = -↑t + I := by ring
  -- cexp(π*I*r*(1 - t + I)) = cexp(π*I*r) * cexp(-π*I*r*t) * cexp(-π*r)
  have h_exp : ∀ r : ℂ, cexp (↑π * I * r * (1 - ↑t + I)) =
      cexp (↑π * I * r) * cexp (-↑π * I * r * ↑t) * cexp (-↑π * r) := fun r => by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1
    calc ↑π * I * r * (1 - ↑t + I)
        = ↑π * I * r - ↑π * I * r * ↑t + ↑π * (I * I) * r := by ring
      _ = ↑π * I * r - ↑π * I * r * ↑t + ↑π * (-1) * r := by rw [I_mul_I]
      _ = ↑π * I * r + -↑π * I * r * ↑t + -↑π * r := by ring
  simp only [h_sub, h_exp]
  ring

/-- Connection: I₅ x = -2 * ∫ t, I₅_integrand (x, t) -/
lemma I₅_eq_integral (x : V) :
    I₅ x = -2 * ∫ t in Ioc (0 : ℝ) 1, I₅_integrand (x, t) := by
  rw [I₅, I₅'_eq_Ioc]
  congr 1
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Ioc
  refine ae_of_all _ fun t ht => ?_
  simp only [I₅_integrand, Φ₅, Φ₅', z₅'_eq_of_mem (mem_Icc_of_Ioc ht), ofReal_pow, I_mul_sq,
    cexp_pi_I_mul_I]
  ring

/-- Connection: I₆ x = 2 * ∫ t, I₆_integrand (x, t) -/
lemma I₆_eq_integral (x : V) :
    I₆ x = 2 * ∫ t in Ici (1 : ℝ), I₆_integrand (x, t) := by
  rw [I₆, I₆'_eq]
  congr 1
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Ici
  refine ae_of_all _ fun t ht => ?_
  simp only [I₆_integrand, Φ₆, Φ₆', z₆'_eq_of_mem ht, ofReal_pow, cexp_pi_I_mul_I]
  ring

/-- Fubini for I₁: swap ∫_{ℝ⁸} and ∫_{(0,1]} -/
theorem I₁_integral_swap :
    ∫ x : V, I₁ x = ∫ t in Ioc (0 : ℝ) 1, ∫ x : V, I₁_integrand (x, t) := by
  simp_rw [I₁_eq_integral]
  exact MeasureTheory.integral_integral_swap Φ₁_prod_integrable

/-- Fubini for I₂: swap ∫_{ℝ⁸} and ∫_{[0,1]} -/
theorem I₂_integral_swap :
    ∫ x : V, I₂ x = ∫ t in Icc (0 : ℝ) 1, ∫ x : V, I₂_integrand (x, t) := by
  simp_rw [I₂_eq_integral]
  exact MeasureTheory.integral_integral_swap Φ₂_prod_integrable

/-- Fubini for I₃: swap ∫_{ℝ⁸} and ∫_{(0,1]} -/
theorem I₃_integral_swap :
    ∫ x : V, I₃ x = ∫ t in Ioc (0 : ℝ) 1, ∫ x : V, I₃_integrand (x, t) := by
  simp_rw [I₃_eq_integral]
  exact MeasureTheory.integral_integral_swap Φ₃_prod_integrable

/-- Fubini for I₄: swap ∫_{ℝ⁸} and ∫_{[0,1]} -/
theorem I₄_integral_swap :
    ∫ x : V, I₄ x = ∫ t in Icc (0 : ℝ) 1, ∫ x : V, I₄_integrand (x, t) := by
  simp_rw [I₄_eq_integral]
  exact MeasureTheory.integral_integral_swap Φ₄_prod_integrable

/-- Fubini for I₅: swap ∫_{ℝ⁸} and ∫_{(0,1]}
Note: includes factor of -2 from I₅ definition. -/
theorem I₅_integral_swap :
    ∫ x : V, I₅ x = -2 * ∫ t in Ioc (0 : ℝ) 1, ∫ x : V, I₅_integrand (x, t) := by
  simp_rw [I₅_eq_integral]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact MeasureTheory.integral_integral_swap Φ₅_prod_integrable

/-- Fubini for I₆: swap ∫_{ℝ⁸} and ∫_{[1,∞)}
Note: includes factor of 2 from I₆ definition. -/
theorem I₆_integral_swap :
    ∫ x : V, I₆ x = 2 * ∫ t in Ici (1 : ℝ), ∫ x : V, I₆_integrand (x, t) := by
  simp_rw [I₆_eq_integral]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact MeasureTheory.integral_integral_swap Φ₆_prod_integrable

end FubiniSwap

/-! ## Basic Integrability

Each Iⱼ is integrable over ℝ⁸ (from Schwartz structure).
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
  simpa [a_eq] using ((((I₁_integrable.add I₂_integrable).add I₃_integrable).add I₄_integrable).add
    I₅_integrable).add I₆_integrable

end BasicIntegrability

end

