/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module


public import SpherePacking.MagicFunction.a.Integrability.CuspPath
public import SpherePacking.MagicFunction.a.IntegralEstimates.Majorants
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fubini for the Contour Integrals `Iⱼ`

Each `Iⱼ : ℝ⁸ → ℂ` is a contour integral in a real parameter `t`, so computing its Fourier
transform means exchanging `∫_{ℝ⁸}` with `∫_{segment}`. This file supplies the product
integrability that licenses the exchange, and the resulting swap lemmas.

The integrands are packaged as functions on `ℝ⁸ × ℝ`, and product integrability is proved by
contour class, reusing the pointwise estimates from
`MagicFunction.a.IntegralEstimates.Majorants`:

* **compact top edge** (`I₂`, `I₄`) and **vertical tail** (`I₆`): the integrand is bounded by
  `w t * exp (-π‖x‖²)` with `w` integrable on the segment, so the Gaussian in `x` and `w` in `t`
  split — this is `prod_integrable_of_gaussian_majorant`;
* **cusp-touching** (`I₅`, and `I₁`, `I₃` up to a unit-modulus phase): here the Gaussian is
  *scaled*, `exp (-π t ‖x‖²)`, and its `x`-integral is `t⁻⁴`, which blows up as `t → 0⁺`. The
  bound `exp (-2π/t) · t²` from the cusp estimate beats it, leaving the integrable
  `exp (-2π/t) · t⁻²`. This is `Φ₅_prod_integrable`, and `Φ₁`, `Φ₃` follow by
  `prod_integrable_of_mul_unit_phase`.

## Main definitions

* `I₁_integrand`–`I₆_integrand`: the integrands as functions `ℝ⁸ × ℝ → ℂ`.

## Main results

* `Φ₁_prod_integrable`–`Φ₆_prod_integrable`: product integrability on `ℝ⁸ × segment`;
* `I₁_eq_integral`–`I₆_eq_integral`: each `Iⱼ` as a set integral of its integrand;
* `I₁_integral_swap`–`I₆_integral_swap`: the Fubini exchanges.

Integrability of each `Iⱼ` over `ℝ⁸` is *not* proved here: it comes from the Schwartz structure.
-/

@[expose] public section

open MeasureTheory Complex Real Set intervalIntegral
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
open MagicFunction.a.RealIntegrands MagicFunction.a.ComplexIntegrands MagicFunction.a.Majorants
open scoped UpperHalfPlane

local notation "V" => EuclideanSpace ℝ (Fin 8)

noncomputable section

namespace MagicFunction.a.Fourier

/-! ## Gaussian workhorses -/

/-- `‖cexp (π I ‖x‖² z)‖ = exp (-π ‖x‖² Im z)`: the modulus of the Gaussian phase attached to a
point `z` of the upper half-plane depends only on `Im z`. -/
lemma norm_cexp_pi_I_norm_sq_mul (x : V) (z : ℂ) :
    ‖cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z)‖ = rexp (-π * ‖x‖ ^ 2 * z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, mul_one,
    sub_zero, zero_sub, zero_add, add_zero, neg_mul]

/-- The Gaussian is integrable on `ℝ⁸`. -/
lemma gaussian_integrable_R8 (c : ℝ) (hc : 0 < c) :
    Integrable (fun x : V ↦ rexp (-c * ‖x‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    (b := c) (by simp [hc]) (0 : ℂ) (0 : V)
  simp only [inner_zero_left, ofReal_zero, mul_zero, add_zero] at h
  have hf : ∀ x : V, rexp (-c * ‖x‖ ^ 2) = ‖cexp (-(c : ℂ) * ‖x‖ ^ 2)‖ := fun x ↦ by
    rw [Complex.norm_exp]
    congr 1
    simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, sq]
  simp_rw [hf]
  exact h.norm

/-- The scaled Gaussian `exp (-c t ‖x‖²)` is integrable on `ℝ⁸` for `c, t > 0`. -/
lemma gaussian_integrable_scaled (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    Integrable (fun x : V ↦ rexp (-c * t * ‖x‖ ^ 2)) := by
  simpa [neg_mul] using gaussian_integrable_R8 (c * t) (mul_pos hc ht)

/-- The `ℝ⁸`-integral of the scaled Gaussian, in the normalisation `c = π t`. -/
lemma integral_gaussian_scaled {t : ℝ} (ht : 0 < t) :
    ∫ x : V, rexp (-π * t * ‖x‖ ^ 2) = t⁻¹ ^ 4 := by
  have h : ∫ x : V, rexp (-(π * t) * ‖x‖ ^ 2)
      = (π / (π * t)) ^ ((Module.finrank ℝ V : ℝ) / 2) :=
    GaussianFourier.integral_rexp_neg_mul_sq_norm (mul_pos Real.pi_pos ht)
  rw [finrank_euclideanSpace_fin] at h
  convert h using 2
  · ring_nf
  · have : π / (π * t) = t⁻¹ := by field_simp
    norm_num [this]

/-- The product measure with a restricted second factor, as a restricted product measure. -/
lemma volume_prod_restrict_eq (s : Set ℝ) :
    (volume : Measure V).prod ((volume : Measure ℝ).restrict s) =
      ((volume : Measure V).prod (volume : Measure ℝ)).restrict (univ ×ˢ s) := by
  conv_lhs => rw [← Measure.restrict_univ (μ := (volume : Measure V))]
  rw [Measure.prod_restrict]

/-! ## Two generic routes to product integrability -/

/-- **Unscaled Gaussian majorant.** If `‖f (x, t)‖ ≤ exp (-π‖x‖²) * w t` on `ℝ⁸ × s` with `w`
integrable on `s`, then `f` is product integrable: the majorant splits as a product of a
function of `x` and a function of `t`.

This covers the compact top-edge segments (`w` constant) and the vertical tail
(`w t = C exp (-2πt)`). -/
theorem prod_integrable_of_gaussian_majorant {f : V × ℝ → ℂ} {s : Set ℝ} {w : ℝ → ℝ}
    (hs : MeasurableSet s)
    (hmeas : AEStronglyMeasurable f (volume.prod (volume.restrict s)))
    (hw : IntegrableOn w s volume)
    (hb : ∀ x : V, ∀ t ∈ s, ‖f (x, t)‖ ≤ rexp (-π * ‖x‖ ^ 2) * w t) :
    Integrable f (volume.prod (volume.restrict s)) := by
  refine Integrable.mono' (g := fun p : V × ℝ ↦ rexp (-π * ‖p.1‖ ^ 2) * w p.2)
    ((gaussian_integrable_R8 π Real.pi_pos).mul_prod hw) hmeas ?_
  rw [volume_prod_restrict_eq, ae_restrict_iff' (MeasurableSet.univ.prod hs)]
  exact ae_of_all _ fun ⟨x, t⟩ ⟨_, ht⟩ ↦ hb x t ht

/-- **Transfer along a unit-modulus phase.** If `f (x, t) = g (x, t) * φ x` on `ℝ⁸ × s` with
`φ` continuous of modulus one, then `f` inherits product integrability from `g`.

This is how `Φ₁` and `Φ₃` inherit from `Φ₅`. -/
theorem prod_integrable_of_mul_unit_phase {f g : V × ℝ → ℂ} {s : Set ℝ} {φ : V → ℂ}
    (hs : MeasurableSet s) (hg : Integrable g (volume.prod (volume.restrict s)))
    (hφ : Continuous φ) (hφ1 : ∀ x, ‖φ x‖ = 1)
    (heq : ∀ x : V, ∀ t ∈ s, f (x, t) = g (x, t) * φ x) :
    Integrable f (volume.prod (volume.restrict s)) := by
  have hmul : Integrable (fun p : V × ℝ ↦ g p * φ p.1)
      (volume.prod (volume.restrict s)) := by
    refine Integrable.mono' hg.norm
      (hg.aestronglyMeasurable.mul (hφ.comp continuous_fst).aestronglyMeasurable) ?_
    exact ae_of_all _ fun p ↦ by rw [norm_mul, hφ1 p.1, mul_one]
  refine hmul.congr ?_
  rw [volume_prod_restrict_eq] at hmul ⊢
  exact Filter.eventually_of_mem (self_mem_ae_restrict (MeasurableSet.univ.prod hs))
    fun ⟨x, t⟩ ⟨_, ht⟩ ↦ (heq x t ht).symm

/-! ## Continuity helpers -/

/-- `φ₀'' ∘ g` is continuous whenever `g` is continuous into the open upper half-plane. -/
lemma continuous_φ₀''_comp {g : ℝ → ℂ} (hg : Continuous g) (him : ∀ t, 0 < (g t).im) :
    Continuous (fun t ↦ φ₀'' (g t)) :=
  φ₀''_holo.continuousOn.comp_continuous hg him

/-- The exponential factor `cexp (π I ‖x‖² z t)` is continuous on `ℝ⁸ × ℝ`. -/
lemma continuous_cexp_norm_sq_mul_path {z : ℝ → ℂ} (hz : Continuous z) :
    Continuous (fun p : V × ℝ ↦ cexp (π * I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * z p.2)) := by
  refine Complex.continuous_exp.comp ?_
  have h : Continuous (fun p : V × ℝ ↦ ((‖p.1‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_norm.comp continuous_fst).pow 2)
  exact (continuous_const.mul h).mul (hz.comp continuous_snd)

/-- If `Im (w t) = 1` throughout, then `-1 / w t` lies in the upper half-plane. -/
lemma im_neg_inv_pos_of_im_one {w : ℝ → ℂ} (him : ∀ t, (w t).im = 1) (t : ℝ) :
    0 < (-1 / w t).im := by
  simp only [neg_div, neg_im, one_div, inv_im, him, neg_neg]
  have hns : 0 < normSq (w t) := normSq_pos.mpr fun h ↦ by
    have := him t; rw [h] at this; simp at this
  positivity

/-- `φ₀'' (-1 / w t)` is continuous when `w` is continuous with `Im (w t) = 1`: the case of the
top edge of the fundamental domain, where the `Iⱼ` parametrisations all have imaginary part 1. -/
lemma continuous_φ₀''_neg_inv_im_one {w : ℝ → ℂ} (hw : Continuous w) (him : ∀ t, (w t).im = 1) :
    Continuous (fun t ↦ φ₀'' (-1 / w t)) := by
  have hne : ∀ t, w t ≠ 0 := fun t h ↦ by simpa [h, him t] using (him t).symm
  exact continuous_φ₀''_comp (continuous_const.div hw hne) (im_neg_inv_pos_of_im_one him)

/-- `t ↦ φ₀'' (I t)` is continuous on `(0, ∞)`. -/
lemma continuousOn_φ₀''_I_mul :
    ContinuousOn (fun t : ℝ ↦ φ₀'' (I * t)) (Ioi 0) :=
  φ₀''_holo.continuousOn.comp (continuousOn_const.mul continuous_ofReal.continuousOn)
    fun t ht ↦ by simpa using mem_Ioi.mp ht

/-! ## The integrands -/

/-- The `I₁` integrand on `ℝ⁸ × (0, 1]`. -/
def I₁_integrand (p : V × ℝ) : ℂ := Φ₁ (‖p.1‖ ^ 2) p.2

/-- The `I₂` integrand on `ℝ⁸ × [0, 1]`. -/
def I₂_integrand (p : V × ℝ) : ℂ := Φ₂ (‖p.1‖ ^ 2) p.2

/-- The `I₃` integrand on `ℝ⁸ × (0, 1]`. -/
def I₃_integrand (p : V × ℝ) : ℂ := Φ₃ (‖p.1‖ ^ 2) p.2

/-- The `I₄` integrand on `ℝ⁸ × [0, 1]`. -/
def I₄_integrand (p : V × ℝ) : ℂ := Φ₄ (‖p.1‖ ^ 2) p.2

/-- The `I₅` integrand on `ℝ⁸ × (0, 1]`. -/
def I₅_integrand (p : V × ℝ) : ℂ := Φ₅ (‖p.1‖ ^ 2) p.2

/-- The `I₆` integrand on `ℝ⁸ × [1, ∞)`. -/
def I₆_integrand (p : V × ℝ) : ℂ := Φ₆ (‖p.1‖ ^ 2) p.2

/-! ## Compact top-edge segments: `I₂`, `I₄` -/

section TopEdge

/-- On the top edge the `φ₀''` factor is bounded, by compactness. One statement serves both
`I₂` (`u = t`) and `I₄` (`u = -t`). -/
lemma exists_bound_φ₀''_top_edge :
    ∃ M ≥ (0 : ℝ), ∀ u ∈ Icc (-1 : ℝ) 1, ‖φ₀'' (-1 / ((u : ℂ) + I))‖ ≤ M := by
  have hcont : Continuous (fun u : ℝ ↦ φ₀'' (-1 / ((u : ℂ) + I))) := by
    refine continuous_φ₀''_neg_inv_im_one (continuous_ofReal.add continuous_const) fun u ↦ ?_
    simp
  obtain ⟨M, hM0, hM⟩ := (IsCompact.bddAbove_image isCompact_Icc
    (continuous_norm.comp hcont).continuousOn).exists_ge (0 : ℝ)
  exact ⟨M, hM0, fun u hu ↦ hM _ ⟨u, hu, rfl⟩⟩

/-- `‖(u + I)²‖ ≤ 2` for `|u| ≤ 1`. -/
lemma norm_sq_add_I_le {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) : ‖((u : ℂ) + I) ^ 2‖ ≤ 2 := by
  rw [norm_pow, ← normSq_eq_norm_sq]
  simp only [normSq_apply, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im, add_zero, zero_add,
    mul_one]
  nlinarith [hu.1, hu.2]

lemma Φ₂_prod_continuous : Continuous I₂_integrand := by
  unfold I₂_integrand Φ₂ Φ₂'
  have him : ∀ t : ℝ, (z₂' t + 1).im = 1 := fun t ↦ by
    simp only [add_im, one_im, add_zero, z₂', IccExtend, Function.comp_apply, z₂, neg_im, neg_zero,
      ofReal_im, I_im, zero_add]
  exact (((continuous_φ₀''_neg_inv_im_one (continuous_z₂'.add continuous_const)
      him).comp continuous_snd).mul
    (((continuous_z₂'.comp continuous_snd).add continuous_const).pow 2)).mul
    (continuous_cexp_norm_sq_mul_path continuous_z₂')

lemma Φ₄_prod_continuous : Continuous I₄_integrand := by
  unfold I₄_integrand Φ₄ Φ₄'
  have him : ∀ t : ℝ, (z₄' t - 1).im = 1 := fun t ↦ by
    simp only [sub_im, one_im, sub_zero, z₄', IccExtend, Function.comp_apply, z₄, add_im, ofReal_im,
      I_im, zero_add]
  exact continuous_const.mul ((((continuous_φ₀''_neg_inv_im_one
      (continuous_z₄'.sub continuous_const) him).comp continuous_snd).mul
    (((continuous_z₄'.comp continuous_snd).sub continuous_const).pow 2)).mul
    (continuous_cexp_norm_sq_mul_path continuous_z₄'))

lemma Φ₂_prod_norm_bound : ∃ C > 0, ∀ x : V, ∀ t ∈ Icc (0 : ℝ) 1,
    ‖I₂_integrand (x, t)‖ ≤ rexp (-π * ‖x‖ ^ 2) * C := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_φ₀''_top_edge
  refine ⟨2 * (M + 1), by positivity, fun x t ht ↦ ?_⟩
  have ht' : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  simp only [I₂_integrand, Φ₂, Φ₂', z₂'_eq_of_mem ht, show (-1 : ℂ) + t + I + 1 = (t : ℂ) + I by
    ring]
  rw [norm_mul, norm_mul]
  have h_exp : ‖cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (-1 + t + I))‖ = rexp (-π * ‖x‖ ^ 2) := by
    simpa using norm_cexp_pi_I_norm_sq_mul x (-1 + t + I)
  rw [h_exp]
  have h1 : ‖φ₀'' (-1 / ((t : ℂ) + I))‖ * ‖((t : ℂ) + I) ^ 2‖ ≤ 2 * (M + 1) := by
    calc ‖φ₀'' (-1 / ((t : ℂ) + I))‖ * ‖((t : ℂ) + I) ^ 2‖
        ≤ M * 2 := mul_le_mul (hM t ht') (norm_sq_add_I_le ht') (norm_nonneg _) hM0
      _ ≤ 2 * (M + 1) := by linarith
  nlinarith [Real.exp_pos (-π * ‖x‖ ^ 2), norm_nonneg (φ₀'' (-1 / ((t : ℂ) + I))),
    norm_nonneg (((t : ℂ) + I) ^ 2)]

lemma Φ₄_prod_norm_bound : ∃ C > 0, ∀ x : V, ∀ t ∈ Icc (0 : ℝ) 1,
    ‖I₄_integrand (x, t)‖ ≤ rexp (-π * ‖x‖ ^ 2) * C := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_φ₀''_top_edge
  refine ⟨2 * (M + 1), by positivity, fun x t ht ↦ ?_⟩
  have ht' : (-t) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simp only [I₄_integrand, Φ₄, Φ₄', z₄'_eq_of_mem ht, show (1 : ℂ) - t + I - 1 = -(t : ℂ) + I by
    ring]
  rw [norm_mul, norm_mul, norm_mul, show ‖(-1 : ℂ)‖ = 1 by simp, one_mul]
  have h_exp : ‖cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (1 - t + I))‖ = rexp (-π * ‖x‖ ^ 2) := by
    simpa using norm_cexp_pi_I_norm_sq_mul x (1 - t + I)
  rw [h_exp]
  have hcast : ((-t : ℝ) : ℂ) = -(t : ℂ) := by push_cast; ring
  have h1 : ‖φ₀'' (-1 / (-(t : ℂ) + I))‖ * ‖(-(t : ℂ) + I) ^ 2‖ ≤ 2 * (M + 1) := by
    calc ‖φ₀'' (-1 / (-(t : ℂ) + I))‖ * ‖(-(t : ℂ) + I) ^ 2‖
        ≤ M * 2 := by
          refine mul_le_mul ?_ ?_ (norm_nonneg _) hM0
          · simpa [hcast] using hM (-t) ht'
          · simpa [hcast] using norm_sq_add_I_le ht'
      _ ≤ 2 * (M + 1) := by linarith
  nlinarith [Real.exp_pos (-π * ‖x‖ ^ 2), norm_nonneg (φ₀'' (-1 / (-(t : ℂ) + I))),
    norm_nonneg ((-(t : ℂ) + I) ^ 2)]

theorem Φ₂_prod_integrable :
    Integrable I₂_integrand (volume.prod (volume.restrict (Icc 0 1))) := by
  obtain ⟨C, _, hC⟩ := Φ₂_prod_norm_bound
  exact prod_integrable_of_gaussian_majorant measurableSet_Icc
    Φ₂_prod_continuous.aestronglyMeasurable
    (integrableOn_const (by simp [Real.volume_Icc]) ENNReal.coe_ne_top) hC

theorem Φ₄_prod_integrable :
    Integrable I₄_integrand (volume.prod (volume.restrict (Icc 0 1))) := by
  obtain ⟨C, _, hC⟩ := Φ₄_prod_norm_bound
  exact prod_integrable_of_gaussian_majorant measurableSet_Icc
    Φ₄_prod_continuous.aestronglyMeasurable
    (integrableOn_const (by simp [Real.volume_Icc]) ENNReal.coe_ne_top) hC

end TopEdge

/-! ## Vertical tail: `I₆` -/

section VerticalTail

lemma Φ₆_prod_continuousOn : ContinuousOn I₆_integrand (univ ×ˢ Ici (1 : ℝ)) := by
  unfold I₆_integrand Φ₆ Φ₆'
  have h1 : ContinuousOn (fun t : ℝ ↦ φ₀'' (z₆' t)) (Ici 1) := by
    refine (continuousOn_φ₀''_I_mul.mono fun t (ht : (1 : ℝ) ≤ t) ↦
      show t ∈ Ioi (0 : ℝ) by simpa using lt_of_lt_of_le one_pos ht).congr fun t ht ↦ ?_
    exact congrArg φ₀'' (z₆'_eq_of_mem ht)
  exact continuousOn_const.mul
    ((h1.comp continuous_snd.continuousOn fun _ ht ↦ ht.2).mul
      (continuous_cexp_norm_sq_mul_path continuous_z₆').continuousOn)

lemma Φ₆_prod_norm_bound : ∃ C > 0, ∀ x : V, ∀ t ∈ Ici (1 : ℝ),
    ‖I₆_integrand (x, t)‖ ≤ rexp (-π * ‖x‖ ^ 2) * (C * rexp (-2 * π * t)) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀''_I_mul_le
  refine ⟨C₀, hC₀_pos, fun x t ht ↦ ?_⟩
  have ht1 : (1 : ℝ) ≤ t := ht
  simp only [I₆_integrand, Φ₆, Φ₆', z₆'_eq_of_mem ht, norm_mul, Complex.norm_I, one_mul]
  have hgauss : ‖cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (I * (t : ℂ)))‖
      = rexp (-π * ‖x‖ ^ 2 * t) := by
    simpa using norm_cexp_pi_I_norm_sq_mul x (I * t)
  rw [hgauss]
  have hφ : ‖φ₀'' (I * (t : ℂ))‖ ≤ C₀ * rexp (-2 * π * t) := hC₀ t (by linarith)
  have hgle : rexp (-π * ‖x‖ ^ 2 * t) ≤ rexp (-π * ‖x‖ ^ 2) := by
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_pos, sq_nonneg ‖x‖, mul_nonneg Real.pi_pos.le (sq_nonneg ‖x‖)]
  calc ‖φ₀'' (I * (t : ℂ))‖ * rexp (-π * ‖x‖ ^ 2 * t)
      ≤ (C₀ * rexp (-2 * π * t)) * rexp (-π * ‖x‖ ^ 2) :=
        mul_le_mul hφ hgle (Real.exp_pos _).le (le_trans (norm_nonneg _) hφ)
    _ = rexp (-π * ‖x‖ ^ 2) * (C₀ * rexp (-2 * π * t)) := by ring

theorem Φ₆_prod_integrable :
    Integrable I₆_integrand (volume.prod (volume.restrict (Ici 1))) := by
  obtain ⟨C, _, hC⟩ := Φ₆_prod_norm_bound
  refine prod_integrable_of_gaussian_majorant measurableSet_Ici ?_ ?_ hC
  · rw [volume_prod_restrict_eq]
    exact Φ₆_prod_continuousOn.aestronglyMeasurable (MeasurableSet.univ.prod measurableSet_Ici)
  · have h : IntegrableOn (fun t ↦ rexp (-2 * π * t)) (Ici 1) volume :=
      integrableOn_exp_mul_Ici (-2 * π) (by linarith [Real.pi_pos])
    exact h.const_mul C

end VerticalTail

/-! ## Cusp-touching segments: `I₅`, then `I₁` and `I₃` -/

section Cusp

lemma Φ₅_prod_continuousOn : ContinuousOn I₅_integrand (univ ×ˢ Ioc (0 : ℝ) 1) := by
  unfold I₅_integrand Φ₅ Φ₅'
  have h1 : ContinuousOn (fun t : ℝ ↦ φ₀'' (-1 / z₅' t)) (Ioc 0 1) := by
    refine (continuousOn_φ₀''_cusp_path.mono fun t ht ↦ ht.1).congr fun t ht ↦ ?_
    rw [z₅'_eq_of_mem (mem_Icc_of_Ioc ht)]
  exact continuousOn_const.mul
    (((h1.comp continuous_snd.continuousOn fun _ ht ↦ ht.2).mul
      ((continuous_z₅'.comp continuous_snd).pow 2).continuousOn).mul
      (continuous_cexp_norm_sq_mul_path continuous_z₅').continuousOn)

/-- The x-slice of the `I₅` integrand is continuous: only the Gaussian depends on `x`. -/
lemma Φ₅_slice_continuous (t : ℝ) : Continuous (fun x : V ↦ I₅_integrand (x, t)) := by
  simp only [I₅_integrand, Φ₅, Φ₅']
  exact continuous_const.mul (continuous_const.mul (Complex.continuous_exp.comp
    ((continuous_const.mul (continuous_ofReal.comp
      (continuous_norm.pow 2))).mul continuous_const)))

/-- The cusp bound, in product form: `exp (-2π/t) t²` times the *scaled* Gaussian. -/
lemma Φ₅_prod_norm_bound : ∃ C > 0, ∀ x : V, ∀ t ∈ Ioc (0 : ℝ) 1,
    ‖I₅_integrand (x, t)‖ ≤ C * rexp (-2 * π / t) * t ^ 2 * rexp (-π * t * ‖x‖ ^ 2) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀''_neg_inv_I_mul_le
  refine ⟨C₀, hC₀_pos, fun x t ht ↦ ?_⟩
  simp only [I₅_integrand, Φ₅, Φ₅', z₅'_eq_of_mem (mem_Icc_of_Ioc ht), norm_mul,
    Complex.norm_I, one_mul, mul_pow, I_sq, neg_one_mul, norm_neg, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht.1]
  have hgauss : ‖cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (I * (t : ℂ)))‖
      = rexp (-π * t * ‖x‖ ^ 2) := by
    rw [norm_cexp_pi_I_norm_sq_mul]
    simp only [mul_im, I_re, I_im, ofReal_re, ofReal_im, one_mul, mul_zero, zero_add,
      mul_right_comm]
  rw [hgauss]
  gcongr
  exact hC₀ t ht.1 (lt_of_le_of_lt ht.2 one_lt_two)

/-- The heart of the cusp case: after integrating the scaled Gaussian in `x` (contributing
`t⁻⁴`) the remaining `t`-integrand is `C exp (-2π/t) t⁻²`, which is bounded on `(0, 1]`. -/
lemma integral_norm_I₅_le : ∃ C > 0, ∀ t ∈ Ioc (0 : ℝ) 1,
    ∫ x : V, ‖I₅_integrand (x, t)‖ ≤ C * rexp (-2 * π) := by
  obtain ⟨C, hC_pos, hC⟩ := Φ₅_prod_norm_bound
  refine ⟨C, hC_pos, fun t ht ↦ ?_⟩
  have hgauss := gaussian_integrable_scaled π t Real.pi_pos ht.1
  have hmaj : Integrable (fun x : V ↦ C * rexp (-2 * π / t) * t ^ 2 * rexp (-π * t * ‖x‖ ^ 2)) :=
    hgauss.const_mul _
  calc ∫ x : V, ‖I₅_integrand (x, t)‖
      ≤ ∫ x : V, C * rexp (-2 * π / t) * t ^ 2 * rexp (-π * t * ‖x‖ ^ 2) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _)
          hmaj (ae_of_all _ fun x ↦ hC x t ht)
    _ = C * rexp (-2 * π / t) * t ^ 2 * ∫ x : V, rexp (-π * t * ‖x‖ ^ 2) := by
        rw [← MeasureTheory.integral_const_mul]
    _ = C * rexp (-2 * π / t) * t ^ 2 * t⁻¹ ^ 4 := by rw [integral_gaussian_scaled ht.1]
    _ = C * (rexp (-2 * π / t) * t⁻¹ ^ 2) := by field_simp
    _ ≤ C * rexp (-2 * π) := by
        refine mul_le_mul_of_nonneg_left ?_ hC_pos.le
        exact exp_neg_div_mul_inv_sq_le ht.1 ht.2

theorem Φ₅_prod_integrable :
    Integrable I₅_integrand (volume.prod (volume.restrict (Ioc 0 1))) := by
  obtain ⟨C, hC_pos, hC⟩ := Φ₅_prod_norm_bound
  have hmeas : AEStronglyMeasurable I₅_integrand (volume.prod (volume.restrict (Ioc 0 1))) := by
    rw [volume_prod_restrict_eq]
    exact Φ₅_prod_continuousOn.aestronglyMeasurable (MeasurableSet.univ.prod measurableSet_Ioc)
  rw [MeasureTheory.integrable_prod_iff' hmeas]
  obtain ⟨C', hC'_pos, hC'⟩ := integral_norm_I₅_le
  refine ⟨?_, ?_⟩
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine ae_of_all _ fun t ht ↦ ?_
    exact Integrable.mono' ((gaussian_integrable_scaled π t Real.pi_pos ht.1).const_mul _)
      (Φ₅_slice_continuous t).aestronglyMeasurable (ae_of_all _ fun x ↦ hC x t ht)
  · refine Integrable.mono' (integrable_const (C' * rexp (-2 * π))) ?_ ?_
    · have hswap : AEStronglyMeasurable (fun p : ℝ × V ↦ ‖I₅_integrand (p.2, p.1)‖)
          ((volume.restrict (Ioc 0 1)).prod (volume : Measure V)) := by
        have h : AEStronglyMeasurable (fun p ↦ ‖I₅_integrand p‖)
            (Measure.map Prod.swap
              (((volume : Measure ℝ).restrict (Ioc 0 1)).prod (volume : Measure V))) := by
          rw [Measure.prod_swap]; exact hmeas.norm
        exact h.comp_measurable measurable_swap
      exact hswap.integral_prod_right'
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine ae_of_all _ fun t ht ↦ ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
      exact hC' t ht

theorem Φ₁_prod_integrable :
    Integrable I₁_integrand (volume.prod (volume.restrict (Ioc 0 1))) :=
  prod_integrable_of_mul_unit_phase measurableSet_Ioc Φ₅_prod_integrable
    (φ := fun x : V ↦ cexp (((-(π * ‖x‖ ^ 2) : ℝ) : ℂ) * I)) (by fun_prop)
    (fun x ↦ Complex.norm_exp_ofReal_mul_I _)
    fun x t ht ↦ Φ₁_eq_Φ₅_mul_phase (mem_Icc_of_Ioc ht)

theorem Φ₃_prod_integrable :
    Integrable I₃_integrand (volume.prod (volume.restrict (Ioc 0 1))) :=
  prod_integrable_of_mul_unit_phase measurableSet_Ioc Φ₅_prod_integrable
    (φ := fun x : V ↦ cexp (((π * ‖x‖ ^ 2 : ℝ) : ℂ) * I)) (by fun_prop)
    (fun x ↦ Complex.norm_exp_ofReal_mul_I _)
    fun x t ht ↦ Φ₃_eq_Φ₅_mul_phase (mem_Icc_of_Ioc ht)

end Cusp

/-! ## Each `Iⱼ` as a set integral of its integrand -/

section EqIntegral

lemma I₁_eq_integral (x : V) : I₁ x = ∫ t in Ioc (0 : ℝ) 1, I₁_integrand (x, t) := by
  rw [I₁, I₁'_eq_Ioc]
  refine setIntegral_congr_ae₀ nullMeasurableSet_Ioc (ae_of_all _ fun t ht ↦ ?_)
  simp only [I₁_integrand, Φ₁, Φ₁', z₁'_eq_of_mem (mem_Icc_of_Ioc ht), ofReal_pow]
  have h_exp : ∀ r : ℂ, cexp ((π : ℂ) * I * r * (-1 + I * (t : ℂ))) =
      cexp (-(π : ℂ) * I * r) * cexp (-(π : ℂ) * r * (t : ℂ)) := fun r ↦ by
    rw [← Complex.exp_add]
    congr 1
    rw [show (π : ℂ) * I * r * (-1 + I * t) = -(π : ℂ) * I * r + (π : ℂ) * (I * I) * r * t by ring,
      I_mul_I]
    ring
  simp only [show (-1 : ℂ) + I * (t : ℂ) + 1 = I * (t : ℂ) by ring, mul_pow, I_sq, h_exp]
  ring

lemma I₂_eq_integral (x : V) : I₂ x = ∫ t in Icc (0 : ℝ) 1, I₂_integrand (x, t) := by
  rw [I₂, I₂'_eq, intervalIntegral_eq_integral_uIoc, if_pos (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), one_smul]
  rw [← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_ae₀ nullMeasurableSet_Icc (ae_of_all _ fun t ht ↦ ?_)
  simp only [I₂_integrand, Φ₂, Φ₂', z₂'_eq_of_mem ht, ofReal_pow]
  have h_exp : ∀ r : ℂ, cexp ((π : ℂ) * I * r * (-1 + (t : ℂ) + I)) =
      cexp (-(π : ℂ) * I * r) * cexp ((π : ℂ) * I * r * (t : ℂ)) * cexp (-(π : ℂ) * r) :=
    fun r ↦ by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      calc (π : ℂ) * I * r * (-1 + (t : ℂ) + I)
          = -(π : ℂ) * I * r + (π : ℂ) * I * r * (t : ℂ) + (π : ℂ) * (I * I) * r := by ring
        _ = _ := by rw [I_mul_I]; ring
  simp only [show (-1 : ℂ) + (t : ℂ) + I + 1 = (t : ℂ) + I by ring, h_exp]
  ring

lemma I₃_eq_integral (x : V) : I₃ x = ∫ t in Ioc (0 : ℝ) 1, I₃_integrand (x, t) := by
  rw [I₃, I₃'_eq_Ioc]
  refine setIntegral_congr_ae₀ nullMeasurableSet_Ioc (ae_of_all _ fun t ht ↦ ?_)
  simp only [I₃_integrand, Φ₃, Φ₃', z₃'_eq_of_mem (mem_Icc_of_Ioc ht), ofReal_pow]
  have h_exp : ∀ r : ℂ, cexp ((π : ℂ) * I * r * (1 + I * (t : ℂ))) =
      cexp ((π : ℂ) * I * r) * cexp (-(π : ℂ) * r * (t : ℂ)) := fun r ↦ by
    rw [← Complex.exp_add]
    congr 1
    rw [show (π : ℂ) * I * r * (1 + I * t) = (π : ℂ) * I * r + (π : ℂ) * (I * I) * r * t by ring,
      I_mul_I]
    ring
  simp only [show (1 : ℂ) + I * (t : ℂ) - 1 = I * (t : ℂ) by ring, mul_pow, I_sq, h_exp]
  ring

lemma I₄_eq_integral (x : V) : I₄ x = ∫ t in Icc (0 : ℝ) 1, I₄_integrand (x, t) := by
  rw [I₄, I₄'_eq, intervalIntegral_eq_integral_uIoc, if_pos (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), one_smul]
  rw [← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_ae₀ nullMeasurableSet_Icc (ae_of_all _ fun t ht ↦ ?_)
  simp only [I₄_integrand, Φ₄, Φ₄', z₄'_eq_of_mem ht, ofReal_pow]
  have h_exp : ∀ r : ℂ, cexp ((π : ℂ) * I * r * (1 - (t : ℂ) + I)) =
      cexp ((π : ℂ) * I * r) * cexp (-(π : ℂ) * I * r * (t : ℂ)) * cexp (-(π : ℂ) * r) :=
    fun r ↦ by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      calc (π : ℂ) * I * r * (1 - (t : ℂ) + I)
          = (π : ℂ) * I * r - (π : ℂ) * I * r * (t : ℂ) + (π : ℂ) * (I * I) * r := by ring
        _ = _ := by rw [I_mul_I]; ring
  simp only [show (1 : ℂ) - (t : ℂ) + I - 1 = -(t : ℂ) + I by ring, h_exp]
  ring

lemma I₅_eq_integral (x : V) : I₅ x = -2 * ∫ t in Ioc (0 : ℝ) 1, I₅_integrand (x, t) := by
  rw [I₅, I₅'_eq_Ioc]
  congr 1
  refine setIntegral_congr_ae₀ nullMeasurableSet_Ioc (ae_of_all _ fun t ht ↦ ?_)
  simp only [I₅_integrand, Φ₅, Φ₅', z₅'_eq_of_mem (mem_Icc_of_Ioc ht), cexp_pi_I_mul_I,
    mul_pow, I_sq]
  push_cast
  ring_nf

lemma I₆_eq_integral (x : V) : I₆ x = 2 * ∫ t in Ici (1 : ℝ), I₆_integrand (x, t) := by
  rw [I₆, I₆'_eq]
  congr 1
  refine setIntegral_congr_ae₀ nullMeasurableSet_Ici (ae_of_all _ fun t ht ↦ ?_)
  simp only [I₆_integrand, Φ₆, Φ₆', z₆'_eq_of_mem ht, cexp_pi_I_mul_I]
  push_cast
  ring_nf

end EqIntegral

/-! ## The Fubini exchanges -/

section FubiniSwap

theorem I₁_integral_swap :
    ∫ x : V, I₁ x = ∫ t in Ioc (0 : ℝ) 1, ∫ x : V, I₁_integrand (x, t) := by
  simp_rw [I₁_eq_integral]
  exact integral_integral_swap Φ₁_prod_integrable

theorem I₂_integral_swap :
    ∫ x : V, I₂ x = ∫ t in Icc (0 : ℝ) 1, ∫ x : V, I₂_integrand (x, t) := by
  simp_rw [I₂_eq_integral]
  exact integral_integral_swap Φ₂_prod_integrable

theorem I₃_integral_swap :
    ∫ x : V, I₃ x = ∫ t in Ioc (0 : ℝ) 1, ∫ x : V, I₃_integrand (x, t) := by
  simp_rw [I₃_eq_integral]
  exact integral_integral_swap Φ₃_prod_integrable

theorem I₄_integral_swap :
    ∫ x : V, I₄ x = ∫ t in Icc (0 : ℝ) 1, ∫ x : V, I₄_integrand (x, t) := by
  simp_rw [I₄_eq_integral]
  exact integral_integral_swap Φ₄_prod_integrable

theorem I₅_integral_swap :
    ∫ x : V, I₅ x = -2 * ∫ t in Ioc (0 : ℝ) 1, ∫ x : V, I₅_integrand (x, t) := by
  simp_rw [I₅_eq_integral]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact integral_integral_swap Φ₅_prod_integrable

theorem I₆_integral_swap :
    ∫ x : V, I₆ x = 2 * ∫ t in Ici (1 : ℝ), ∫ x : V, I₆_integrand (x, t) := by
  simp_rw [I₆_eq_integral]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact integral_integral_swap Φ₆_prod_integrable

end FubiniSwap

end MagicFunction.a.Fourier

end
