/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular

/-! # Deforming Paths of Integration for Open Contours

We deform paths of integration along rectangular contours extending infinitely in the vertical
direction, under Cauchy-Goursat-type conditions and the hypothesis that the top-edge integral tends
to zero. Uniform decay within the vertical strip suffices for this limit. The original theorems
assuming decay uniformly over all real parts are retained as wrappers.
-/

@[expose] public section
open Set Real Complex intervalIntegral Metric Filter MeasureTheory

open scoped Interval Topology

namespace Complex

section aux

-- WHY ARE THESE NOT JUST `exact?`????!!!!
theorem re_of_real_add_real_mul_I (x y : ℝ) : (x + y * I).re = x := by simp
theorem im_of_real_add_real_mul_I (x y : ℝ) : (x + y * I).im = y := by simp

end aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {x₁ x₂ : ℝ} (y : ℝ)

section Tendsto_Zero

/-- Strip-local decay suffices: if `f` decays uniformly as `Im z → ∞` *within the vertical strip*
`[[x₁, x₂]] ×ℂ ℝ` swept by the top edge, then
$\lim_{m \to \infty} \int_{x_1}^{x_2} f(x + mI) dx = 0$.

This is the primitive form. The decay is only ever used at points of the strip, so requiring it
off the strip would be gratuitous — and in applications often false, since an integrand can decay
as `Im z → ∞` within a bounded strip while growing without bound along a horizontal line. -/
lemma tendsto_integral_atTop_nhds_zero_of_tendsto_im_atTop_nhds_zero_of_mem_uIcc
    (htendsto : ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, z.re ∈ [[x₁, x₂]] → M ≤ z.im → ‖f z‖ < ε) :
    Tendsto (fun (m : ℝ) ↦ ∫ (x : ℝ) in x₁..x₂, f (x + m * I)) atTop (𝓝 0) := by
  simp only [NormedAddGroup.tendsto_nhds_zero, eventually_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := htendsto (ε / (|x₂ - x₁| + 1)) (by positivity)
  refine ⟨M, fun y hy ↦ ?_⟩
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦
    (hM (x + y * I) (by simpa using uIoc_subset_uIcc hx)
      (by simpa using hy)).le).trans_lt ?_
  have hpos : 0 < ε / (|x₂ - x₁| + 1) := by positivity
  have hcancel := div_mul_cancel₀ ε (by positivity : |x₂ - x₁| + 1 ≠ 0)
  nlinarith

/-- If $f(z) \to 0$ as $\Im(z) \to \infty$, then
  $\lim_{m \to \infty} \int_{x_1}^{x_2} f(x + mI) dx = 0$.

A wrapper around the strip-local
`tendsto_integral_atTop_nhds_zero_of_tendsto_im_atTop_nhds_zero_of_mem_uIcc`. -/
lemma tendsto_integral_atTop_nhds_zero_of_tendsto_im_atTop_nhds_zero
    (htendsto : ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖f z‖ < ε) :
    Tendsto (fun (m : ℝ) ↦ ∫ (x : ℝ) in x₁..x₂, f (x + m * I)) atTop (𝓝 0) :=
  tendsto_integral_atTop_nhds_zero_of_tendsto_im_atTop_nhds_zero_of_mem_uIcc
    (fun ε hε ↦ (htendsto ε hε).imp fun _ hM z _ hz ↦ hM z hz)

end Tendsto_Zero

section Eventually_Eq_Zero

private lemma hzero (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y))) (s : Set ℂ) (hs : s.Countable)
    (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Ioi y)) \ s, DifferentiableAt ℂ f x) :
    ∀ m ≥ y, (∫ (x : ℝ) in x₁..x₂, f (x + y * I)) - (∫ (x : ℝ) in x₁..x₂, f (x + m * I))
      + (I • ∫ (t : ℝ) in y..m, f (x₂ + t * I)) - (I • ∫ (t : ℝ) in y..m, f (x₁ + t * I))
    = 0 := by
  intro m hm
  calc _
  _ = (((∫ (t : ℝ) in (x₁ + y * I).re..(x₂ + m * I).re, f (t + (x₁ + y * I).im * I))
      - ∫ (t : ℝ) in (x₁ + y * I).re..(x₂ + m * I).re, f (t + (x₂ + m * I).im * I))
      + I • ∫ (t : ℝ) in (x₁ + y * I).im..(x₂ + m * I).im, f ((x₂ + m * I).re + t * I))
      - I • ∫ (t : ℝ) in (x₁ + y * I).im..(x₂ + m * I).im, f ((x₁ + y * I).re + t * I) := by
      simp only [re_of_real_add_real_mul_I, im_of_real_add_real_mul_I]
  _ = 0 := by
      refine Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
        f (x₁ + y * I) (x₂ + m * I) s hs ?_ ?_ <;>
      simp only [re_of_real_add_real_mul_I, im_of_real_add_real_mul_I]
      · refine hcont.mono (reProdIm_subset_iff.mpr ?_)
        gcongr
        exact (uIcc_of_le hm).subset.trans Icc_subset_Ici_self
      · rintro z ⟨hz₁, hz₂⟩
        rw [mem_reProdIm, inf_eq_left.2 hm] at hz₁
        exact hdiff z ⟨⟨hz₁.1, hz₁.2.1⟩, hz₂⟩

/-- A direct consequence of the **Cauchy-Goursat Theorem for rectangles**: given the conditions of
the Cauchy-Goursat Theorem between two vertical lines in the Complex plane, fixing some `y`, the
integral around rectangles bounded by these vertical lines, the horizontal line with imaginary
part `y`, and a horizontal line with imaginary part `m` is eventually equal to `0`.

By Cauchy-Goursat, it is immediate that this is true when `m ≥ y`. Indeed, the contents of this
lemma are not particularly nontrivial. The point is to state this fact using `eventually` result so
it will be compatible with `tendsto_congr'`, which is useful for applications. -/
lemma integral_boundary_rect_eq_zero_eventually_atTop_of_differentiable_on_off_countable
    (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y))) (s : Set ℂ) (hs : s.Countable)
    (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Ioi y)) \ s, DifferentiableAt ℂ f x) :
    (fun (m : ℝ) ↦
      (∫ (x : ℝ) in x₁..x₂, f (x + y * I))
        - (∫ (x : ℝ) in x₁..x₂, f (x + m * I))
        + (I • ∫ (t : ℝ) in y..m, f (x₂ + t * I))
        - (I • ∫ (t : ℝ) in y..m, f (x₁ + t * I)))
    =ᶠ[atTop] (fun (_ : ℝ) ↦ 0) :=
  (eventually_ge_atTop y).mono (hzero y hcont s hs hdiff)

end Eventually_Eq_Zero

section Contour_Deformation_Tensdsto

/-- **Deformation of open rectangular contours:** Given two infinite vertical contours such that a
function satisfies Cauchy-Goursat conditions between them, interval integrals of increasing interval
length along the first contour tend to the sum of a translation integral and the limit of interval
integrals along the second integral.

We call this a deformation of _open rectangular contours_ because it allows us to change contours
when working with contours that look like "infinite boxes without lids"---that is, rectangular
contours that are "open" at the top (we do not mean open in a topological sense). -/
theorem tendsto_integral_boundary_open_rect_one_side_atTop_of_tendsto_top
    (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y))) (s : Set ℂ) (hs : s.Countable)
    (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Ioi y)) \ s, DifferentiableAt ℂ f x)
    {C₂ : E} (hC₂ : Tendsto (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₂ + t * I)) atTop (𝓝 C₂))
    (htop : Tendsto (fun (m : ℝ) ↦ ∫ (x : ℝ) in x₁..x₂, f (x + m * I)) atTop (𝓝 0)) :
    Tendsto (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₁ + t * I)) atTop <|
      𝓝 ((∫ (t : ℝ) in x₁..x₂, f (t + y * I)) + C₂) := by
  refine Tendsto.congr' ((eventually_ge_atTop y).mono fun m hm ↦
    sub_eq_zero.mp (hzero y hcont s hs hdiff m hm)) ?_
  simpa using (tendsto_const_nhds.sub htop).add hC₂

/-- **Deformation of open rectangular contours.** The original formulation, whose decay hypothesis
is global in the real direction; it is a wrapper around the `_of_tendsto_top` version. -/
theorem tendsto_integral_boundary_open_rect_one_side_atTop_nhds_sum_other_two_sides
    (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y))) (s : Set ℂ) (hs : s.Countable)
    (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Ioi y)) \ s, DifferentiableAt ℂ f x)
    {C₂ : E} (hC₂ : Tendsto (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₂ + t * I)) atTop (𝓝 C₂))
    (htendsto : ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖f z‖ < ε) :
    Tendsto (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₁ + t * I)) atTop <|
      𝓝 ((∫ (t : ℝ) in x₁..x₂, f (t + y * I)) + C₂) :=
  tendsto_integral_boundary_open_rect_one_side_atTop_of_tendsto_top
    y hcont s hs hdiff hC₂
    (tendsto_integral_atTop_nhds_zero_of_tendsto_im_atTop_nhds_zero htendsto)

/-- **Deformation of open rectangular contours:** Given two infinite vertical contours such that a
function satisfies Cauchy-Goursat conditions between them, the limit of interval integrals along the
first contour equals the sum of a translation integral and the limit of interval integrals along
the second integral. -/
theorem integral_boundary_open_rect_eq_zero_of_tendsto_top
    (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y))) (s : Set ℂ) (hs : s.Countable)
    (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Ioi y)) \ s, DifferentiableAt ℂ f x)
    {C₁ : E} (hC₁ : Tendsto (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₁ + t * I)) atTop (𝓝 C₁))
    {C₂ : E} (hC₂ : Tendsto (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₂ + t * I)) atTop (𝓝 C₂))
    (htop : Tendsto (fun (m : ℝ) ↦ ∫ (x : ℝ) in x₁..x₂, f (x + m * I)) atTop (𝓝 0)) :
    (∫ (t : ℝ) in x₁..x₂, f (t + y * I)) + C₂ - C₁ = 0 :=
  sub_eq_zero_of_eq <| tendsto_nhds_unique
    (tendsto_integral_boundary_open_rect_one_side_atTop_of_tendsto_top y hcont s hs hdiff hC₂ htop)
    hC₁

/-- Wrapper for the globally-decaying formulation. -/
theorem integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable
    (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y))) (s : Set ℂ) (hs : s.Countable)
    (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Ioi y)) \ s, DifferentiableAt ℂ f x)
    {C₁ : E} (hC₁ : Tendsto (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₁ + t * I)) atTop (𝓝 C₁))
    {C₂ : E} (hC₂ : Tendsto (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₂ + t * I)) atTop (𝓝 C₂))
    (htendsto : ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖f z‖ < ε) :
    (∫ (t : ℝ) in x₁..x₂, f (t + y * I)) + C₂ - C₁ = 0 :=
  integral_boundary_open_rect_eq_zero_of_tendsto_top
    y hcont s hs hdiff hC₁ hC₂
    (tendsto_integral_atTop_nhds_zero_of_tendsto_im_atTop_nhds_zero htendsto)

/-- **Deformation of open rectangular contours:** Given two infinite vertical contours such that a
function satisfies Cauchy-Goursat conditions between them, the limit of interval integrals along the
first contour equals the sum of a translation integral and the limit of interval integrals along
the second integral.

This is a variant of `integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable`. The
sole difference is that the assumptions in this lemma do not include the factor of `I` that comes
from contour parametrisation. The reason we state this version is that it might be more convenient
to use in certain cases.
-/
theorem integral_boundary_open_rect_eq_zero_of_tendsto_top'
    (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y))) (s : Set ℂ) (hs : s.Countable)
    (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Ioi y)) \ s, DifferentiableAt ℂ f x)
    {C₁ : E} (hC₁ : Tendsto (fun m ↦ ∫ (t : ℝ) in y..m, f (x₁ + t * I)) atTop (𝓝 C₁))
    {C₂ : E} (hC₂ : Tendsto (fun m ↦ ∫ (t : ℝ) in y..m, f (x₂ + t * I)) atTop (𝓝 C₂))
    (htop : Tendsto (fun (m : ℝ) ↦ ∫ (x : ℝ) in x₁..x₂, f (x + m * I)) atTop (𝓝 0)) :
    (∫ (t : ℝ) in x₁..x₂, f (t + y * I)) + (I • C₂) - (I • C₁) = 0 :=
  integral_boundary_open_rect_eq_zero_of_tendsto_top
    y hcont s hs hdiff (hC₁.const_smul I) (hC₂.const_smul I) htop

/-- Wrapper for the globally-decaying formulation. -/
theorem integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable'
    (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y))) (s : Set ℂ) (hs : s.Countable)
    (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Ioi y)) \ s, DifferentiableAt ℂ f x)
    {C₁ : E} (hC₁ : Tendsto (fun m ↦ ∫ (t : ℝ) in y..m, f (x₁ + t * I)) atTop (𝓝 C₁))
    {C₂ : E} (hC₂ : Tendsto (fun m ↦ ∫ (t : ℝ) in y..m, f (x₂ + t * I)) atTop (𝓝 C₂))
    (htendsto : ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖f z‖ < ε) :
    (∫ (t : ℝ) in x₁..x₂, f (t + y * I)) + (I • C₂) - (I • C₁) = 0 :=
  integral_boundary_open_rect_eq_zero_of_tendsto_top'
    y hcont s hs hdiff hC₁ hC₂
    (tendsto_integral_atTop_nhds_zero_of_tendsto_im_atTop_nhds_zero htendsto)

end Contour_Deformation_Tensdsto

section Contour_Deformation_of_Integrable_along_BOTH

/-- **Deformation of open rectangular contours:** Given two infinite vertical contours such that a
function satisfies Cauchy-Goursat conditions between them and is integrable along both vertical
contours, the improper integral along the first contour equals the sum of a translation integral
and the improper integrals along the second integral.

This is a variant of `integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable'` that
requires the much stronger assumption of integrability. The reason integrability is stronger is that
it requires the integral of the norm of the function to be finite rather than just that of the
function. We nevertheless include this version of the theorem because it is likely that in
applications involving specific functions, there will already be proofs of integrability.
-/
theorem integral_boundary_open_rect_eq_zero_of_integrable_on_of_tendsto_top
    (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y))) (s : Set ℂ) (hs : s.Countable)
    (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Ioi y)) \ s, DifferentiableAt ℂ f x)
    (hint₁ : IntegrableOn (fun (t : ℝ) ↦ f (x₁ + t * I)) (Ioi y) volume)
    (hint₂ : IntegrableOn (fun (t : ℝ) ↦ f (x₂ + t * I)) (Ioi y) volume)
    (htop : Tendsto (fun (m : ℝ) ↦ ∫ (x : ℝ) in x₁..x₂, f (x + m * I)) atTop (𝓝 0)) :
    (∫ (x : ℝ) in x₁..x₂, f (x + y * I)) + (I • ∫ (t : ℝ) in Ioi y, f (x₂ + t * I))
      - (I • ∫ (t : ℝ) in Ioi y, f (x₁ + t * I)) = 0 :=
  integral_boundary_open_rect_eq_zero_of_tendsto_top' y hcont s hs hdiff
    (intervalIntegral_tendsto_integral_Ioi y hint₁ tendsto_id)
    (intervalIntegral_tendsto_integral_Ioi y hint₂ tendsto_id) htop

/-- Wrapper for the globally-decaying formulation. -/
theorem integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
    (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y))) (s : Set ℂ) (hs : s.Countable)
    (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Ioi y)) \ s, DifferentiableAt ℂ f x)
    (hint₁ : IntegrableOn (fun (t : ℝ) ↦ f (x₁ + t * I)) (Ioi y) volume)
    (hint₂ : IntegrableOn (fun (t : ℝ) ↦ f (x₂ + t * I)) (Ioi y) volume)
    (htendsto : ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖f z‖ < ε) :
    (∫ (x : ℝ) in x₁..x₂, f (x + y * I)) + (I • ∫ (t : ℝ) in Ioi y, f (x₂ + t * I))
      - (I • ∫ (t : ℝ) in Ioi y, f (x₁ + t * I)) = 0 :=
  integral_boundary_open_rect_eq_zero_of_integrable_on_of_tendsto_top
    y hcont s hs hdiff hint₁ hint₂
    (tendsto_integral_atTop_nhds_zero_of_tendsto_im_atTop_nhds_zero htendsto)

end Contour_Deformation_of_Integrable_along_BOTH

----------------------------------------------------------------------------------------------------

section Contour_Deformation_of_Integrable_along_ONE

/- I'm not sure if the following is true. Certainly, from `hint₁`, it follows that the integral
of `f` along `x₂` does exist. But does that mean the integral of `‖f‖` along `x₂` also exists? -/
theorem integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on'
    (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y))) (s : Set ℂ) (hs : s.Countable)
    (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Ioi y)) \ s, DifferentiableAt ℂ f x)
    (hint₁ : IntegrableOn (fun (t : ℝ) ↦ f (x₁ + t * I)) (Ioi y) volume)
    (htendsto : ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖f z‖ < ε) :
    (∫ (x : ℝ) in x₁..x₂, f (x + y * I)) + (I • ∫ (t : ℝ) in Ioi y, f (x₂ + t * I))
      - (I • ∫ (t : ℝ) in Ioi y, f (x₁ + t * I)) = 0 := by
  refine integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
    y hcont s hs hdiff hint₁ ?_ htendsto
  sorry

  -- Use the first 3 to prove the last one. Also find pf that continuous functions are integrable
  -- on bounded intervals - use `integrableOn_Ioi_of_intervalIntegral_norm_tendsto`.
  -- NOT EVEN THE ABOVE.
  -- Say that the integral is eventually the sum of the other three integrals.
  -- Try and do some kind of `integrableOn_of_eventually_eq_integrableOn`
  -- (Maybe prove this? Idk)
  -- let b :=

-- #check integrableOn_Ioi_of_intervalIntegral_norm_tendsto -- use for last one
-- -- #check integrableOn_Ioi_of_intervalIntegral_tendsto -- use for last one
-- #check Filter.tendsto_id

-- #check integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
-- #check intervalIntegral_tendsto_integral_Ioi

end Contour_Deformation_of_Integrable_along_ONE
end Complex
