/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

module
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular

/-! # Deforming Paths of Integration for Open Contours

In this file, we prove that if a function tends to zero as the imaginary part of its input tends to
infinity and satisfies Cauchy-Goursat-type conditions, then we can deform paths of integration along
rectangular contours that extend infinitely in the vertical direction.
-/

namespace Complex

open Set Real intervalIntegral Metric Filter MeasureTheory
open scoped Interval Topology

section aux

@[simp] theorem re_of_real_add_real_mul_I (x y : ℝ) : (x + y * I).re = x := by simp

/-- Imaginary part of `x + y * I` is `y`. -/
@[simp] public theorem im_of_real_add_real_mul_I (x y : ℝ) : (x + y * I).im = y := by simp

end aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {x₁ x₂ : ℝ} (y : ℝ)

section Tendsto_Zero

/-- If $f(z) \to 0$ as $\Im(z) \to \infty$, then
  $\lim_{m \to \infty} \int_{x_1}^{x_2} f(x + mI) dx = 0$. -/
lemma tendsto_integral_atTop_nhds_zero_of_tendsto_im_atTop_nhds_zero
    (htendsto : ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖f z‖ < ε) :
    Tendsto (fun (m : ℝ) ↦ ∫ (x : ℝ) in x₁..x₂, f (x + m * I)) atTop (𝓝 0) := by
  by_cases h : x₁ = x₂
  · subst h; simp
  simp only [NormedAddCommGroup.tendsto_nhds_zero, eventually_atTop, ge_iff_le]
  intro ε hε
  have hx : 0 < |x₂ - x₁| := abs_sub_pos.mpr (ne_comm.mp h)
  obtain ⟨M, hM⟩ :=
    htendsto ((1 / 2 : ℝ) * (ε / |x₂ - x₁|)) (mul_pos (by norm_num) (div_pos hε hx))
  use M
  intro m hm
  calc ‖∫ (x : ℝ) in x₁..x₂, f (x + m * I)‖
  _ ≤ ((1 / 2) * (ε / |x₂ - x₁|)) * |x₂ - x₁| :=
      intervalIntegral.norm_integral_le_of_norm_le_const <| by
      intro x hx'
      exact le_of_lt <| hM (x + m * I) (by simpa using hm)
  _ = (1 / 2) * ε := by
      have hx0 : (|x₂ - x₁| : ℝ) ≠ 0 := ne_of_gt hx
      field_simp [mul_assoc, hx0]
  _ < ε := by linarith

end Tendsto_Zero

section Eventually_Eq_Zero

lemma hzero (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y))) (s : Set ℂ) (hs : s.Countable)
    (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Ioi y)) \ s, DifferentiableAt ℂ f x) :
    ∀ m ≥ y, (∫ (x : ℝ) in x₁..x₂, f (x + y * I)) - (∫ (x : ℝ) in x₁..x₂, f (x + m * I))
      + (I • ∫ (t : ℝ) in y..m, f (x₂ + t * I)) - (I • ∫ (t : ℝ) in y..m, f (x₁ + t * I))
    = 0 := by
  intro m hm
  simpa [re_of_real_add_real_mul_I, im_of_real_add_real_mul_I] using
    (Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f (x₁ + y * I)
      (x₂ + m * I) s hs
      (by
        refine hcont.mono ?_
        rw [reProdIm_subset_iff]
        gcongr
        · simp
        · simpa [re_of_real_add_real_mul_I, im_of_real_add_real_mul_I, uIcc_of_le hm] using
            (Icc_subset_Ici_self : Icc y m ⊆ Ici y))
      (by
        intro z hz
        rcases (by
          simpa [re_of_real_add_real_mul_I, im_of_real_add_real_mul_I] using hz :
            z ∈ (Ioo (min x₁ x₂) (max x₁ x₂) ×ℂ Ioo (min y m) (max y m)) ∧ z ∉ s) with ⟨hz, hzns⟩
        refine hdiff z ⟨?_, hzns⟩
        rw [mem_reProdIm] at hz ⊢
        refine ⟨hz.1, ?_⟩
        have hz_im : y < z.im := by
          have hz_im := (mem_Ioo.1 hz.2).1
          simpa [min_eq_left hm] using hz_im
        exact hz_im))

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
    =ᶠ[atTop] (fun (_ : ℝ) ↦ 0) := by
  filter_upwards [eventually_ge_atTop y] with m hm
  exact hzero y hcont s hs hdiff m hm

end Eventually_Eq_Zero

section Contour_Deformation_Tensdsto

/-- **Deformation of open rectangular contours:** Given two infinite vertical contours such that a
function satisfies Cauchy-Goursat conditions between them, interval integrals of increasing interval
length along the first contour tend to the sum of a translation integral and the limit of interval
integrals along the second integral.

We call this a deformation of _open rectangular contours_ because it allows us to change contours
when working with contours that look like "infinite boxes without lids"---that is, rectangular
contours that are "open" at the top (we do not mean open in a topological sense). -/
theorem tendsto_integral_boundary_open_rect_one_side_atTop_nhds_sum_other_two_sides
    (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y))) (s : Set ℂ) (hs : s.Countable)
    (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Ioi y)) \ s, DifferentiableAt ℂ f x)
    {C₂ : E} (hC₂ : Tendsto (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₂ + t * I)) atTop (𝓝 C₂))
    (htendsto : ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖f z‖ < ε) :
    Tendsto (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₁ + t * I)) atTop <|
      𝓝 ((∫ (t : ℝ) in x₁..x₂, f (t + y * I)) + C₂) := by
  have heventually : (fun (m : ℝ) ↦
      (∫ (x : ℝ) in x₁..x₂, f (x + y * I))
        - (∫ (x : ℝ) in x₁..x₂, f (x + m * I))
        + (I • ∫ (t : ℝ) in y..m, f (x₂ + t * I)))
      =ᶠ[atTop] (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₁ + t * I)) := by
    filter_upwards [eventually_ge_atTop y] with m hm
    rw [← sub_eq_zero, ← (hzero y hcont s hs hdiff m hm)]
  rw [tendsto_congr' heventually.symm, ← sub_zero (∫ (t : ℝ) in x₁..x₂, f (↑t + ↑y * I))]
  refine (Tendsto.sub ?_ ?_).add hC₂
  · rw [sub_zero, tendsto_const_nhds_iff]
  · exact tendsto_integral_atTop_nhds_zero_of_tendsto_im_atTop_nhds_zero htendsto

/-- **Deformation of open rectangular contours:** Given two infinite vertical contours such that a
function satisfies Cauchy-Goursat conditions between them, the limit of interval integrals along the
first contour equals the sum of a translation integral and the limit of interval integrals along
the second integral. -/
theorem integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable
    (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y))) (s : Set ℂ) (hs : s.Countable)
    (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Ioi y)) \ s, DifferentiableAt ℂ f x)
    {C₁ : E} (hC₁ : Tendsto (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₁ + t * I)) atTop (𝓝 C₁))
    {C₂ : E} (hC₂ : Tendsto (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₂ + t * I)) atTop (𝓝 C₂))
    (htendsto : ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖f z‖ < ε) :
    (∫ (t : ℝ) in x₁..x₂, f (t + y * I)) + C₂ - C₁ = 0 := by
  exact sub_eq_zero.2 <|
    (tendsto_nhds_unique hC₁ <|
        tendsto_integral_boundary_open_rect_one_side_atTop_nhds_sum_other_two_sides
          y hcont s hs hdiff hC₂ htendsto).symm

/-- **Deformation of open rectangular contours:** Given two infinite vertical contours such that a
function satisfies Cauchy-Goursat conditions between them, the limit of interval integrals along the
first contour equals the sum of a translation integral and the limit of interval integrals along
the second integral.

This is a variant of `integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable`. The
sole difference is that the assumptions in this lemma do not include the factor of `I` that comes
from contour parametrisation. The reason we state this version is that it might be more convenient
to use in certain cases.
-/
theorem integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable'
    (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y))) (s : Set ℂ) (hs : s.Countable)
    (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Ioi y)) \ s, DifferentiableAt ℂ f x)
    {C₁ : E} (hC₁ : Tendsto (fun m ↦ ∫ (t : ℝ) in y..m, f (x₁ + t * I)) atTop (𝓝 C₁))
    {C₂ : E} (hC₂ : Tendsto (fun m ↦ ∫ (t : ℝ) in y..m, f (x₂ + t * I)) atTop (𝓝 C₂))
    (htendsto : ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖f z‖ < ε) :
    (∫ (t : ℝ) in x₁..x₂, f (t + y * I)) + (I • C₂) - (I • C₁) = 0 :=
  integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable y hcont s hs hdiff
    (hC₁.const_smul I) (hC₂.const_smul I) htendsto

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
public theorem
    integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
    (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y))) (s : Set ℂ) (hs : s.Countable)
    (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Ioi y)) \ s, DifferentiableAt ℂ f x)
    (hint₁ : IntegrableOn (fun (t : ℝ) ↦ f (x₁ + t * I)) (Ioi y) volume)
    (hint₂ : IntegrableOn (fun (t : ℝ) ↦ f (x₂ + t * I)) (Ioi y) volume)
    (htendsto : ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖f z‖ < ε) :
    (∫ (x : ℝ) in x₁..x₂, f (x + y * I)) + (I • ∫ (t : ℝ) in Ioi y, f (x₂ + t * I))
      - (I • ∫ (t : ℝ) in Ioi y, f (x₁ + t * I)) = 0 := by
  refine integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable' y hcont s hs hdiff
    (intervalIntegral_tendsto_integral_Ioi y hint₁ tendsto_id)
    (intervalIntegral_tendsto_integral_Ioi y hint₂ tendsto_id) htendsto

end Contour_Deformation_of_Integrable_along_BOTH

section Contour_Deformation_Tendsto_Top

/-- Finite-rectangle deformation on a bounded strip.

This is a convenience lemma for applications where one already knows directly that the top-edge
interval integral tends to `0` as the height tends to `∞`. -/
public theorem rect_deform_of_tendsto_top {f : ℂ → E} {x₁ x₂ y : ℝ}
    (hcont : ContinuousOn f (Set.uIcc x₁ x₂ ×ℂ Set.Ici y))
    (hdiff :
      ∀ z ∈ (Set.Ioo (min x₁ x₂) (max x₁ x₂) ×ℂ Set.Ioi y), DifferentiableAt ℂ f z)
    (hint₁ :
      IntegrableOn (fun t : ℝ => f ((x₁ : ℂ) + (t : ℂ) * I)) (Set.Ioi y) volume)
    (hint₂ :
      IntegrableOn (fun t : ℝ => f ((x₂ : ℂ) + (t : ℂ) * I)) (Set.Ioi y) volume)
    (htop :
      Tendsto (fun m : ℝ => ∫ x in x₁..x₂, f ((x : ℂ) + (m : ℂ) * I)) atTop (𝓝 0)) :
    (∫ x in x₁..x₂, f ((x : ℂ) + (y : ℂ) * I)) +
          (I • ∫ t in Set.Ioi y, f ((x₂ : ℂ) + (t : ℂ) * I)) -
            (I • ∫ t in Set.Ioi y, f ((x₁ : ℂ) + (t : ℂ) * I)) = 0 := by
  have hrect :
      ∀ m : ℝ, y ≤ m →
        (∫ x in x₁..x₂, f ((x : ℂ) + (y : ℂ) * I)) -
              (∫ x in x₁..x₂, f ((x : ℂ) + (m : ℂ) * I)) +
            (I • ∫ t in y..m, f ((x₂ : ℂ) + (t : ℂ) * I)) -
              (I • ∫ t in y..m, f ((x₁ : ℂ) + (t : ℂ) * I)) = 0 := by
    intro m hm
    have hdiff' :
        ∀ z ∈ ((Set.Ioo (min x₁ x₂) (max x₁ x₂) ×ℂ Set.Ioi y) \ (∅ : Set ℂ)),
          DifferentiableAt ℂ f z := by
      intro z hz
      exact hdiff z (by simpa using hz.1)
    simpa using
      (Complex.hzero (f := f) (x₁ := x₁) (x₂ := x₂) (y := y) hcont (s := (∅ : Set ℂ))
        (hs := by simp) hdiff' m hm)
  have hEq :
      (fun m : ℝ =>
          (∫ x in x₁..x₂, f ((x : ℂ) + (y : ℂ) * I)) +
              (I • ∫ t in y..m, f ((x₂ : ℂ) + (t : ℂ) * I)) -
                (I • ∫ t in y..m, f ((x₁ : ℂ) + (t : ℂ) * I))) =ᶠ[atTop]
        fun m : ℝ => ∫ x in x₁..x₂, f ((x : ℂ) + (m : ℂ) * I) := by
    filter_upwards [eventually_ge_atTop y] with m hm
    have h0 := hrect m hm
    have h1 :=
      congrArg (fun z : E => z + ∫ x in x₁..x₂, f ((x : ℂ) + (m : ℂ) * I)) h0
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h1
  have hF0 :
      Tendsto
          (fun m : ℝ =>
            (∫ x in x₁..x₂, f ((x : ℂ) + (y : ℂ) * I)) +
                (I • ∫ t in y..m, f ((x₂ : ℂ) + (t : ℂ) * I)) -
                  (I • ∫ t in y..m, f ((x₁ : ℂ) + (t : ℂ) * I))) atTop (𝓝 0) :=
    (tendsto_congr' hEq).2 htop
  have hV₁ :
      Tendsto (fun m : ℝ => ∫ t in y..m, f ((x₁ : ℂ) + (t : ℂ) * I)) atTop
        (𝓝 (∫ t in Set.Ioi y, f ((x₁ : ℂ) + (t : ℂ) * I))) :=
    intervalIntegral_tendsto_integral_Ioi y hint₁ tendsto_id
  have hV₂ :
      Tendsto (fun m : ℝ => ∫ t in y..m, f ((x₂ : ℂ) + (t : ℂ) * I)) atTop
        (𝓝 (∫ t in Set.Ioi y, f ((x₂ : ℂ) + (t : ℂ) * I))) :=
    intervalIntegral_tendsto_integral_Ioi y hint₂ tendsto_id
  have hFlim :
      Tendsto
          (fun m : ℝ =>
            (∫ x in x₁..x₂, f ((x : ℂ) + (y : ℂ) * I)) +
                (I • ∫ t in y..m, f ((x₂ : ℂ) + (t : ℂ) * I)) -
                  (I • ∫ t in y..m, f ((x₁ : ℂ) + (t : ℂ) * I))) atTop
        (𝓝 ((∫ x in x₁..x₂, f ((x : ℂ) + (y : ℂ) * I)) +
              (I • ∫ t in Set.Ioi y, f ((x₂ : ℂ) + (t : ℂ) * I)) -
                (I • ∫ t in Set.Ioi y, f ((x₁ : ℂ) + (t : ℂ) * I)))) := by
    have hV₁' := hV₁.const_smul I
    have hV₂' := hV₂.const_smul I
    exact (tendsto_const_nhds.add hV₂').sub hV₁'
  have :
      (∫ x in x₁..x₂, f ((x : ℂ) + (y : ℂ) * I)) +
            (I • ∫ t in Set.Ioi y, f ((x₂ : ℂ) + (t : ℂ) * I)) -
              (I • ∫ t in Set.Ioi y, f ((x₁ : ℂ) + (t : ℂ) * I)) = (0 : E) :=
    tendsto_nhds_unique hFlim hF0
  simpa using this

end Contour_Deformation_Tendsto_Top

end Complex
