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
      field_simp [mul_assoc, (show (|x₂ - x₁| : ℝ) ≠ 0 from ne_of_gt hx)]
  _ < ε := by linarith

end Tendsto_Zero

section Eventually_Eq_Zero

lemma hzero (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y))) (s : Set ℂ) (hs : s.Countable)
    (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Ioi y)) \ s, DifferentiableAt ℂ f x)
    (m : ℝ) (hm : m ≥ y) :
    (∫ (x : ℝ) in x₁..x₂, f (x + y * I)) - (∫ (x : ℝ) in x₁..x₂, f (x + m * I))
      + (I • ∫ (t : ℝ) in y..m, f (x₂ + t * I)) - (I • ∫ (t : ℝ) in y..m, f (x₁ + t * I))
    = 0 := by
  simpa [re_of_real_add_real_mul_I, im_of_real_add_real_mul_I] using
    Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f (x₁ + y * I)
      (x₂ + m * I) s hs
      (hcont.mono (by
        rw [reProdIm_subset_iff]
        gcongr
        · simp
        · simpa [re_of_real_add_real_mul_I, im_of_real_add_real_mul_I, uIcc_of_le hm] using
            (Icc_subset_Ici_self : Icc y m ⊆ Ici y)))
      (fun z hz => by
        obtain ⟨hz, hzns⟩ : z ∈ Ioo (min x₁ x₂) (max x₁ x₂) ×ℂ Ioo (min y m) (max y m) ∧ z ∉ s := by
          simpa [re_of_real_add_real_mul_I, im_of_real_add_real_mul_I] using hz
        refine hdiff z ⟨?_, hzns⟩
        rw [mem_reProdIm] at hz ⊢
        exact ⟨hz.1, by simpa [min_eq_left hm] using (mem_Ioo.1 hz.2).1⟩)

end Eventually_Eq_Zero

section Contour_Deformation_Tensdsto

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
  set C₁ := ∫ (t : ℝ) in Ioi y, f (x₁ + t * I)
  set C₂ := ∫ (t : ℝ) in Ioi y, f (x₂ + t * I)
  have hC₁ : Tendsto (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₁ + t * I)) atTop (𝓝 (I • C₁)) :=
    (intervalIntegral_tendsto_integral_Ioi y hint₁ tendsto_id).const_smul I
  have hC₂ : Tendsto (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₂ + t * I)) atTop (𝓝 (I • C₂)) :=
    (intervalIntegral_tendsto_integral_Ioi y hint₂ tendsto_id).const_smul I
  have heventually : (fun (m : ℝ) ↦
      (∫ (x : ℝ) in x₁..x₂, f (x + y * I))
        - (∫ (x : ℝ) in x₁..x₂, f (x + m * I))
        + (I • ∫ (t : ℝ) in y..m, f (x₂ + t * I)))
      =ᶠ[atTop] (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₁ + t * I)) := by
    filter_upwards [eventually_ge_atTop y] with m hm
    rw [← sub_eq_zero, ← (hzero y hcont s hs hdiff m hm)]
  have hC₁' : Tendsto (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₁ + t * I)) atTop
      (𝓝 ((∫ (t : ℝ) in x₁..x₂, f (t + y * I)) + I • C₂)) := by
    rw [tendsto_congr' heventually.symm, ← sub_zero (∫ (t : ℝ) in x₁..x₂, f (↑t + ↑y * I))]
    refine (Tendsto.sub ?_ ?_).add hC₂
    · rw [sub_zero, tendsto_const_nhds_iff]
    · exact tendsto_integral_atTop_nhds_zero_of_tendsto_im_atTop_nhds_zero htendsto
  exact sub_eq_zero.2 (tendsto_nhds_unique hC₁ hC₁').symm

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
  have hEq :
      (fun m : ℝ =>
          (∫ x in x₁..x₂, f ((x : ℂ) + (y : ℂ) * I)) +
              (I • ∫ t in y..m, f ((x₂ : ℂ) + (t : ℂ) * I)) -
                (I • ∫ t in y..m, f ((x₁ : ℂ) + (t : ℂ) * I))) =ᶠ[atTop]
        fun m : ℝ => ∫ x in x₁..x₂, f ((x : ℂ) + (m : ℂ) * I) := by
    filter_upwards [eventually_ge_atTop y] with m hm
    have hdiff' :
        ∀ z ∈ ((Set.Ioo (min x₁ x₂) (max x₁ x₂) ×ℂ Set.Ioi y) \ (∅ : Set ℂ)),
          DifferentiableAt ℂ f z :=
      fun z hz => hdiff z (by simpa using hz.1)
    have hr := Complex.hzero (f := f) (x₁ := x₁) (x₂ := x₂) (y := y) hcont (s := (∅ : Set ℂ))
      (hs := by simp) hdiff' m hm
    grind only
  have hV₁ := (intervalIntegral_tendsto_integral_Ioi y hint₁ tendsto_id).const_smul I
  have hV₂ := (intervalIntegral_tendsto_integral_Ioi y hint₂ tendsto_id).const_smul I
  simpa using tendsto_nhds_unique
    ((tendsto_const_nhds.add hV₂).sub hV₁) ((tendsto_congr' hEq).2 htop)

end Contour_Deformation_Tendsto_Top

end Complex
