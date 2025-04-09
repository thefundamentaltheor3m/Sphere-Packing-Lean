import Mathlib

/-! # Deforming Paths of Integration for Open Contours

In this file, we prove that if a function tends to zero as the imaginary part of its input tends to
infinity, then
-/

open Set Real Complex intervalIntegral Metric Filter MeasureTheory

open scoped Interval Topology

namespace Complex

section aux

-- WHY ARE THESE NOT JUST `exact?`????!!!!
theorem re_of_real_add_real_mul_I (x y : ℝ) : (x + y * I).re = x := by simp
theorem im_of_real_add_real_mul_I (x y : ℝ) : (x + y * I).im = y := by simp

end aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℂ → E} (x₁ x₂ y : ℝ) (hlt : x₁ < x₂) (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y)))
  -- (htendsto : ∀ (x : ℝ), Tendsto (fun (y : ℝ) ↦ f (x + y * I)) atTop (𝓝 0)) -- This is rubbish
  -- How do I express the following condition using filters? Is it even possible?
  (htendsto : ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖f z‖ < ε)
  (s : Set ℂ) (hs : s.Countable)
  (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Iio y)) \ s, DifferentiableAt ℂ f x)

omit [CompleteSpace E] in
include htendsto in
/-- If $f(z) \to 0$ as $\Im(z) \to \infty$, then
  $\lim_{m \to \infty} \int_{x_1}^{x_2} f(x + mI) dx = 0$. -/
lemma tendsto_integral_atTop_nhds_zero_of_tendsto_im_atTop_nhds_zero :
    Tendsto (fun (m : ℝ) ↦ ∫ (x : ℝ) in x₁..x₂, f (x + m * I)) atTop (𝓝 0) := by
  wlog hne : x₁ ≠ x₂
  · rw [ne_eq, Decidable.not_not] at hne
    simp only [hne, integral_same, tendsto_const_nhds_iff]
  simp only [NormedAddCommGroup.tendsto_nhds_zero, eventually_atTop, ge_iff_le]
  intro ε hε
  obtain ⟨M, hM⟩ := htendsto ((1 / 2) * (ε / |x₂ - x₁|)) <| by
    simp only [one_div, gt_iff_lt, inv_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
    exact (div_pos hε (abs_sub_pos.mpr hne.symm))
  use M
  intro y hy
  calc ‖∫ (x : ℝ) in x₁..x₂, f (↑x + ↑y * I)‖
  _ ≤ ((1 / 2) * (ε / |x₂ - x₁|)) * |x₂ - x₁| :=
      intervalIntegral.norm_integral_le_of_norm_le_const <| by
      intro x hx
      specialize hM (x + y * I)
      rw [im_of_real_add_real_mul_I x y] at hM
      exact le_of_lt (hM hy)
  _ = (1 / 2) * ε := by
      rw [mul_assoc]
      have : 0 ≠ |x₂ - x₁| := ne_of_lt (abs_sub_pos.mpr hne.symm)
      field_simp [this]
  _ < ε := by linarith

example (x : E) : Tendsto (fun (_ : ℝ) ↦ 0) atTop (𝓝 x) → x = 0 := by
  rw [tendsto_const_nhds_iff]
  exact Eq.symm

#check integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
#check intervalIntegral_tendsto_integral_Ioi

include hlt hcont htendsto s hs hdiff in
theorem integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable :
    (∫ (x : ℝ) in x₁..x₂, f (x + y * I))
    + (I • ∫ (t : ℝ) in Ioi y, f (x₂ + t * I))
    - (I • ∫ (t : ℝ) in Ioi y, f (x₁ + t * I))
    = 0 := by
  symm
  rw [← tendsto_const_nhds_iff (X := E) (Y := ℝ) (l := atTop) (c := 0)]
  have hzero : (fun (m : ℝ) ↦
      (∫ (x : ℝ) in x₁..x₂, f (x + y * I))
      - (∫ (x : ℝ) in x₁..x₂, f (x + m * I))
      + (I • ∫ (t : ℝ) in y..m, f (x₂ + t * I))
      - (I • ∫ (t : ℝ) in y..m, f (x₁ + t * I)))
    = (fun (m : ℝ) ↦ 0) := by
    ext m
    calc _
    _ = (((∫ (t : ℝ) in (x₁ + y * I).re..(x₂ + m * I).re, f (t + (x₁ + y * I).im * I))
        - ∫ (t : ℝ) in (x₁ + y * I).re..(x₂ + m * I).re, f (t + (x₂ + m * I).im * I))
        + I • ∫ (t : ℝ) in (x₁ + y * I).im..(x₂ + m * I).im, f ((x₂ + m * I).re + t * I))
        - I • ∫ (t : ℝ) in (x₁ + y * I).im..(x₂ + m * I).im, f ((x₁ + y * I).re + t * I) := by
      simp only [re_of_real_add_real_mul_I x₁ y, re_of_real_add_real_mul_I x₂ m,
                 im_of_real_add_real_mul_I x₁ y, im_of_real_add_real_mul_I x₂ m]
    _ = 0 := by
      refine Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
        f (x₁ + y * I) (x₂ + m * I) s hs ?_ ?_ <;>
      simp only [re_of_real_add_real_mul_I x₁ y, re_of_real_add_real_mul_I x₂ m,
                 im_of_real_add_real_mul_I x₁ y, im_of_real_add_real_mul_I x₂ m]
      · apply continuousOn_of_forall_continuousAt
        intro z hz
        specialize hcont z
        sorry
      · intro z hz
        specialize hdiff z
        sorry
  rw [← hzero]
  refine Tendsto.sub (Tendsto.add (Tendsto.sub ?_ ?_) ?_) ?_
  · exact tendsto_const_nhds_iff.mpr (integral_of_le (le_of_lt hlt))
  · have : (∫ (x : ℝ) in Ioc x₂ x₁, (fun x ↦ f (↑x + ↑y * I)) x ∂volume) = 0 := by
      refine setIntegral_zero_measure (α := ℝ) (fun x ↦ f (↑x + ↑y * I)) ?_
      simp only [volume_Ioc, ENNReal.ofReal_eq_zero, tsub_le_iff_right, zero_add]
      exact le_of_lt hlt
    rw [this]
    exact tendsto_integral_atTop_nhds_zero_of_tendsto_im_atTop_nhds_zero x₁ x₂ htendsto
  -- For the last two, we need `intervalIntegral_tendsto_integral_Ioi`.
  · sorry
  ·
    -- refine MeasureTheory.intervalIntegral_tendsto_integral_Ioi
    --   (f := fun t ↦ f (x₁ + t * I)) y ?_ tendsto_id

    sorry

#check Tendsto.add
#check Tendsto.sub
#check Filter.tendsto_id
