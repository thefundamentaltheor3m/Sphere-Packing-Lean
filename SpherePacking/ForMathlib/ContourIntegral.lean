import Mathlib

/-! # Deforming Paths of Integration for Open Contours

In this file, we prove that if a function tends to zero as the imaginary part of its input tends to
infinity, then
-/

#check Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable

open Set Real Complex intervalIntegral Metric Filter

open scoped Interval Topology

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (f : ℂ → E) (x₁ x₂ y : ℝ) (hne : x₁ ≠ x₂) (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y)))
  -- (htendsto : ∀ (x : ℝ), Tendsto (fun (y : ℝ) ↦ f (x + y * I)) atTop (𝓝 0)) -- This is rubbish
  -- How do I express the following condition using filters? Is it even possible?
  (htendsto : ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖f z‖ < ε)
  (s : Set ℂ) (hs : s.Countable)
  (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Iio y)) \ s, DifferentiableAt ℂ f x)

omit [CompleteSpace E] in
include hne htendsto in  -- Can I also do cases on whether x₁ = x₂? This would remove `hne`
lemma tendsto_integral_atTop_nhds_zero_of_tendsto_im_atTop_nhds_zero :
    Tendsto (fun (m : ℝ) ↦ ∫ (x : ℝ) in x₁..x₂, f (x + m * I)) atTop (𝓝 0) := by
  simp only [NormedAddCommGroup.tendsto_nhds_zero, eventually_atTop, ge_iff_le]
  intro ε hε
  obtain ⟨M, hM⟩ := htendsto ((1 / 2) * (ε / |x₂ - x₁|)) <| by
    simp only [one_div, gt_iff_lt, inv_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
    exact (div_pos hε (abs_sub_pos.mpr hne.symm))
  use M
  intro y hy
  have him (x : ℝ) : (x + y * I).im = y := by simp -- I think `ringI` should also be able to do this
  calc ‖∫ (x : ℝ) in x₁..x₂, f (↑x + ↑y * I)‖
  _ ≤ ((1 / 2) * (ε / |x₂ - x₁|)) * |x₂ - x₁| :=
      intervalIntegral.norm_integral_le_of_norm_le_const <| by
      intro x hx
      specialize hM (x + y * I)
      rw [him x] at hM
      exact le_of_lt (hM hy)
  _ = (1 / 2) * ε := by
      rw [mul_assoc]
      have : 0 ≠ |x₂ - x₁| := ne_of_lt (abs_sub_pos.mpr hne.symm)
      field_simp [this]
  _ < ε := by linarith



-- theorem integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable
