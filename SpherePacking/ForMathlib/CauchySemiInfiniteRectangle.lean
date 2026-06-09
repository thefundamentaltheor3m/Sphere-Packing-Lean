/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Cauchy's theorem on a semi-infinite rectangle

A self-contained variant of Cauchy's theorem on the closed semi-infinite rectangle
`[a, b] × [c, ∞)`, derived directly from mathlib's closed-rectangle Cauchy theorem
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` by passing to the
limit as the rectangle height `R → ∞`.

This file vendors the result `cauchy_semi_infinite_rectangle_eq` so that the
sphere-packing project does not need to depend on `LeanModularForms` for it.

## Main result

* `SpherePacking.ForMathlib.cauchy_semi_infinite_rectangle_eq`: for a holomorphic
  function `f` on a convex open set containing the closed strip `[a, b] × [c, ∞)`,
  if the top-edge integral vanishes as the height tends to infinity, then the
  bottom horizontal integral equals the difference of the two upward vertical
  integrals (as an identity that the four-term combination is zero).
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real Interval

namespace SpherePacking.ForMathlib

noncomputable section

/-- **Cauchy's theorem on a semi-infinite rectangle.** For a holomorphic
function `f` on a convex open set `U` containing the closed semi-infinite
rectangle `[a, b] × [c, ∞)`, if `f`'s integral over the top horizontal segment
`[a, b] × {R}` tends to `0` as `R → ∞`, then the bottom horizontal integral
equals the difference of the two upward vertical integrals:

  `∫ x in a..b, f(x + ci) + (∫ y in Ioi c, f(b + yi))·I - (∫ y in Ioi c, f(a + yi))·I = 0`.

The proof applies mathlib's closed-rectangle Cauchy theorem to `[a, b] × [c, R]`
for each `R > c` and passes to the limit.
-/
public theorem cauchy_semi_infinite_rectangle_eq
    {a b c : ℝ} (hab : a < b)
    {U : Set ℂ} (_hU_open : IsOpen U) (_hU_convex : Convex ℝ U)
    (h_strip_in_U : ∀ x ∈ Set.Icc a b, ∀ y, c ≤ y → (x : ℂ) + y * Complex.I ∈ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (h_top_vanish : Filter.Tendsto
      (fun R : ℝ => ∫ x in a..b, f ((x : ℂ) + R * Complex.I)) Filter.atTop (𝓝 0))
    (h_int_b : MeasureTheory.IntegrableOn
      (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * Complex.I)) (Set.Ioi c))
    (h_int_a : MeasureTheory.IntegrableOn
      (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) (Set.Ioi c)) :
    (∫ x in a..b, f ((x : ℂ) + c * Complex.I))
      + (∫ y in Set.Ioi c, f ((b : ℂ) + (y : ℂ) * Complex.I)) * Complex.I
      - (∫ y in Set.Ioi c, f ((a : ℂ) + (y : ℂ) * Complex.I)) * Complex.I = 0 := by
  -- Step 1: the closed-rectangle identity for each finite height `R > c`.
  -- mathlib's `integral_boundary_rect_eq_zero_of_differentiableOn` applied to
  -- `z := a + c·I`, `w := b + R·I` gives a four-term identity.
  have h_eq : ∀ᶠ R : ℝ in atTop,
      (∫ x in a..b, f ((x : ℂ) + c * Complex.I))
        - (∫ x in a..b, f ((x : ℂ) + R * Complex.I))
        + Complex.I • (∫ y in c..R, f ((b : ℂ) + y * Complex.I))
        - Complex.I • (∫ y in c..R, f ((a : ℂ) + y * Complex.I)) = 0 := by
    filter_upwards [Filter.eventually_gt_atTop c] with R hcR
    have h_subset : (Set.uIcc a b) ×ℂ (Set.uIcc c R) ⊆ U := by
      rw [Set.uIcc_of_le hab.le, Set.uIcc_of_le hcR.le]
      intro z hz
      rw [Complex.mem_reProdIm] at hz
      obtain ⟨hx, hy⟩ := hz
      -- Decompose `z = (z.re : ℂ) + z.im * I` and apply the strip hypothesis.
      rw [← Complex.re_add_im z]
      exact h_strip_in_U z.re hx z.im hy.1
    have h_re_a : ((a : ℂ) + c * Complex.I).re = a := by simp
    have h_re_b : ((b : ℂ) + R * Complex.I).re = b := by simp
    have h_im_a : ((a : ℂ) + c * Complex.I).im = c := by simp
    have h_im_b : ((b : ℂ) + R * Complex.I).im = R := by simp
    have h_diff : DifferentiableOn ℂ f
        ((Set.uIcc ((a : ℂ) + c * Complex.I).re ((b : ℂ) + R * Complex.I).re) ×ℂ
         (Set.uIcc ((a : ℂ) + c * Complex.I).im ((b : ℂ) + R * Complex.I).im)) := by
      rw [h_re_a, h_re_b, h_im_a, h_im_b]
      exact hf.mono h_subset
    have h_cauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      f ((a : ℂ) + c * Complex.I) ((b : ℂ) + R * Complex.I) h_diff
    rw [h_re_a, h_re_b, h_im_a, h_im_b] at h_cauchy
    -- `h_cauchy` matches the goal up to associativity of `+`/`-`.
    linear_combination h_cauchy
  -- Step 2: take the limit `R → ∞`.
  -- The horizontal bottom integral is constant.
  -- The horizontal top integral tends to `0` (by `h_top_vanish`).
  -- The vertical integrals tend to their `Set.Ioi c` counterparts.
  have h_lim_right : Tendsto
      (fun R : ℝ => ∫ y in c..R, f ((b : ℂ) + y * Complex.I)) atTop
      (𝓝 (∫ y in Set.Ioi c, f ((b : ℂ) + y * Complex.I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi c h_int_b Filter.tendsto_id
  have h_lim_left : Tendsto
      (fun R : ℝ => ∫ y in c..R, f ((a : ℂ) + y * Complex.I)) atTop
      (𝓝 (∫ y in Set.Ioi c, f ((a : ℂ) + y * Complex.I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi c h_int_a Filter.tendsto_id
  have h_lim_right_I :
      Tendsto (fun R : ℝ => Complex.I • (∫ y in c..R, f ((b : ℂ) + y * Complex.I))) atTop
      (𝓝 (Complex.I • (∫ y in Set.Ioi c, f ((b : ℂ) + y * Complex.I)))) :=
    h_lim_right.const_smul Complex.I
  have h_lim_left_I :
      Tendsto (fun R : ℝ => Complex.I • (∫ y in c..R, f ((a : ℂ) + y * Complex.I))) atTop
      (𝓝 (Complex.I • (∫ y in Set.Ioi c, f ((a : ℂ) + y * Complex.I)))) :=
    h_lim_left.const_smul Complex.I
  have h_lim_bottom :
      Tendsto (fun _ : ℝ => ∫ x in a..b, f ((x : ℂ) + c * Complex.I)) atTop
      (𝓝 (∫ x in a..b, f ((x : ℂ) + c * Complex.I))) := tendsto_const_nhds
  have h_lim_total :
      Tendsto
        (fun R : ℝ =>
          (∫ x in a..b, f ((x : ℂ) + c * Complex.I))
            - (∫ x in a..b, f ((x : ℂ) + R * Complex.I))
            + Complex.I • (∫ y in c..R, f ((b : ℂ) + y * Complex.I))
            - Complex.I • (∫ y in c..R, f ((a : ℂ) + y * Complex.I))) atTop
        (𝓝 ((∫ x in a..b, f ((x : ℂ) + c * Complex.I))
              - 0
              + Complex.I • (∫ y in Set.Ioi c, f ((b : ℂ) + y * Complex.I))
              - Complex.I • (∫ y in Set.Ioi c, f ((a : ℂ) + y * Complex.I)))) :=
    ((h_lim_bottom.sub h_top_vanish).add h_lim_right_I).sub h_lim_left_I
  have h_eventually_zero :
      Tendsto
        (fun R : ℝ =>
          (∫ x in a..b, f ((x : ℂ) + c * Complex.I))
            - (∫ x in a..b, f ((x : ℂ) + R * Complex.I))
            + Complex.I • (∫ y in c..R, f ((b : ℂ) + y * Complex.I))
            - Complex.I • (∫ y in c..R, f ((a : ℂ) + y * Complex.I))) atTop (𝓝 0) :=
    Tendsto.congr' (h_eq.mono fun _ h => h.symm) tendsto_const_nhds
  have h_eq_lim : (∫ x in a..b, f ((x : ℂ) + c * Complex.I))
        - 0
        + Complex.I • (∫ y in Set.Ioi c, f ((b : ℂ) + y * Complex.I))
        - Complex.I • (∫ y in Set.Ioi c, f ((a : ℂ) + y * Complex.I)) = 0 :=
    tendsto_nhds_unique h_lim_total h_eventually_zero
  -- Rearrange `I • z = z * I`.
  simp only [smul_eq_mul, mul_comm Complex.I] at h_eq_lim
  linear_combination h_eq_lim

end

end SpherePacking.ForMathlib
