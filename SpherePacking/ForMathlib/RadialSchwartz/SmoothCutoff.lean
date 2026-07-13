/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module


public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

@[expose] public section

/-! # Schwartz functions from smoothness and decay on a right half-line

The radial components `I₁', …, I₆', J₁', …, J₆' : ℝ → ℂ` of the integrals defining Viazovska's
magic function are only well-behaved on a right half-line: each is smooth on `(a, ∞)` for a
suitable `a < 0` and decays rapidly (together with all derivatives) on `[0, ∞)`, but grows
exponentially (or is a junk value) far to the left of the origin. They are therefore *not*
Schwartz functions as stated. However, only their values on `[0, ∞)` matter, because the
corresponding functions on `ℝ⁸` are obtained by composing with `‖·‖ ^ 2 ≥ 0`.

This file provides the bridge: multiplying by a smooth transition function that vanishes on
`(-∞, a/2]` and is identically `1` on `[0, ∞)` produces a genuine Schwartz function agreeing with
the original function on `[0, ∞)`.

## Main definitions and results

* `exists_smooth_cutoff`: there is a smooth `f : ℝ → ℝ` with `f = 0` on `(-∞, -1]` and `f = 1` on
  `[0, ∞)`. This is the statement of PR #316 (Matt Cushman); here it is obtained directly from
  mathlib's `Real.smoothTransition`.
* `SchwartzMap.ofNonnegDecay`: the Schwartz function obtained from `f : ℝ → E` (smooth on
  `(a, ∞)`, `a < 0`, with Schwartz-type decay on `[0, ∞)`) by multiplying with the smooth
  transition function `x ↦ Real.smoothTransition (1 - 2 * x / a)`, which vanishes on `(-∞, a/2]`
  and equals `1` on `[0, ∞)`.
* `SchwartzMap.ofNonnegDecay_apply_of_nonneg`: `SchwartzMap.ofNonnegDecay` agrees with `f` on
  `[0, ∞)`.
-/

open Real Set Filter
open scoped ContDiff Topology

/-- There exists a smooth transition function that is identically `0` on `(-∞, -1]` and
identically `1` on `[0, ∞)`. This is the statement of PR #316 (Matt Cushman), obtained here from
mathlib's `Real.smoothTransition`. -/
theorem exists_smooth_cutoff :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ (∀ x : ℝ, x ≤ -1 → f x = 0) ∧ ∀ x : ℝ, x ≥ 0 → f x = 1 :=
  ⟨fun x ↦ smoothTransition (x + 1),
    smoothTransition.contDiff.comp (contDiff_id.add contDiff_const),
    fun _ hx ↦ smoothTransition.zero_of_nonpos (by linarith),
    fun _ hx ↦ smoothTransition.one_of_one_le (by linarith)⟩

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ℝ → E} {a : ℝ}

section TransitionLemmas

/- The rescaled transition function `x ↦ Real.smoothTransition (1 - 2 * x / a)` (for `a < 0`)
vanishes on `(-∞, a/2]`, is identically `1` on `[0, ∞)` and transitions smoothly in between.
For `a = -2` this is exactly `x ↦ Real.smoothTransition (x + 1)`, transitioning on `[-1, 0]`. -/

private lemma transition_eq_zero (ha : a < 0) {x : ℝ} (hx : x ≤ a / 2) :
    smoothTransition (1 - 2 * x / a) = 0 :=
  smoothTransition.zero_of_nonpos <| by rw [sub_nonpos, le_div_iff_of_neg ha]; linarith

private lemma transition_eq_one (ha : a < 0) {x : ℝ} (hx : 0 ≤ x) :
    smoothTransition (1 - 2 * x / a) = 1 :=
  smoothTransition.one_of_one_le <| by
    have h2 : 2 * x / a ≤ 0 := div_nonpos_iff.2 (.inl ⟨by linarith, ha.le⟩)
    linarith

private lemma eventuallyEq_zero (ha : a < 0) {x : ℝ} (hx : x < a / 2) :
    (fun x ↦ smoothTransition (1 - 2 * x / a) • f x) =ᶠ[𝓝 x] fun _ ↦ (0 : E) := by
  filter_upwards [Iio_mem_nhds hx] with y hy
  rw [transition_eq_zero ha hy.le, zero_smul]

private lemma eventuallyEq_self (ha : a < 0) {x : ℝ} (hx : 0 < x) :
    (fun x ↦ smoothTransition (1 - 2 * x / a) • f x) =ᶠ[𝓝 x] f := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  rw [transition_eq_one ha hy.le, one_smul]

private lemma contDiff_transition_smul (ha : a < 0) (hf : ContDiffOn ℝ ∞ f (Ioi a)) :
    ContDiff ℝ ∞ fun x ↦ smoothTransition (1 - 2 * x / a) • f x := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge a x with hx | hx
  · have h1 : ContDiffAt ℝ ∞ (fun x : ℝ ↦ smoothTransition (1 - 2 * x / a)) x :=
      (smoothTransition.contDiff.comp
        (by fun_prop : ContDiff ℝ ∞ fun x : ℝ ↦ 1 - 2 * x / a)).contDiffAt
    exact h1.smul (hf.contDiffAt (isOpen_Ioi.mem_nhds hx))
  · exact contDiffAt_const.congr_of_eventuallyEq
      (eventuallyEq_zero ha (hx.trans_lt (by linarith)))

private lemma decay_transition_smul (ha : a < 0) (hf : ContDiffOn ℝ ∞ f (Ioi a))
    (hdecay : ∀ k n : ℕ, ∃ C, ∀ x ≥ (0 : ℝ), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) (k n : ℕ) :
    ∃ C, ∀ x, ‖x‖ ^ k *
      ‖iteratedFDeriv ℝ n (fun x ↦ smoothTransition (1 - 2 * x / a) • f x) x‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := a / 2) (b := 1)).exists_bound_of_continuousOn
    (((contDiff_transition_smul ha hf).continuous_iteratedFDeriv
      (mod_cast le_top)).continuousOn)
  obtain ⟨C₂, hC₂⟩ := hdecay k n
  have hC₁0 : (0 : ℝ) ≤ C₁ := (norm_nonneg _).trans (hC₁ 0 ⟨by linarith, zero_le_one⟩)
  refine ⟨max ((1 + |a|) ^ k * C₁) C₂, fun x ↦ ?_⟩
  rcases lt_or_ge x (a / 2) with hx | hx
  · -- On `(-∞, a/2)` the product vanishes identically, so all its derivatives vanish.
    have h0 : iteratedFDeriv ℝ n (fun x ↦ smoothTransition (1 - 2 * x / a) • f x) x = 0 := by
      rw [((eventuallyEq_zero ha hx).iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_fun_zero,
        Pi.zero_apply]
    rw [h0, norm_zero, mul_zero]
    exact le_max_of_le_left (mul_nonneg (by positivity) hC₁0)
  rcases le_or_lt x 1 with hx1 | hx1
  · -- On the compact interval `[a/2, 1]` we use continuity of the iterated derivatives.
    refine le_max_of_le_left ?_
    have hxa : ‖x‖ ≤ 1 + |a| := by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [neg_abs_le a, abs_nonneg a], by linarith [abs_nonneg a]⟩
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxa _) (hC₁ x ⟨hx, hx1⟩) (norm_nonneg _)
      (by positivity)
  · -- On `(1, ∞)` the product agrees with `f` near `x`, so the decay hypothesis applies.
    have heq : iteratedFDeriv ℝ n (fun x ↦ smoothTransition (1 - 2 * x / a) • f x) x
        = iteratedFDeriv ℝ n f x :=
      ((eventuallyEq_self ha (one_pos.trans hx1)).iteratedFDeriv ℝ n).eq_of_nhds
    rw [heq]
    exact le_max_of_le_right (hC₂ x (by linarith))

end TransitionLemmas

/-- The Schwartz function obtained from a function `f : ℝ → E` that is smooth on `(a, ∞)` for
some `a < 0` and has Schwartz-type decay on `[0, ∞)`, by multiplying with a smooth transition
function that vanishes on `(-∞, a/2]` and is identically `1` on `[0, ∞)`. It agrees with `f` on
`[0, ∞)`: see `SchwartzMap.ofNonnegDecay_apply_of_nonneg`. -/
noncomputable def ofNonnegDecay (f : ℝ → E) (a : ℝ) (ha : a < 0)
    (hf : ContDiffOn ℝ ∞ f (Ioi a))
    (hdecay : ∀ k n : ℕ, ∃ C, ∀ x ≥ (0 : ℝ), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    𝓢(ℝ, E) where
  toFun x := smoothTransition (1 - 2 * x / a) • f x
  smooth' := contDiff_transition_smul ha hf
  decay' := decay_transition_smul ha hf hdecay

theorem ofNonnegDecay_apply_of_nonneg {ha : a < 0} {hf : ContDiffOn ℝ ∞ f (Ioi a)}
    {hdecay : ∀ k n : ℕ, ∃ C, ∀ x ≥ (0 : ℝ), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C}
    {x : ℝ} (hx : 0 ≤ x) : ofNonnegDecay f a ha hf hdecay x = f x := by
  show smoothTransition (1 - 2 * x / a) • f x = f x
  rw [transition_eq_one ha hx, one_smul]

theorem ofNonnegDecay_apply_of_le_half {ha : a < 0} {hf : ContDiffOn ℝ ∞ f (Ioi a)}
    {hdecay : ∀ k n : ℕ, ∃ C, ∀ x ≥ (0 : ℝ), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C}
    {x : ℝ} (hx : x ≤ a / 2) : ofNonnegDecay f a ha hf hdecay x = 0 := by
  show smoothTransition (1 - 2 * x / a) • f x = 0
  rw [transition_eq_zero ha hx, zero_smul]

end SchwartzMap
