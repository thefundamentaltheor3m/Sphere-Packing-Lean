/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import SpherePacking.ModularForms.Monotonicity_ImagAxis
import SpherePacking.ModularForms.Monotonicity_L10_GAndEventuallyPos

/-!
# Monotonicity of Q = F/G on the Imaginary Axis

This file proves Proposition 8.12 from the blueprint: the function
`Q(t) = F(it)/G(it)` is strictly decreasing on `(0, ∞)`.

## Main definitions

* `MonotoneFG.Q` : The function `Q(t) = F(it)/G(it)` restricted to `t > 0`

## Main results

* `MonotoneFG.L₁₀_pos_imag_axis` : `L₁,₀(it) > 0` for all `t > 0`
* `MonotoneFG.Q_strictAntiOn` : `Q` is strictly decreasing on `(0, ∞)`

## Blueprint references

* Definition 8.3: Definitions of F and G (see `FG.lean`)
* Lemma 8.8: Differential equations (65) and (66)
* Corollary 8.9: Positivity of RHS of (65) and (66) on imaginary axis
* Proposition 8.12: Monotonicity of Q

## Structure

The proof is organized across three files:
- `Monotonicity_ImagAxis.lean`: Positivity and realness on imaginary axis (Section 0-2)
- `Monotonicity_L10.lean`: L₁₀ Wronskian and Serre derivative analysis (Section 3-6)
- `Monotonicity.lean` (this file): Final composition (Section 7)
-/

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap

open scoped ModularForm MatrixGroups Manifold ArithmeticFunction.sigma

namespace MonotoneFG

/-!
## Section 7: L₁,₀ Positivity and Monotonicity of Q = F/G

The main result `L₁₀_pos_imag_axis` follows from `antiSerreDerPos` (Theorem 6.54)
applied to the Serre derivative positivity and eventual positivity from the L10 file.
-/

/--
`L₁,₀(it) > 0` for all `t > 0`.
Blueprint: Apply Theorem 6.54 (antiSerreDerPos) with k = 22.
-/
theorem L₁₀_pos_imag_axis : ResToImagAxis.Pos L₁₀ := by
  -- Apply antiSerreDerPos (Theorem 6.54) with k = 22
  -- Requires: (1) serre_D 22 L₁₀ is positive on imaginary axis
  --           (2) L₁₀ is eventually positive on imaginary axis
  exact antiSerreDerPos serre_D_L₁₀_pos_imag_axis L₁₀_eventually_pos_imag_axis

/--
The function `Q(t) = Re(F(it)/G(it))` for `t > 0`.
Since F(it) and G(it) are both positive reals, Q(t) = F(it)/G(it) as real numbers.
-/
noncomputable def Q (t : ℝ) : ℝ :=
  if ht : 0 < t then
    (F ⟨Complex.I * t, by simp [ht]⟩).re / (G ⟨Complex.I * t, by simp [ht]⟩).re
  else 0

/--
`Q(t) = F(it)/G(it)` equals the real quotient for `t > 0`.
-/
theorem Q_eq_F_div_G (t : ℝ) (ht : 0 < t) :
    Q t = (F ⟨Complex.I * t, by simp [ht]⟩).re / (G ⟨Complex.I * t, by simp [ht]⟩).re := by
  simp [Q, ht]

/--
`Q` is differentiable on `(0, ∞)`.
Proof: Q(t) = F(it).re / G(it).re is a quotient of differentiable functions where the denominator
is positive (from G_imag_axis_pos).

Key steps:
1. F and G are MDifferentiable (F_holo, G_holo)
2. ResToImagAxis.Differentiable gives differentiability of F.resToImagAxis and G.resToImagAxis
3. Complex.reCLM extracts real parts differentiably
4. Quotient rule applies since G.resToImagAxis(t).re > 0 (from G_imag_axis_pos)
5. Q coincides with this quotient on (0,∞) by definition
-/
theorem Q_differentiableOn : DifferentiableOn ℝ Q (Set.Ioi 0) := by
  intro t ht
  simp only [Set.mem_Ioi] at ht
  -- F.resToImagAxis and G.resToImagAxis are differentiable at t
  have hF_diff : DifferentiableAt ℝ F.resToImagAxis t := ResToImagAxis.Differentiable F F_holo t ht
  have hG_diff : DifferentiableAt ℝ G.resToImagAxis t := ResToImagAxis.Differentiable G G_holo t ht
  -- Their real parts are also differentiable
  have hF_re_diff : DifferentiableAt ℝ (fun s => (F.resToImagAxis s).re) t :=
    Complex.reCLM.differentiableAt.comp t hF_diff
  have hG_re_diff : DifferentiableAt ℝ (fun s => (G.resToImagAxis s).re) t :=
    Complex.reCLM.differentiableAt.comp t hG_diff
  -- G.resToImagAxis(t).re > 0, hence ≠ 0
  have hG_pos := G_imag_axis_pos.2 t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte] at hG_pos
  have hG_ne_zero : (G.resToImagAxis t).re ≠ 0 := by
    simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte]
    exact ne_of_gt hG_pos
  -- Quotient is differentiable
  have hQ_diff_at : DifferentiableAt ℝ
      (fun s => (F.resToImagAxis s).re / (G.resToImagAxis s).re) t :=
    hF_re_diff.div hG_re_diff hG_ne_zero
  -- Q equals this quotient locally on (0, ∞)
  apply hQ_diff_at.differentiableWithinAt.congr_of_eventuallyEq_of_mem
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_Ioi] at hs
    simp only [Q, hs, ↓reduceDIte, Function.resToImagAxis_apply, ResToImagAxis]
  · simp only [Set.mem_Ioi, ht]

/--
The derivative of Q is `(-2π) * L₁,₀(it) / G(it)²`.
Blueprint: Quotient rule and chain rule.

Proof structure:
1. Q(t) = F(it).re / G(it).re for t > 0
2. By quotient rule: deriv Q = (F'·G - F·G') / G² (where F' = deriv of F.re on imaginary axis)
3. By chain rule: F' = -2π·(D F).re and G' = -2π·(D G).re
4. L₁₀ = D F · G - F · D G, so L₁₀.re = (D F).re · G.re - F.re · (D G).re
5. Combining: deriv Q = -2π · L₁₀.re / G.re²
-/
theorem deriv_Q (t : ℝ) (ht : 0 < t) :
    deriv Q t = (-2 * π) * (L₁₀ ⟨Complex.I * t, by simp [ht]⟩).re /
      (G ⟨Complex.I * t, by simp [ht]⟩).re ^ 2 := by
  -- Helper: z = I * t on the upper half-plane
  set z : ℍ := ⟨Complex.I * t, by simp [ht]⟩ with hz_def
  -- Differentiability of real parts
  have hF_diff : DifferentiableAt ℝ F.resToImagAxis t := ResToImagAxis.Differentiable F F_holo t ht
  have hG_diff : DifferentiableAt ℝ G.resToImagAxis t := ResToImagAxis.Differentiable G G_holo t ht
  have hF_re_diff : DifferentiableAt ℝ (fun s => (F.resToImagAxis s).re) t :=
    Complex.reCLM.differentiableAt.comp t hF_diff
  have hG_re_diff : DifferentiableAt ℝ (fun s => (G.resToImagAxis s).re) t :=
    Complex.reCLM.differentiableAt.comp t hG_diff
  -- G(it).re > 0, hence ≠ 0
  have hG_pos : 0 < (G z).re := by
    have h := G_imag_axis_pos.2 t ht
    simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte] at h
    exact h
  have hG_ne : (G z).re ≠ 0 := ne_of_gt hG_pos
  -- Q equals F.re / G.re locally
  have hQ_eq : Q =ᶠ[nhds t] (fun s => (F.resToImagAxis s).re / (G.resToImagAxis s).re) := by
    filter_upwards [lt_mem_nhds ht] with s hs
    simp only [Q, hs, ↓reduceDIte, Function.resToImagAxis_apply, ResToImagAxis]
  -- Apply quotient rule
  rw [hQ_eq.deriv_eq]
  have hdiv : deriv (fun s => (F.resToImagAxis s).re / (G.resToImagAxis s).re) t =
      (deriv (fun s => (F.resToImagAxis s).re) t * (G.resToImagAxis t).re -
       (F.resToImagAxis t).re * deriv (fun s => (G.resToImagAxis s).re) t) /
      (G.resToImagAxis t).re ^ 2 := by
    have hG_ne' : (G.resToImagAxis t).re ≠ 0 := by
      simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte]
      simp only [hz_def] at hG_ne
      exact hG_ne
    exact deriv_div hF_re_diff hG_re_diff hG_ne'
  rw [hdiv]
  -- Derivative of real part equals real part of derivative for F, G
  -- Using HasFDerivAt.comp_hasDerivAt: deriv (reCLM ∘ h) = reCLM ∘ deriv h
  have hF_deriv_re : deriv (fun s => (F.resToImagAxis s).re) t =
      (deriv F.resToImagAxis t).re :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hF_diff.hasDerivAt).deriv
  have hG_deriv_re : deriv (fun s => (G.resToImagAxis s).re) t =
      (deriv G.resToImagAxis t).re :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hG_diff.hasDerivAt).deriv
  -- Apply chain rule for resToImagAxis
  rw [hF_deriv_re, hG_deriv_re, deriv_resToImagAxis_eq F F_holo ht,
      deriv_resToImagAxis_eq G G_holo ht]
  -- Simplify using realness on imaginary axis
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, hz_def]
  -- F and G are real on the imaginary axis
  have hF_real := F_imag_axis_real t ht
  have hG_real := G_imag_axis_real t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte] at hF_real hG_real
  -- Use L₁₀ definition: L₁₀ = D F · G - F · D G
  have hL₁₀ := L₁₀_eq_FD_G_sub_F_DG z
  -- Simplify: (-2 * π : ℂ).im = 0 since π is real
  have h2pi_im : (-2 * (π : ℂ)).im = 0 := by simp
  have h2_re : (-2 : ℂ).re = -2 := by simp
  -- Unfold z
  simp only [hz_def] at hL₁₀ hF_real hG_real
  -- Final simplification
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, h2pi_im, h2_re]
  rw [hL₁₀]
  simp only [mul_re, sub_re]
  -- Since F.im = G.im = 0
  simp only [hF_real, hG_real, mul_zero, sub_zero, zero_mul]
  ring

/--
`deriv Q t < 0` for all `t > 0`.
Blueprint: L₁,₀(it) > 0 and G(it) > 0 imply deriv Q t < 0.
-/
theorem deriv_Q_neg (t : ℝ) (ht : 0 < t) : deriv Q t < 0 := by
  rw [deriv_Q t ht]
  have hL := L₁₀_pos_imag_axis.2 t ht
  have hG := G_imag_axis_pos.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hL hG
  -- (-2π) * (positive) / (positive)² < 0
  apply div_neg_of_neg_of_pos
  · apply mul_neg_of_neg_of_pos
    · simp [pi_pos]
    · exact hL
  · exact sq_pos_of_pos hG

/--
**Proposition 8.12**: `Q` is strictly decreasing on `(0, ∞)`.
Blueprint: Follows from deriv Q < 0 on (0, ∞).
-/
theorem Q_strictAntiOn : StrictAntiOn Q (Set.Ioi 0) := by
  -- Apply strictAntiOn_of_deriv_neg from Mathlib mean value theorem results
  apply strictAntiOn_of_deriv_neg
  · -- Convexity: (0, ∞) is convex
    exact convex_Ioi 0
  · -- Continuity: Q is continuous on (0, ∞)
    exact Q_differentiableOn.continuousOn
  · -- Negative derivative on interior: deriv Q < 0 on (0, ∞)
    -- interior (Ioi 0) = Ioi 0 since Ioi is open
    intro t ht
    rw [interior_Ioi] at ht
    exact deriv_Q_neg t ht

/--
Corollary: `Q` is strictly anti-monotone (decreasing) as a function on positive reals.
-/
theorem Q_strictAnti : ∀ {t₁ t₂ : ℝ}, 0 < t₁ → t₁ < t₂ → Q t₂ < Q t₁ := by
  intro t₁ t₂ ht₁ ht₁₂
  exact Q_strictAntiOn (Set.mem_Ioi.mpr ht₁) (Set.mem_Ioi.mpr (lt_trans ht₁ ht₁₂)) ht₁₂

end MonotoneFG
