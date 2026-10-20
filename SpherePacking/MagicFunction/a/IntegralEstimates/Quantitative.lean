/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import SpherePacking.MagicFunction.a.IntegralEstimates.Decay
public import SpherePacking.MagicFunction.a.IntegralEstimates.I1
public import SpherePacking.MagicFunction.a.IntegralEstimates.I2
public import SpherePacking.MagicFunction.a.IntegralEstimates.I3
public import SpherePacking.MagicFunction.a.IntegralEstimates.I4
public import SpherePacking.MagicFunction.a.IntegralEstimates.I5
public import SpherePacking.MagicFunction.a.IntegralEstimates.I6

/-!
# Uniform quantitative bounds for the contour integrals

The constants in these estimates are chosen before the squared-radius parameter `r`.
The cusp integrals use the common integral bound from `Decay`; the top edges have
exponential decay, and the vertical tail has an explicit exponential integral.

The `Iⱼ'_pow_mul_norm_le` estimates give polynomially weighted bounds for all six
integrals on `r ≥ 0`, with one constant independent of both `r` and the power `n`.
These concern the original scalar integrals, before any Schwartz extension, and do
not assert bounds on their derivatives.
-/

@[expose] public section

open Real Complex Set MeasureTheory
open MagicFunction.a.RealIntegrals MagicFunction.a.Majorants

namespace MagicFunction.a.IntegralEstimates

/-- Exact integral of the vertical-tail bound, with `r` the squared-radius parameter. -/
private lemma integral_majorant_vertical_eq (r C : ℝ) (hr : 0 ≤ r) :
    (∫ t in Ici (1 : ℝ), C * rexp (-2 * π * t) * rexp (-π * r * t)) =
      C * rexp (-π * (r + 2)) / (π * (r + 2)) := by
  have hneg : -π * (r + 2) < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos pi_pos) (by positivity)
  have heq : (fun t : ℝ ↦ C * rexp (-2 * π * t) * rexp (-π * r * t)) =
      fun t ↦ C * rexp ((-π * (r + 2)) * t) := by
    ext t
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq, integral_const_mul, integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi hneg 1]
  simp only [mul_one, neg_mul, neg_div_neg_eq]
  ring

private lemma norm_cusp_integral_le {C r : ℝ} {g : ℝ → ℂ}
    (hφ : ∀ s : ℝ, 1 / 2 < s → ‖φ₀'' (I * s)‖ ≤ C * rexp (-2 * π * s))
    (hg : ∀ s ∈ Ici (1 : ℝ), ‖g s‖ ≤ ‖φ₀'' (I * s)‖ * rexp (-π * r / s)) :
    ‖∫ s in Ici (1 : ℝ), g s‖ ≤
      C * ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * rexp (-π * r / s) := by
  calc
    _ ≤ ∫ s in Ici (1 : ℝ), C * rexp (-2 * π * s) * rexp (-π * r / s) := by
      apply norm_integral_le_of_norm_le (integrableOn_majorant_cusp r C)
      apply ae_restrict_of_forall_mem measurableSet_Ici
      intro s hs
      apply (hg s hs).trans
      gcongr
      exact hφ s (lt_of_lt_of_le (by norm_num) hs)
    _ = _ := by simp_rw [mul_assoc]; rw [integral_const_mul]

private lemma norm_top_integral_le {C r : ℝ} (hC : 0 ≤ C) {g : ℝ → ℂ} {w : ℝ → ℂ}
    (hφ : ∀ z : ℂ, 1 / 2 < z.im → ‖φ₀'' z‖ ≤ C * rexp (-2 * π * z.im))
    (hw : ∀ t ∈ Ioo (0 : ℝ) 1, 1 / 2 < (w t).im)
    (hg : ∀ t ∈ Ioo (0 : ℝ) 1, ‖g t‖ ≤ ‖φ₀'' (w t)‖ * 2 * rexp (-π * r)) :
    ‖∫ t in Ioo (0 : ℝ) 1, g t‖ ≤ (C * rexp (-π) * 2) * rexp (-π * r) := by
  have hb : ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖g t‖ ≤ C * rexp (-π) * 2 * rexp (-π * r) := by
    intro t ht
    apply (hg t ht).trans
    calc
      _ ≤ C * rexp (-2 * π * (w t).im) * 2 * rexp (-π * r) := by
        gcongr
        exact hφ (w t) (hw t ht)
      _ ≤ _ := by gcongr; nlinarith [hw t ht, pi_pos]
  simpa using norm_integral_le_of_norm_le
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (integrable_const _)
    (ae_restrict_of_forall_mem measurableSet_Ioo hb)

/-- A single constant bounds `I₁'` by the cusp integral for every real parameter. -/
theorem I₁'_bound_uniform : ∃ C > 0, ∀ r : ℝ,
    ‖I₁' r‖ ≤ C * ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * rexp (-π * r / s) := by
  obtain ⟨C, hC, hφ⟩ := norm_φ₀''_I_mul_le
  refine ⟨C, hC, fun r ↦ ?_⟩
  rw [I₁.Complete_Change_of_Variables]
  exact norm_cusp_integral_le hφ (I₁.I₁'_bounding_aux_1 r)

/-- A single constant bounds `I₃'` by the cusp integral for every real parameter. -/
theorem I₃'_bound_uniform : ∃ C > 0, ∀ r : ℝ,
    ‖I₃' r‖ ≤ C * ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * rexp (-π * r / s) := by
  obtain ⟨C, hC, hφ⟩ := norm_φ₀''_I_mul_le
  refine ⟨C, hC, fun r ↦ ?_⟩
  rw [I₃.Complete_Change_of_Variables]
  exact norm_cusp_integral_le hφ (I₃.I₃'_bounding_aux_1 r)

/-- A single constant bounds `I₅'` by the cusp integral for every real parameter. -/
theorem I₅'_bound_uniform : ∃ C > 0, ∀ r : ℝ,
    ‖I₅' r‖ ≤ C * ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * rexp (-π * r / s) := by
  obtain ⟨C, hC, hφ⟩ := norm_φ₀''_I_mul_le
  refine ⟨2 * C, by positivity, fun r ↦ ?_⟩
  rw [I₅.Complete_Change_of_Variables, norm_mul, norm_neg, Complex.norm_ofNat]
  calc
    _ ≤ 2 * (C * ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * rexp (-π * r / s)) := by
      gcongr
      exact norm_cusp_integral_le hφ (I₅.I₅'_bounding_aux_1 r)
    _ = _ := by ring

/-- A single exponential bound for `I₂'`, uniform in the scalar parameter. -/
theorem I₂'_bound_uniform : ∃ C > 0, ∀ r : ℝ, ‖I₂' r‖ ≤ C * rexp (-π * r) := by
  obtain ⟨C, hC, hφ⟩ := norm_φ₀''_le
  refine ⟨C * rexp (-π) * 2, by positivity, fun r ↦ ?_⟩
  rw [I₂.I₂'_eq_integral_g_Ioo]
  exact norm_top_integral_le hC.le hφ I₂.im_parametrisation_lower (I₂.I₂'_bounding_aux_1 r)

/-- A single exponential bound for `I₄'`, uniform in the scalar parameter. -/
theorem I₄'_bound_uniform : ∃ C > 0, ∀ r : ℝ, ‖I₄' r‖ ≤ C * rexp (-π * r) := by
  obtain ⟨C, hC, hφ⟩ := norm_φ₀''_le
  refine ⟨C * rexp (-π) * 2, by positivity, fun r ↦ ?_⟩
  rw [I₄.I₄'_eq_integral_g_Ioo]
  exact norm_top_integral_le hC.le hφ I₄.im_parametrisation_lower (I₄.I₄'_bounding_aux_1 r)

/-- The vertical-tail bound uses `r + 2`, with a constant independent of `r ≥ 0`. -/
theorem I₆'_bound_uniform : ∃ C > 0, ∀ r : ℝ, 0 ≤ r →
    ‖I₆' r‖ ≤ C * rexp (-π * (r + 2)) / (r + 2) := by
  obtain ⟨C, hC, hφ⟩ := norm_φ₀''_I_mul_le
  refine ⟨2 * C / π, by positivity, fun r hr ↦ ?_⟩
  have hb : ‖∫ t in Ici (1 : ℝ), I₆.g r t‖ ≤
      ∫ t in Ici (1 : ℝ), C * rexp (-2 * π * t) * rexp (-π * r * t) := by
    apply norm_integral_le_of_norm_le (integrableOn_majorant_vertical r C hr)
    apply ae_restrict_of_forall_mem measurableSet_Ici
    intro t ht
    rw [I₆.I₆'_bounding_aux_1 r t ht]
    gcongr
    exact hφ t (lt_of_lt_of_le (by norm_num) ht)
  rw [integral_majorant_vertical_eq r C hr] at hb
  rw [I₆.I₆'_eq_integral_g_Ioo, norm_mul, Complex.norm_ofNat]
  calc
    _ ≤ 2 * (C * rexp (-π * (r + 2)) / (π * (r + 2))) := by gcongr
    _ = _ := by simp only [div_mul_eq_div_div]; ring

private lemma pow_mul_norm_le_of_cusp_bound {f : ℝ → ℂ}
    (hf : ∃ C > 0, ∀ r : ℝ,
      ‖f r‖ ≤ C * ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * rexp (-π * r / s)) :
    ∃ C > 0, ∀ (n : ℕ) (r : ℝ), 0 ≤ r →
      r ^ n * ‖f r‖ ≤ C * ((n / π * rexp (-1)) ^ n * n.factorial / (2 * π) ^ (n + 1)) := by
  obtain ⟨C, hC, hf⟩ := hf
  refine ⟨C, hC, fun n r hr ↦ ?_⟩
  calc
    _ ≤ r ^ n * (C * ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * rexp (-π * r / s)) := by
      gcongr
      exact hf r
    _ = C * (r ^ n * ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * rexp (-π * r / s)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_mul_integral_le hr) hC.le

private lemma pow_mul_norm_le_of_exp_bound {f : ℝ → ℂ}
    (hf : ∃ C > 0, ∀ r : ℝ, 0 ≤ r → ‖f r‖ ≤ C * rexp (-π * r)) :
    ∃ C > 0, ∀ (n : ℕ) (r : ℝ), 0 ≤ r →
      r ^ n * ‖f r‖ ≤ C * (n / π * rexp (-1)) ^ n := by
  obtain ⟨C, hC, hf⟩ := hf
  refine ⟨C, hC, fun n r hr ↦ ?_⟩
  calc
    _ ≤ r ^ n * (C * rexp (-π * r)) := by gcongr; exact hf r hr
    _ = C * (r ^ n * rexp (-π * r)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_neg_mul_decay n pi_pos hr) hC.le

/-- Polynomially weighted bounds for `I₁'`, uniform in the power and nonnegative parameter. -/
theorem I₁'_pow_mul_norm_le : ∃ C > 0, ∀ (n : ℕ) (r : ℝ), 0 ≤ r →
    r ^ n * ‖I₁' r‖ ≤ C * ((n / π * rexp (-1)) ^ n * n.factorial / (2 * π) ^ (n + 1)) :=
  pow_mul_norm_le_of_cusp_bound I₁'_bound_uniform

/-- Polynomially weighted bounds for `I₃'`, uniform in the power and nonnegative parameter. -/
theorem I₃'_pow_mul_norm_le : ∃ C > 0, ∀ (n : ℕ) (r : ℝ), 0 ≤ r →
    r ^ n * ‖I₃' r‖ ≤ C * ((n / π * rexp (-1)) ^ n * n.factorial / (2 * π) ^ (n + 1)) :=
  pow_mul_norm_le_of_cusp_bound I₃'_bound_uniform

/-- Polynomially weighted bounds for `I₅'`, uniform in the power and nonnegative parameter. -/
theorem I₅'_pow_mul_norm_le : ∃ C > 0, ∀ (n : ℕ) (r : ℝ), 0 ≤ r →
    r ^ n * ‖I₅' r‖ ≤ C * ((n / π * rexp (-1)) ^ n * n.factorial / (2 * π) ^ (n + 1)) :=
  pow_mul_norm_le_of_cusp_bound I₅'_bound_uniform

/-- Polynomially weighted bounds for `I₂'`, uniform in the power and nonnegative parameter. -/
theorem I₂'_pow_mul_norm_le : ∃ C > 0, ∀ (n : ℕ) (r : ℝ), 0 ≤ r →
    r ^ n * ‖I₂' r‖ ≤ C * (n / π * rexp (-1)) ^ n :=
  pow_mul_norm_le_of_exp_bound (I₂'_bound_uniform.imp fun _ h ↦ ⟨h.1, fun r _ ↦ h.2 r⟩)

/-- Polynomially weighted bounds for `I₄'`, uniform in the power and nonnegative parameter. -/
theorem I₄'_pow_mul_norm_le : ∃ C > 0, ∀ (n : ℕ) (r : ℝ), 0 ≤ r →
    r ^ n * ‖I₄' r‖ ≤ C * (n / π * rexp (-1)) ^ n :=
  pow_mul_norm_le_of_exp_bound (I₄'_bound_uniform.imp fun _ h ↦ ⟨h.1, fun r _ ↦ h.2 r⟩)

/-- Polynomially weighted bounds for `I₆'`, uniform in the power and nonnegative parameter. -/
theorem I₆'_pow_mul_norm_le : ∃ C > 0, ∀ (n : ℕ) (r : ℝ), 0 ≤ r →
    r ^ n * ‖I₆' r‖ ≤ C * (n / π * rexp (-1)) ^ n := by
  apply pow_mul_norm_le_of_exp_bound
  obtain ⟨C, hC, hf⟩ := I₆'_bound_uniform
  refine ⟨C, hC, fun r hr ↦ (hf r hr).trans ?_⟩
  calc
    _ ≤ C * rexp (-π * (r + 2)) := div_le_self (by positivity) (by linarith)
    _ ≤ C * rexp (-π * r) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [pi_pos])) hC.le

end MagicFunction.a.IntegralEstimates
