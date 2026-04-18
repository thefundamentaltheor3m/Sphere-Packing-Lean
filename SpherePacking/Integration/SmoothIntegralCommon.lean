module
public import SpherePacking.ForMathlib.DerivHelpers
public import SpherePacking.Integration.DifferentiationUnderIntegral
public import SpherePacking.ForMathlib.IteratedDeriv
import SpherePacking.ForMathlib.ExpBounds

/-!
# Smoothness and decay for integrals on `(0, 1)`

This file is a small wrapper around:
- `SpherePacking.Integration.DifferentiationUnderIntegral` (differentiate under the integral sign),
- `SpherePacking.ForMathlib.IteratedDeriv` (package smoothness from a `HasDerivAt` recurrence).

It also provides a standard one-sided decay argument for integrals whose exponential factor has a
uniform norm formula such as `‖cexp ((x : ℂ) * coeff t)‖ = exp (-π * x)`.
-/

namespace SpherePacking.Integration.SmoothIntegralCommon

noncomputable section

open scoped Interval
open Complex Real Set MeasureTheory Filter intervalIntegral
open SpherePacking.Integration.DifferentiationUnderIntegral

variable {coeff hf : ℝ → ℂ}

/-- The basic family of interval integrals, with the `n`-th derivative integrand `gN n`. -/
@[expose] public def I (n : ℕ) (x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, gN (coeff := coeff) (hf := hf) n x t

private lemma hasDerivAt_I_succ
    (continuous_hf : Continuous hf)
    (continuous_coeff : Continuous coeff)
    (exists_bound_norm_h : ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi)
    (n : ℕ) (x₀ : ℝ) :
    HasDerivAt (fun x : ℝ ↦ I (coeff := coeff) (hf := hf) n x)
      (I (coeff := coeff) (hf := hf) (n + 1) x₀) x₀ := by
  simpa [I] using
    (hasDerivAt_integral_gN_of_continuous (coeff := coeff) (hf := hf)
      continuous_hf continuous_coeff exists_bound_norm_h coeff_norm_le (n := n) (x₀ := x₀))

/-- Identify `iteratedDeriv` of `I 0` with `I n`, using the derivative recurrence. -/
public lemma iteratedDeriv_eq_I
    (continuous_hf : Continuous hf)
    (continuous_coeff : Continuous coeff)
    (exists_bound_norm_h : ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi)
    (n : ℕ) :
    iteratedDeriv n (fun x : ℝ ↦ I (coeff := coeff) (hf := hf) 0 x) =
      fun x : ℝ ↦ I (coeff := coeff) (hf := hf) n x := by
  simpa using
    (SpherePacking.ForMathlib.iteratedDeriv_eq_of_hasDerivAt_succ
      (I := fun (n : ℕ) (x : ℝ) => I (coeff := coeff) (hf := hf) n x)
      (fun n x =>
        hasDerivAt_I_succ (coeff := coeff) (hf := hf) continuous_hf continuous_coeff
          exists_bound_norm_h coeff_norm_le (n := n) (x₀ := x))
      n)

/-- Smoothness of `x ↦ I 0 x` under the hypotheses needed for dominated differentiation. -/
public theorem contDiff_integral
    (continuous_hf : Continuous hf)
    (continuous_coeff : Continuous coeff)
    (exists_bound_norm_h : ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ I (coeff := coeff) (hf := hf) 0 x) := by
  simpa using
    SpherePacking.ForMathlib.contDiff_of_hasDerivAt_succ (I := I (coeff := coeff) (hf := hf))
      (fun n x =>
        hasDerivAt_I_succ (coeff := coeff) (hf := hf) continuous_hf continuous_coeff
          exists_bound_norm_h coeff_norm_le n x)

/-- One-sided decay for `I 0 x` from a uniform bound on `‖cexp ((x : ℂ) * coeff t)‖`. -/
private theorem decay_integral
    (continuous_hf : Continuous hf)
    (continuous_coeff : Continuous coeff)
    (exists_bound_norm_h : ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi)
    (norm_cexp : ∀ x t : ℝ, ‖cexp ((x : ℂ) * coeff t)‖ = Real.exp (-Real.pi * x)) :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : ℝ ↦ I (coeff := coeff) (hf := hf) 0 x) x‖ ≤ C := by
  intro k n
  obtain ⟨B, hB⟩ :=
    SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul (k := k) (b := Real.pi) Real.pi_pos
  obtain ⟨Mh, hMh⟩ := exists_bound_norm_h
  have hMh0 : 0 ≤ Mh := (norm_nonneg (hf 1)).trans (hMh 1 (by simp))
  refine ⟨(2 * Real.pi) ^ n * Mh * B, fun x hx => ?_⟩
  have hxabs : ‖x‖ = x := by simp [Real.norm_eq_abs, abs_of_nonneg hx]
  have hrepr := congrArg (fun f : ℝ → ℂ => f x)
    (iteratedDeriv_eq_I (coeff := coeff) (hf := hf)
      continuous_hf continuous_coeff ⟨Mh, hMh⟩ coeff_norm_le (n := n))
  have hnormI :
      ‖I (coeff := coeff) (hf := hf) n x‖ ≤
        (2 * Real.pi) ^ n * Mh * Real.exp (-Real.pi * x) := by
    rw [I]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (1 : ℝ))
      (C := (2 * Real.pi) ^ n * Mh * Real.exp (-Real.pi * x))
      (f := fun t : ℝ ↦ gN (coeff := coeff) (hf := hf) n x t) (fun t ht => ?_)).trans_eq (by simp)
    have hmul : ‖coeff t‖ ^ n * ‖hf t‖ ≤ (2 * Real.pi) ^ n * Mh :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (coeff_norm_le t) n) (hMh t ht)
        (norm_nonneg _) (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi) _)
    calc ‖gN (coeff := coeff) (hf := hf) n x t‖
        = ‖coeff t‖ ^ n * ‖hf t‖ * ‖cexp ((x : ℂ) * coeff t)‖ := by
          simp [gN, g, norm_pow, mul_left_comm, mul_comm, mul_assoc]
      _ ≤ (2 * Real.pi) ^ n * Mh * Real.exp (-Real.pi * x) := by
          simpa [mul_assoc, norm_cexp] using
            (mul_le_mul_of_nonneg_right hmul (norm_nonneg (cexp ((x : ℂ) * coeff t))))
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : ℝ ↦ I (coeff := coeff) (hf := hf) 0 x) x‖
        = x ^ k * ‖I (coeff := coeff) (hf := hf) n x‖ := by
          simp [hxabs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, hrepr]
    _ ≤ x ^ k * ((2 * Real.pi) ^ n * Mh * Real.exp (-Real.pi * x)) := by gcongr
    _ = (2 * Real.pi) ^ n * Mh * (x ^ k * Real.exp (-Real.pi * x)) := by ring
    _ ≤ (2 * Real.pi) ^ n * Mh * B :=
          mul_le_mul_of_nonneg_left (hB x hx)
            (mul_nonneg (pow_nonneg (by positivity) n) hMh0)

/-- Specialize `decay_integral` when `Re (coeff t) = -π` for all `t`. -/
public theorem decay_integral_of_coeff_re
    (continuous_hf : Continuous hf)
    (continuous_coeff : Continuous coeff)
    (exists_bound_norm_h : ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi)
    (coeff_re : ∀ t : ℝ, (coeff t).re = (-Real.pi : ℝ)) :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : ℝ ↦ I (coeff := coeff) (hf := hf) 0 x) x‖ ≤ C := by
  simpa using
    (decay_integral (coeff := coeff) (hf := hf)
      continuous_hf continuous_coeff exists_bound_norm_h coeff_norm_le
      (norm_cexp := fun x t => by
        simp [Complex.norm_exp, Complex.mul_re, coeff_re t, mul_comm]))

end

end SpherePacking.Integration.SmoothIntegralCommon
