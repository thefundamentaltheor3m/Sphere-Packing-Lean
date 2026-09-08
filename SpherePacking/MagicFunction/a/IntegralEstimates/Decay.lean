/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular
public import SpherePacking.ForMathlib.Analysis.Complex.Exponential

/-!
# Bound on the integral with which we bound I₁, I₃, I₅, J₁, J₃, J₅ and their derivatives
-/

@[expose] public section

open Real MeasureTheory Set


-- [TODO] improve using dot notation for integrability lemmas
/-- Exponential decay beats polynomial growth: for `c < 0` and `0 ≤ a`, the function
`s ↦ exp (c * s) * (d * s ^ n)` is integrable on the ray `[a, ∞)`.

This is the `p = 1`, natural-power case of `integrableOn_rpow_mul_exp_neg_mul_rpow`,
transported from `Ioi 0` to an arbitrary ray `Ici a` with `0 ≤ a`. -/
theorem integrableOn_exp_mul_const_mul_pow_Ici {a c : ℝ} (ha : 0 ≤ a) (hc : c < 0) (d : ℝ)
    (n : ℕ) : IntegrableOn (fun s : ℝ => rexp (c * s) * (d * s ^ n)) (Ici a) volume := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  refine IntegrableOn.congr_fun (((integrableOn_rpow_mul_exp_neg_mul_rpow (s := n) (p := 1)
    (b := -c) (neg_one_lt_zero.trans_le n.cast_nonneg) le_rfl (neg_pos.2 hc)).mono_set
    (Ioi_subset_Ioi ha)).const_mul d) (fun s _ => ?_) measurableSet_Ioi
  rw [rpow_one, rpow_natCast, neg_neg]
  ring

namespace MagicFunction

open Nat

private lemma neg_two_pi_neg : -2 * π < 0 := mul_neg_of_neg_of_pos (by norm_num) pi_pos

theorem pow_mul_integral_le {r : ℝ} (hr : 0 ≤ r) {n : ℕ} :
    r ^ n * ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * rexp (-π * r / s) ≤
      (n / π * rexp (-1)) ^ n * (n)! / (2 * π) ^ (n + 1) := calc
  _ = ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * (r ^ n * rexp (-π * r / s)) := by
      simp only [← smul_eq_mul (a := r ^ n), ← integral_smul]
      grind [smul_eq_mul (a := r ^ n)]
  _ ≤ ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * ((n / π * rexp (-1)) ^ n * s ^ n) := by
      refine setIntegral_mono_of_nonneg ?_ ?_ ?_
      · intro _ hs
        rw [mem_Ici] at hs
        positivity
      · intro s hs
        rw [mem_Ici] at hs
        gcongr 1
        rw [← mul_inv_le_iff₀ (by positivity)]
        calc
        _ = r ^ n * (s ^ n)⁻¹ * rexp (-π * (r / s)) := by ring_nf
        _ = (r / s) ^ n * rexp (-π * (r / s)) := by
            rw [div_pow]
            congr
        _ ≤ _ := exp_neg_mul_decay n pi_pos (x := r / s) <| by positivity
      · exact integrableOn_exp_mul_const_mul_pow_Ici zero_le_one neg_two_pi_neg _ n
  _ ≤ (n / π * rexp (-1)) ^ n * ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * s ^ n := by
      simp only [← smul_eq_mul (a := (n / π * rexp (-1)) ^ n), ← integral_smul]
      grind [smul_eq_mul (a := (n / π * rexp (-1)) ^ n)]
  _ ≤ (n / π * rexp (-1)) ^ n * ∫ s in Ici (0 : ℝ), rexp (-2 * π * s) * s ^ n := by
      gcongr 1
      refine setIntegral_mono_set ?_ (ae_restrict_of_forall_mem measurableSet_Ici ?_) ?_
      · simpa using integrableOn_exp_mul_const_mul_pow_Ici le_rfl neg_two_pi_neg 1 n
      · intro s hs
        rw [mem_Ici] at hs
        positivity
      · filter_upwards with x
        change x ∈ Set.Ici 1 → x ∈ Set.Ici 0
        grind
  _ = (n / π * rexp (-1)) ^ n *
        ∫ s in Ici (0 : ℝ), 1 / (2 * π) ^ n * rexp (-2 * π * s) * (2 * π * s) ^ n := by
      congr with s
      field
  _ = (n / π * rexp (-1)) ^ n * 1 / (2 * π) ^ n *
        ∫ s in Ici (0 : ℝ), rexp (-2 * π * s) * (2 * π * s) ^ n := by
      rw [mul_div_assoc, mul_assoc]
      congr 1
      simp only [← smul_eq_mul (a := 1 / (2 * π) ^ n), ← integral_smul]
      grind [smul_eq_mul (a := 1 / (2 * π) ^ n)]
  _ = (n / π * rexp (-1)) ^ n * 1 / (2 * π) ^ (n + 1) * Gamma (n + 1) := by
      rw [Gamma_eq_integral (by positivity), mul_div_assoc, mul_div_assoc,
        show 1 / (2 * π) ^ (n + 1) = 1 / (2 * π) ^ n * 1 / (2 * π) by field,
        mul_assoc, mul_assoc, mul_div_assoc, mul_assoc]
      congr 2
      -- Now this is a change of variables inside an integral
      let f : ℝ → ℝ := fun x ↦ 2 * π * x
      let f' : ℝ → ℝ := fun _ ↦ 2 * π
      let g : ℝ → ℝ := fun x ↦ rexp (-x) * x ^ n
      let s : Set ℝ := Ici 0
      have hs : MeasurableSet s := measurableSet_Ici
      have hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x := by
        intro x hx
        convert_to HasDerivWithinAt ((2 * π) • id) ((2 * π) • 1) s x
        · aesop
        · aesop
        exact (hasDerivWithinAt_id x s).fun_const_smul (c := (2 * π))
      have hf : InjOn f s := by aesop
      rw [← integral_Ici_eq_integral_Ioi]
      convert_to ∫ (x : ℝ) in s, g (f x) = 1 / (2 * π) * ∫ (x : ℝ) in s, g x
      · simp [s, g, f]
      · simp [s, g]
      have hfs : f '' s = s := by
        ext x
        simp only [mem_image, mem_Ici, s]
        constructor <;> intro hx
        · obtain ⟨y, hy₁, hy₂⟩ := hx
          rw [← hy₂]
          positivity
        · refine ⟨x / (2 * π), by positivity, ?_⟩
          field
      conv_rhs => rw [← hfs]
      simp only [integral_image_eq_integral_abs_deriv_smul hs hf' hf g, f', integral_smul]
      rw [smul_eq_mul, ← mul_assoc]
      conv_lhs => rw [← one_mul (a := ∫ _ in _, _)]
      congr
      rw [abs_mul, abs_of_nonneg (pi_nonneg), abs_of_nonneg (by positivity)]
      field_simp
  _ = _ := by rw [Gamma_nat_eq_factorial n]; field

end MagicFunction
