module
public import SpherePacking.MagicFunction.b.PsiBounds

import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Topology.Order.Compact

/-!
# Exponential decay of `H₂` on the positive imaginary axis

This file derives an exponential bound `‖H₂(it)‖ ≤ C * exp(-π t)` for `t ≥ 1`. This is a key input
for bounding `ψS` on the imaginary axis, and hence for the Schwartz decay of the integrals
defining Viazovska's magic function `b`.

## Main statement
* `exists_bound_norm_H₂_resToImagAxis_exp_Ici_one`
-/

namespace MagicFunction.b.PsiBounds.PsiExpBounds

noncomputable section

open scoped Topology UpperHalfPlane

open Complex Real Filter Topology UpperHalfPlane Set
open HurwitzKernelBounds

lemma norm_Θ₂_term_resToImagAxis (n : ℤ) (t : ℝ) (ht : 0 < t) :
    ‖Θ₂_term n ⟨Complex.I * t, by simp [ht]⟩‖ =
      rexp (-π * (((n : ℝ) + (1 / 2)) ^ 2) * t) := by
  set τ : ℍ := ⟨(Complex.I : ℂ) * t, by simp [ht]⟩
  have hτ : (τ : ℂ) = (Complex.I : ℂ) * t := rfl
  have hnorm_pref : ‖cexp (π * (Complex.I : ℂ) * (τ : ℂ) / 4)‖ = rexp (-π * (t / 4)) := by
    simp [Complex.norm_exp, hτ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hnorm_core :
      ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ =
        rexp (-(π * (n : ℝ) ^ 2 * t) - 2 * π * (n : ℝ) * (t / 2)) := by
    have h := norm_jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)
    rw [show ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ =
      rexp (-π * (n : ℝ) ^ 2 * t - 2 * π * (n : ℝ) * (t / 2)) by simpa [hτ] using h]
    ring_nf
  simpa [τ] using (calc
    ‖Θ₂_term n τ‖ =
        ‖cexp (π * (Complex.I : ℂ) * (τ : ℂ) / 4)‖ *
          ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ := by
          simp [Θ₂_term_as_jacobiTheta₂_term, hτ, mul_assoc]
    _ = rexp (-π * (((n : ℝ) + (1 / 2)) ^ 2) * t) := by
          rw [hnorm_pref, hnorm_core, ← Real.exp_add]; congr 1; ring)

lemma norm_Θ₂_resToImagAxis_le (t : ℝ) (ht : 0 < t) :
    ‖Θ₂.resToImagAxis t‖ ≤
      (2 * rexp (-π * ((1 / 2 : ℝ) ^ 2) * t)) / (1 - rexp (-π * t)) := by
  set τ : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hΘ (n : ℤ) : ‖Θ₂_term n τ‖ = f_int 0 (1 / 2 : ℝ) t n := by
    simp [HurwitzKernelBounds.f_int, pow_zero, one_mul,
      show ‖Θ₂_term n τ‖ = rexp (-π * (((n : ℝ) + (1 / 2)) ^ 2) * t) by
        simpa [τ] using norm_Θ₂_term_resToImagAxis n t ht]
  have hsumm : Summable (fun n : ℤ => ‖Θ₂_term n τ‖) :=
    (summable_f_int 0 (1 / 2 : ℝ) ht).congr (fun n => by simpa using (hΘ n).symm)
  have htri : ‖Θ₂.resToImagAxis t‖ ≤ ∑' n : ℤ, ‖Θ₂_term n τ‖ := by
    simpa [ResToImagAxis, Θ₂, τ, ht] using (norm_tsum_le_tsum_norm hsumm)
  have hsum : (∑' n : ℤ, ‖Θ₂_term n τ‖) = F_int 0 ((1 / 2 : ℝ) : UnitAddCircle) t := by
    simpa [HurwitzKernelBounds.F_int] using tsum_congr fun n => by simpa using hΘ n
  have hFint :
      F_int 0 ((1 / 2 : ℝ) : UnitAddCircle) t = F_nat 0 (1 / 2 : ℝ) t + F_nat 0 (1 / 2 : ℝ) t := by
    have h := F_int_eq_of_mem_Icc 0 (a := (1 / 2 : ℝ))
      ⟨by norm_num, by norm_num⟩ ht
    simpa [show (1 : ℝ) - (2⁻¹ : ℝ) = (2⁻¹ : ℝ) by norm_num] using h
  have hbd_nat' :
      F_nat 0 (1 / 2 : ℝ) t ≤ rexp (-π * ((1 / 2 : ℝ) ^ 2) * t) / (1 - rexp (-π * t)) := by
    have hnonneg' : 0 ≤ F_nat 0 (2⁻¹ : ℝ) t := by
      simpa [F_nat] using tsum_nonneg (fun n : ℕ => by
        simp only [HurwitzKernelBounds.f_nat, pow_zero]; positivity)
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg'] using
      (F_nat_zero_le (a := (1 / 2 : ℝ)) (ha := by norm_num) ht)
  grind only

/-- Exponential decay bound for `H₂` on the positive imaginary axis. -/
public lemma exists_bound_norm_H₂_resToImagAxis_exp_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖H₂.resToImagAxis t‖ ≤ C * rexp (-π * t) := by
  let Cθ : ℝ := (2 : ℝ) / (1 - rexp (-π))
  refine ⟨Cθ ^ 4, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hΘ2 : ‖Θ₂.resToImagAxis t‖ ≤ Cθ * rexp (-π * (t / 4)) := by
    have hden_pos : 0 < (1 - rexp (-π : ℝ)) :=
      sub_pos.2 (Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos]))
    calc
      ‖Θ₂.resToImagAxis t‖ ≤
          (2 * rexp (-π * ((1 / 2 : ℝ) ^ 2) * t)) / (1 - rexp (-π * t)) :=
            norm_Θ₂_resToImagAxis_le t ht0
      _ = (2 * rexp (-π * (t / 4))) / (1 - rexp (-π * t)) := by
            rw [show -π * ((1 / 2 : ℝ) ^ 2) * t = -π * (t / 4) by ring]
      _ ≤ (2 * rexp (-π * (t / 4))) / (1 - rexp (-π : ℝ)) :=
            div_le_div_of_nonneg_left (by positivity) hden_pos
              (sub_le_sub_left (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, ht])) 1)
      _ = Cθ * rexp (-π * (t / 4)) := by
            simp [Cθ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  calc
    ‖H₂.resToImagAxis t‖ = ‖Θ₂.resToImagAxis t‖ ^ 4 := by
      simp [H₂, Function.resToImagAxis, ResToImagAxis, ht0, norm_pow]
    _ ≤ (Cθ * rexp (-π * (t / 4))) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hΘ2 4
    _ = (Cθ ^ 4) * rexp (-π * t) := by
      rw [mul_pow, ← Real.exp_nat_mul, show (4 : ℕ) * (-π * (t / 4)) = -π * t by push_cast; ring]

end

end MagicFunction.b.PsiBounds.PsiExpBounds
