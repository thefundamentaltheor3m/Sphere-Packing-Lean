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
    have h :
        ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ =
          rexp (-π * (n : ℝ) ^ 2 * t - 2 * π * (n : ℝ) * (t / 2)) := by
      simpa [hτ] using norm_jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)
    have : (-π * (n : ℝ) ^ 2 * t - 2 * π * (n : ℝ) * (t / 2)) =
        (-(π * (n : ℝ) ^ 2 * t) - 2 * π * (n : ℝ) * (t / 2)) := by
      ring
    simpa [this] using h
  simpa [τ] using (calc
    ‖Θ₂_term n τ‖ =
        ‖cexp (π * (Complex.I : ℂ) * (τ : ℂ) / 4)‖ *
          ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ := by
          simp [Θ₂_term_as_jacobiTheta₂_term, hτ, mul_assoc]
    _ = rexp (-π * (t / 4)) *
        rexp (-(π * (n : ℝ) ^ 2 * t) - 2 * π * (n : ℝ) * (t / 2)) := by
          simp [hnorm_pref, hnorm_core]
    _ = rexp ((-π * (t / 4)) + (-(π * (n : ℝ) ^ 2 * t) - 2 * π * (n : ℝ) * (t / 2))) := by
          simp [Real.exp_add]
    _ = rexp (-π * (((n : ℝ) + (1 / 2)) ^ 2) * t) := by
          congr 1
          ring
    )

lemma norm_Θ₂_resToImagAxis_le (t : ℝ) (ht : 0 < t) :
    ‖Θ₂.resToImagAxis t‖ ≤
      (2 * rexp (-π * ((1 / 2 : ℝ) ^ 2) * t)) / (1 - rexp (-π * t)) := by
  set τ : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hΘ (n : ℤ) : ‖Θ₂_term n τ‖ = f_int 0 (1 / 2 : ℝ) t n := by
    have hn : ‖Θ₂_term n τ‖ = rexp (-π * (((n : ℝ) + (1 / 2)) ^ 2) * t) := by
      simpa [τ] using norm_Θ₂_term_resToImagAxis n t ht
    simp [HurwitzKernelBounds.f_int, hn, pow_zero, one_mul]
  have hsumm : Summable (fun n : ℤ => ‖Θ₂_term n τ‖) := by
    refine (summable_f_int 0 (1 / 2 : ℝ) ht).congr ?_
    intro n
    simpa using (hΘ n).symm
  have htri : ‖Θ₂.resToImagAxis t‖ ≤ ∑' n : ℤ, ‖Θ₂_term n τ‖ := by
    simpa [ResToImagAxis, Θ₂, τ, ht] using (norm_tsum_le_tsum_norm hsumm)
  have ha : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hsum : (∑' n : ℤ, ‖Θ₂_term n τ‖) = F_int 0 ((1 / 2 : ℝ) : UnitAddCircle) t := by
    have hterm : (∑' n : ℤ, ‖Θ₂_term n τ‖) = ∑' n : ℤ, f_int 0 (1 / 2 : ℝ) t n := by
      refine tsum_congr fun n => ?_
      simpa using hΘ n
    simpa [HurwitzKernelBounds.F_int] using hterm
  have hFint :
      F_int 0 ((1 / 2 : ℝ) : UnitAddCircle) t = F_nat 0 (1 / 2 : ℝ) t + F_nat 0 (1 / 2 : ℝ) t := by
    have h := F_int_eq_of_mem_Icc 0 (a := (1 / 2 : ℝ)) ha ht
    have hsub : (1 : ℝ) - (2⁻¹ : ℝ) = (2⁻¹ : ℝ) := by norm_num
    simpa [hsub] using h
  have hbd_nat' :
      F_nat 0 (1 / 2 : ℝ) t ≤ rexp (-π * ((1 / 2 : ℝ) ^ 2) * t) / (1 - rexp (-π * t)) := by
    have hnonneg : 0 ≤ F_nat 0 (1 / 2 : ℝ) t := by
      have : 0 ≤ (∑' n : ℕ, f_nat 0 (1 / 2 : ℝ) t n) :=
        tsum_nonneg (fun n => by
          simp only [HurwitzKernelBounds.f_nat, pow_zero, one_div]
          positivity)
      simpa [F_nat] using this
    have hnonneg' : 0 ≤ F_nat 0 (2⁻¹ : ℝ) t := by simpa using hnonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg'] using
      (F_nat_zero_le (a := (1 / 2 : ℝ)) (ha := (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))) ht)
  calc
    ‖Θ₂.resToImagAxis t‖ ≤ ∑' n : ℤ, ‖Θ₂_term n τ‖ := htri
    _ = F_int 0 ((1 / 2 : ℝ) : UnitAddCircle) t := hsum
    _ = F_nat 0 (1 / 2 : ℝ) t + F_nat 0 (1 / 2 : ℝ) t := hFint
    _ = 2 * F_nat 0 (1 / 2 : ℝ) t := by ring
    _ ≤ 2 * (rexp (-π * ((1 / 2 : ℝ) ^ 2) * t) / (1 - rexp (-π * t))) := by
          simpa using (mul_le_mul_of_nonneg_left hbd_nat' (by norm_num : (0 : ℝ) ≤ 2))
    _ = (2 * rexp (-π * ((1 / 2 : ℝ) ^ 2) * t)) / (1 - rexp (-π * t)) := by ring

/-- Exponential decay bound for `H₂` on the positive imaginary axis. -/
public lemma exists_bound_norm_H₂_resToImagAxis_exp_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖H₂.resToImagAxis t‖ ≤ C * rexp (-π * t) := by
  let Cθ : ℝ := (2 : ℝ) / (1 - rexp (-π))
  refine ⟨Cθ ^ 4, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hΘ2 :
      ‖Θ₂.resToImagAxis t‖ ≤ Cθ * rexp (-π * (t / 4)) := by
    have hmain := norm_Θ₂_resToImagAxis_le t ht0
    have hquarter :
        rexp (-π * ((1 / 2 : ℝ) ^ 2) * t) = rexp (-π * (t / 4)) := by
      congr 1
      ring
    have hquarter' :
        (2 * rexp (-π * ((1 / 2 : ℝ) ^ 2) * t)) / (1 - rexp (-π * t)) =
          (2 * rexp (-π * (t / 4))) / (1 - rexp (-π * t)) := by
      simpa using congrArg (fun u => (2 * u) / (1 - rexp (-π * t))) hquarter
    have hden_pos : 0 < (1 - rexp (-π : ℝ)) := by
      have : rexp (-π : ℝ) < 1 := by
        simpa [Real.exp_lt_one_iff] using (show (-π : ℝ) < 0 by nlinarith [Real.pi_pos])
      exact sub_pos.2 this
    have hden' : (1 - rexp (-π : ℝ)) ≤ (1 - rexp (-π * t)) := by
      have hmono : rexp (-π * t) ≤ rexp (-π : ℝ) := by
        refine Real.exp_le_exp.2 ?_
        nlinarith [Real.pi_pos, ht]
      simpa using (sub_le_sub_left hmono 1)
    calc
      ‖Θ₂.resToImagAxis t‖ ≤
          (2 * rexp (-π * ((1 / 2 : ℝ) ^ 2) * t)) / (1 - rexp (-π * t)) := hmain
      _ = (2 * rexp (-π * (t / 4))) / (1 - rexp (-π * t)) := hquarter'
      _ ≤ (2 * rexp (-π * (t / 4))) / (1 - rexp (-π : ℝ)) := by
            exact div_le_div_of_nonneg_left (by positivity) hden_pos hden'
      _ = Cθ * rexp (-π * (t / 4)) := by
            simp [Cθ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hH2 :
      ‖H₂.resToImagAxis t‖ = ‖Θ₂.resToImagAxis t‖ ^ 4 := by
    simp [H₂, Function.resToImagAxis, ResToImagAxis, ht0, norm_pow]
  have hpow : ‖Θ₂.resToImagAxis t‖ ^ 4 ≤ (Cθ * rexp (-π * (t / 4))) ^ 4 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hΘ2 4
  calc
    ‖H₂.resToImagAxis t‖ = ‖Θ₂.resToImagAxis t‖ ^ 4 := hH2
    _ ≤ (Cθ * rexp (-π * (t / 4))) ^ 4 := hpow
    _ = (Cθ ^ 4) * rexp (-π * t) := by
          -- `(exp(-π*t/4))^4 = exp(-π*t)`
          have hexp :
              rexp (-π * (t / 4)) ^ 4 = rexp (-π * t) := by
            calc
              rexp (-π * (t / 4)) ^ 4 = rexp (4 * (-π * (t / 4))) := by
                    simpa using (Real.exp_nat_mul (-π * (t / 4)) 4).symm
              _ = rexp (-π * t) := by
                    congr 1
                    ring
          calc
            (Cθ * rexp (-π * (t / 4))) ^ 4 = (Cθ ^ 4) * (rexp (-π * (t / 4)) ^ 4) := by
                  simp [mul_pow]
            _ = (Cθ ^ 4) * rexp (-π * t) := by
                  rw [hexp]

end

end MagicFunction.b.PsiBounds.PsiExpBounds
