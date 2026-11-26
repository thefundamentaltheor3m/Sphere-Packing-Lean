/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Circle integrals as interval integrals, and circle parametrisations

Proved lemmas used by `change_var` (circle mode) and `cint`, kept apart so
that `change_var` does not import Cauchy's theorem.

* Circle integrals unfold to interval integrals (`circleIntegral_eq_intervalIntegral`), and a
  reparametrised circle integral folds back (`intervalIntegral_circleMap_reparam'`).
* `I ^ t` and `exp (t * I)` are circle parametrisations (`I_cpow_ofReal`, …).
-/

-- Public: `change_var` names these lemmas in the proofs it builds at the user's site.
public section

open Complex
open scoped Real

namespace ChangeVar

/-! ## Circle integrals as interval integrals -/

theorem circleIntegral_eq_intervalIntegral (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    (∮ z in C(c, R), f z) =
      ∫ θ in (0 : ℝ)..2 * π, (R * exp (θ * I) * I) * f (c + R * exp (θ * I)) := by
  simp only [circleIntegral, deriv_circleMap, circleMap, smul_eq_mul, zero_add]

theorem intervalIntegral_circleMap_reparam (g : ℂ → ℂ) (c : ℂ) (R α : ℝ) (hα : α ≠ 0) :
    (∫ t in (0 : ℝ)..2 * π / α,
        (α : ℂ) * (deriv (circleMap c R) (α * t) * g (circleMap c R (α * t)))) =
      ∮ z in C(c, R), g z := by
  have key := intervalIntegral.integral_comp_mul_left (a := 0) (b := 2 * π / α)
    (fun θ => deriv (circleMap c R) θ * g (circleMap c R θ)) hα
  simp only [mul_zero] at key
  have h2 : α * (2 * π / α) = 2 * π := by field_simp
  rw [intervalIntegral.integral_const_mul, key, h2, Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul, mul_inv_cancel₀ hα, Complex.ofReal_one, one_mul]
  simp only [circleIntegral, smul_eq_mul]

theorem intervalIntegral_circleMap_reparam' (g : ℂ → ℂ) (c : ℂ) (R α T : ℝ) (hα : α ≠ 0)
    (hT : α * T = 2 * π) :
    (∫ t in (0 : ℝ)..T,
        (α : ℂ) * (deriv (circleMap c R) (α * t) * g (circleMap c R (α * t)))) =
      ∮ z in C(c, R), g z := by
  have hT' : T = 2 * π / α := by rw [eq_div_iff hα, mul_comm]; exact hT
  subst hT'
  exact intervalIntegral_circleMap_reparam g c R α hα

/-! ## Recognised circle parametrisations (used by `change_var z = ψ`)

Each lemma has the shape `∀ …, ψ t = circleMap c R (α * t)` with the real parameter last. -/

theorem circleMap_self (c : ℂ) (R α t : ℝ) :
    circleMap c R (α * t) = circleMap c R (α * t) := rfl

theorem circleMap_one_mul (c : ℂ) (R t : ℝ) : circleMap c R t = circleMap c R (1 * t) := by
  rw [one_mul]

theorem exp_ofReal_mul_I_eq_circleMap (t : ℝ) : exp (t * I) = circleMap 0 1 (1 * t) := by
  simp [circleMap]

theorem I_cpow_ofReal (t : ℝ) : I ^ (t : ℂ) = circleMap 0 1 (π / 2 * t) := by
  rw [cpow_def_of_ne_zero I_ne_zero, log_I, circleMap]
  simp only [zero_add, ofReal_one, one_mul]
  congr 1
  push_cast
  ring

end ChangeVar

end
