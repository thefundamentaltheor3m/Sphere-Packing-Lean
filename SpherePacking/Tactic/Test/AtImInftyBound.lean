/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import SpherePacking.ForMathlib.AtImInfty
public import SpherePacking.ForMathlib.Real
public import SpherePacking.ModularForms.exp_lems
public import SpherePacking.ModularForms.Eisenstein
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Tests for `eventually_im_infty`, `isbigo_im_infty`, and the `@[bound]` curation
-/

@[expose] public section

open UpperHalfPlane Filter Complex Real
open scoped Real

section eventually_im_infty

example : ∀ᶠ z : ℍ in atImInfty, 0 < z.im := by
  eventually_im_infty 1 with z hz
  positivity

example (p : ℍ → Prop) (h : ∀ z : ℍ, 2 ≤ z.im → p z) : ∀ᶠ z in atImInfty, p z := by
  eventually_im_infty 2 with z hz
  exact h z hz

-- Bare form: leaves the `∀ z, A ≤ z.im → _` goal, so more variables can be introduced
example (p : ℍ → ℕ → Prop) (h : ∀ z : ℍ, ∀ k : ℕ, p z k) :
    ∀ᶠ z : ℍ in atImInfty, ∀ k : ℕ, p z k := by
  eventually_im_infty 1
  intro z _hz k
  exact h z k

end eventually_im_infty

section isbigo_im_infty

example (f : ℍ → ℂ) (h : ∀ z : ℍ, ‖f z‖ ≤ 3 * z.im) :
    f =O[atImInfty] fun z => (z.im : ℂ) := by
  isbigo_im_infty 3 1 with z hz
  calc ‖f z‖ ≤ 3 * z.im := h z
    _ ≤ 3 * ‖(z.im : ℂ)‖ := by simp [abs_of_pos z.im_pos]

end isbigo_im_infty

section bound_curation

-- `exp (-2π) < 1/2` and the `r/(1-r)³ ≤ 8r` leaf bounds
example : Real.exp (-2 * π) < 1 / 2 := by bound
example {r : ℝ} (h0 : 0 ≤ r) (hr : r < 1 / 2) : r / (1 - r) ^ 3 ≤ 8 * r := by bound
example {q : ℂ} (hq : ‖q‖ < 1 / 2) : ‖q‖ / (1 - ‖q‖) ^ 3 ≤ 8 * ‖q‖ := by bound

-- Norm bounds on `q`-parameters
example (z : ℍ) : ‖cexp (2 * ↑π * Complex.I * z)‖ < 1 := by bound
example (z : ℍ) (hz : 1 ≤ z.im) : ‖cexp (2 * ↑π * Complex.I * z)‖ ≤ Real.exp (-2 * π) := by
  exact norm_exp_two_pi_I_le_exp_neg_two_pi z hz

-- Chaining: `‖q‖ < 1/2` from the two tagged leaves
example (z : ℍ) (hz : 1 ≤ z.im) : ‖cexp (2 * ↑π * Complex.I * z)‖ < 1 / 2 :=
  lt_of_le_of_lt (norm_exp_two_pi_I_le_exp_neg_two_pi z hz) exp_neg_two_pi_lt_half

end bound_curation
