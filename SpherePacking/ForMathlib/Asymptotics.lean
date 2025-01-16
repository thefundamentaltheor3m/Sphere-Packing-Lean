/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

The contents of this file should go somewhere in Mathlib.Analysis.Asymptotics. Not sure where...
-/

import Mathlib.Analysis.Asymptotics.Asymptotics

open Asymptotics Filter

variable {α E : Type*}
variable [LinearOrder α] [Nonempty α]
variable [NormedDivisionRing E]

-- Turns out the following result exists as `IsBigO.mul`.
-- Wonder why exact? didn't work... is this a greater level of generality?
theorem mul_isBigO_mul {f g F G : α → E} (hf : f =O[atTop] F) (hg : g =O[atTop] G) :
    (f * g) =O[atTop] (F * G) := by
  simp [isBigO_iff] at hf hg ⊢
  obtain ⟨cf, af, hf⟩ := hf
  obtain ⟨cg, ag, hg⟩ := hg
  use cf * cg, max af ag
  intro n hn
  specialize hf n (le_of_max_le_left hn)
  specialize hg n (le_of_max_le_right hn)
  calc ‖f n‖ * ‖g n‖
  _ ≤ cf * ‖F n‖ * ‖g n‖ := by gcongr
  _ ≤ cf * ‖F n‖ * (cg * ‖G n‖) := by
        gcongr
        exact Preorder.le_trans 0 ‖f n‖ (cf * ‖F n‖) (norm_nonneg _) hf
  _ = cf * cg * (‖F n‖ * ‖G n‖) := by ring

example {f g F G : α → ℝ} (hf : f =O[atTop] F) (hg : g =O[atTop] G) :
    (f * g) =O[atTop] (F * G) := mul_isBigO_mul hf hg

example {f g F G : ℤ → ℝ} (hf : f =O[atTop] F) (hg : g =O[atTop] G) :
    (f * g) =O[atTop] (F * G) := mul_isBigO_mul hf hg

theorem isBigO_pow {f F : α → E} {n : ℕ} (hf : f =O[atTop] F) :
    (fun x => (f x) ^ n) =O[atTop] (fun x => (F x) ^ n) := by
  induction' n with n hn
  · simp only [pow_zero]
    exact (isBigO_const_const_iff atTop).mpr fun a ↦ a
  · simp only [pow_succ]
    exact IsBigO.mul hn hf

#min_imports
