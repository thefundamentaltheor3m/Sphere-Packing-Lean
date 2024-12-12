/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
import Mathlib

/-! The contents of this file should go to Topology.Algebra.InfiniteSum, either
 into Basic or into another file. -/

variable {β : Type*} {f g : β → ℝ} (hg : Multipliable g)

-- *THIS LEMMA IS WRONG! Eg. constant function ℕ → ℝ : n ↦ 1 / 2*
-- -- This has nothing to do with the fact that the product exists because if it's not
-- -- multipliable, the product is 1. So, we just need to show that all the terms are positive.
-- lemma tprod_pos_of_pos (hf : ∀ b, 0 < f b) : 0 < ∏' b, f b := by
--   if hmul : Multipliable f then
--   · unfold Multipliable at hmul
--     obtain ⟨a, ha⟩ := hmul
--     -- rw [HasProd_iff]
--     sorry
--   else
--   · rw [tprod_eq_one_of_not_multipliable hmul]
--     exact zero_lt_one


lemma tprod_le_of_nonneg (hfnn : 0 ≤ f) (hfg : f ≤ g) : ∏' b, f b ≤ ∏' b, g b := by

  sorry

/- # State:
* Tprod le tprod under nonnegativity assumption, without OrderedCommMonoid
* Tprod positive: make a specific aux lemma for the one we want
-/
