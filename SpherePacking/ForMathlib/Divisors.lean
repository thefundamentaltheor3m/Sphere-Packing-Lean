/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

The contents of this file should eventually be moved to Mathlib/NumberTheory/Divisors.lean
-/

import Mathlib.NumberTheory.Divisors

open Finset

namespace Nat

theorem card_divisors_le_self (n : ℕ) : #n.divisors ≤ n := calc
  _ ≤ #(Ico 1 (n + 1)) := by
    apply card_le_card
    simp only [divisors, filter_subset]
  _ = n := by simp

end Nat

#min_imports
