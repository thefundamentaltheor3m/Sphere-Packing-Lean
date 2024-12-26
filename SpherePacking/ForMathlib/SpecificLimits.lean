/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

The contents of this file should eventually be moved to Mathlib/Analysis/SpecificLimits/Normed.lean
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic

open Filter

theorem summable_real_norm_mul_geometric_of_norm_lt_one {k : ℕ} {r : ℂ}
    (hr : ‖r‖ < 1) {u : ℕ → ℂ} (hu : u =O[atTop] (fun n ↦ (↑(n ^ k) : ℝ))) :
    Summable fun n : ℕ ↦ ‖u n * r ^ n‖ := by
  sorry
