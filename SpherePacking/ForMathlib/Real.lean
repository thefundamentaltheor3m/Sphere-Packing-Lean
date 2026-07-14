module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Bound

@[expose] public section

/-! `Real.rpow_ne_one` formerly in this file follows from mathlib's `Real.rpow_right_inj`
(`a ^ b = a ^ 0 = 1 ↔ b = 0` for `0 < a`, `a ≠ 1`). -/

/-- For `0 ≤ r < 1/2` one has `r / (1 - r)³ ≤ 8r`, the standard cheap bound making
geometric-series estimates linear in `r`. -/
@[bound]
theorem div_one_sub_pow_three_le {r : ℝ} (h0 : 0 ≤ r) (hr : r < 1 / 2) :
    r / (1 - r) ^ 3 ≤ 8 * r := by
  have h1 : (1 / 8 : ℝ) ≤ (1 - r) ^ 3 := by nlinarith [sq_nonneg (1 - r)]
  calc r / (1 - r) ^ 3 ≤ r / (1 / 8) :=
        div_le_div_of_nonneg_left h0 (by norm_num) h1
    _ = 8 * r := by ring
