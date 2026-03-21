module
public import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# ENNReal

This file provides `ENNReal.div_div_div_cancel_left`.
-/

/-- Cancel a common numerator in a ratio of `ENNReal` divisions.

If `a` is nonzero and finite, and `c` is finite, then `(a / b) / (a / c) = c / b`.
-/
public theorem ENNReal.div_div_div_cancel_left {a b c : ENNReal} (ha : a ≠ 0) (ha' : a ≠ ⊤)
    (hc : c ≠ ⊤) :
    (a / b) / (a / c) = c / b := by
  by_cases hb : b = 0
  · simp [ha, hb, div_zero, top_div, div_eq_top, hc, ha']
    split_ifs with hct
    · simp [hct]
    · simp [eq_comm, div_eq_top, hct]
  · rw [← toReal_eq_toReal_iff', toReal_div, toReal_div, toReal_div, toReal_div]
    · rw [div_div_div_cancel_left']
      rw [ne_eq, toReal_eq_zero_iff, not_or]
      tauto
    · simp [*, ne_eq, div_eq_top]
    · simp [*, ne_eq, div_eq_top]
