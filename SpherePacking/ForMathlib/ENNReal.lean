module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section

open ENNReal Filter Topology

-- `ENNReal.Tendsto.rpow` is now mathlib's `Filter.Tendsto.ennrpow_const`.

theorem ENNReal.div_div_div_cancel_left {a b c : ENNReal} (ha : a ≠ 0) (ha' : a ≠ ⊤) (hc : c ≠ ⊤) :
    (a / b) / (a / c) = c / b := by
  by_cases hb : b = 0
  · simp [ha, hb, div_zero, top_div, div_eq_top, hc, ha']
    split_ifs with hc
    · simp [hc]
    · simp [eq_comm, div_eq_top, hc]
  · rw [← toReal_eq_toReal_iff', toReal_div, toReal_div, toReal_div, toReal_div]
    · rw [div_div_div_cancel_left']
      rw [ne_eq, toReal_eq_zero_iff, not_or]
      tauto
    · simp [*, ne_eq, div_eq_top]
    · simp [*, ne_eq, div_eq_top]
