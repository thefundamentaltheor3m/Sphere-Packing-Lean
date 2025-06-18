import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem Real.rpow_ne_one {a b : ℝ} (ha : 0 < a) (ha' : a ≠ 1) (hb : b ≠ 0) : a ^ b ≠ 1 := by
  contrapose! hb
  rw [← Real.rpow_zero a] at hb
  by_cases ha'' : 1 < a
  · exact (Real.strictMono_rpow_of_base_gt_one ha'').injective hb
  · have : a < 1 := lt_of_le_of_ne (le_of_not_gt ha'') ha'
    exact (Real.strictAnti_rpow_of_base_lt_one ha this).injective hb
