import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Order

open Complex
open scoped ComplexOrder

protected lemma Complex.le_div_iff₀ {a b c : ℂ} (hc : 0 < c) :
    a ≤ b / c ↔ a * c ≤ b := by
  simp [le_def]
  constructor
  all_goals intro h; simp [div_re, div_im, (le_def.1 <| le_of_lt hc).2.symm] at h ⊢
  · sorry
  · sorry

protected lemma Complex.mul_le_mul_iff_of_pos_right {a b c : ℂ} (hc : 0 < c) :
    a * c ≤ b * c ↔ a ≤ b := by
  simp [le_def, ← (lt_def.1 hc).2]
  constructor
  all_goals intro h;
  · refine ⟨(mul_le_mul_iff_of_pos_right (lt_def.1 hc).1).mp h.1, ?_⟩
    obtain ⟨h₁, h_re | h_im⟩ := h
    · exact h_re
    · exfalso; rw [lt_def] at hc; simp [h_im] at hc
  · exact ⟨(mul_le_mul_iff_of_pos_right (lt_def.1 hc).1).mpr h.1, by simp [h.2]⟩

protected lemma Complex.mul_le_mul_iff_of_pos_left {a b c : ℂ} (hc : 0 < c) :
    c * a ≤ c * b ↔ a ≤ b := by
  simp [mul_comm c _]
  exact Complex.mul_le_mul_iff_of_pos_right hc
