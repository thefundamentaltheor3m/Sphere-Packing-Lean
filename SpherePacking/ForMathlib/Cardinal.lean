import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Basic

open scoped Cardinal

lemma Cardinal.aux {α : Type*} {s : Set α} : toENat #s = s.encard := by
  by_cases hs : s.Finite
  · have := hs.fintype
    rw [mk_fintype, map_natCast, Set.encard_eq_coe_toFinset_card, Set.toFinset_card]
  · have hs' := hs
    rw [← lt_aleph0_iff_set_finite, not_lt] at hs'
    rw [Set.encard_eq_top_iff.mpr hs, toENat_eq_top.mpr hs']

example {α : Type*} (s t : Set α) (h : #s ≤ #t) : s.encard ≤ t.encard := by
  convert Cardinal.toENat.monotone' h <;> simp [Cardinal.aux]

