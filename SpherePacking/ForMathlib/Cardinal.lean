import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Basic

open scoped Cardinal

lemma Cardinal.aux {α : Type*} {s : Set α} : toENat #s = s.encard := by
  rfl

example {α : Type*} (s t : Set α) (h : #s ≤ #t) : s.encard ≤ t.encard := by
  convert Cardinal.toENat.monotone' h
