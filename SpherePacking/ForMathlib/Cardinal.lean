module

public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

open scoped Cardinal

-- `Cardinal.aux` (`toENat #s = s.encard`) is now mathlib's `Set.toENat_cardinalMk` (a `rfl`-lemma).

example {α : Type*} (s t : Set α) (h : #s ≤ #t) : s.encard ≤ t.encard := by
  convert Cardinal.toENat.monotone' h
