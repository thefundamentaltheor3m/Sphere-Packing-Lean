import Mathlib

lemma foo1 (n : ℕ) : n = n := by simp

lemma foo2 (n : ℤ) : n = n := sorry

lemma foo3 : 1 + 1 = 2 := by simp

lemma foo4 : 3 + 4 = 5 := sorry  -- Let's try a false statement
