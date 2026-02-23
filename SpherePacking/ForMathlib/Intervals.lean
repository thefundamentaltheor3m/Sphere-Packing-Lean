module
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Basic

/-!
# Interval splitting lemmas

This file provides small set-theoretic identities for splitting open intervals, used to
decompose integrability/integrals into a bounded piece and a tail.
-/

namespace SpherePacking.ForMathlib

open Set

/-- Split `(a, ∞)` into the bounded part `(a, b]` and the tail `(b, ∞)`, assuming `a ≤ b`. -/
public lemma Ioi_eq_Ioc_union_Ioi {a b : ℝ} (hab : a ≤ b) :
    Set.Ioi a = Set.Ioc a b ∪ Set.Ioi b := by
  ext t
  refine ⟨fun ht => (le_or_gt t b).elim (fun htb => Or.inl ⟨ht, htb⟩) Or.inr, ?_⟩
  rintro (ht | ht)
  · exact ht.1
  · exact lt_of_le_of_lt hab ht

end SpherePacking.ForMathlib
