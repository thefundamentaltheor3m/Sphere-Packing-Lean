module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Bounds on compact intervals

This file provides simple existence lemmas for upper and lower bounds of continuous real
functions on compact intervals in `ℝ`.

## Main statements
* `SpherePacking.ForMathlib.exists_upper_bound_on_Icc`
* `SpherePacking.ForMathlib.exists_upper_bound_on_uIoc`
* `SpherePacking.ForMathlib.exists_lower_bound_pos_on_Icc`
-/

namespace SpherePacking.ForMathlib

open Set
open scoped Interval

/-- A continuous function on `Icc a b` admits a (global) upper bound on that interval. -/
public lemma exists_upper_bound_on_Icc {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) :
    ∃ C, ∀ x ∈ Icc a b, g x ≤ C := by
  rcases (isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab) hg) with ⟨x0, -, hxmax⟩
  exact ⟨g x0, fun _ hx => hxmax hx⟩

/--
A continuous function on `Icc a b` admits a (global) upper bound on the unordered interval
`Ι a b`.
-/
public lemma exists_upper_bound_on_uIoc {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) :
    ∃ C, ∀ x ∈ Ι a b, g x ≤ C := by
  rcases exists_upper_bound_on_Icc (g := g) hab hg with ⟨C, hC⟩
  refine ⟨C, fun x hx => hC x (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hx))⟩

/-- Variant of `exists_upper_bound_on_Icc` for a globally continuous function. -/
public lemma Continuous.exists_upper_bound_on_Icc {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ}
    (hab : a ≤ b) : ∃ C, ∀ x ∈ Icc a b, g x ≤ C :=
  SpherePacking.ForMathlib.exists_upper_bound_on_Icc (g := g) hab hg.continuousOn

/--
If `g` is positive and continuous on `Icc a b`, then it admits a positive uniform lower bound.
-/
public lemma exists_lower_bound_pos_on_Icc {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < g x) :
    ∃ c, 0 < c ∧ ∀ x ∈ Icc a b, c ≤ g x := by
  simpa using (isCompact_Icc.exists_forall_le' (f := g) hg (a := (0 : ℝ)) hpos)

end SpherePacking.ForMathlib
