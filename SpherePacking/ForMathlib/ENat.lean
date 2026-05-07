module
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Instances.ENat
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# `ENat`-valued `tsum` helpers

Small `ENat` lemmas missing from mathlib, used in the sphere-packing density computation.
-/

/-- The infinite sum of a constant `c : ENat` over a type `α` is `ENat.card α * c`. -/
public theorem ENat.tsum_const {α : Type*} (c : ENat) :
    ∑' (_ : α), c = ENat.card α * c := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  obtain hfin | hinf := fintypeOrInfinite α
  · simp [tsum_fintype]
  simp only [card_eq_top_of_infinite]
  refine HasSum.tsum_eq (by
    change Filter.Tendsto _ _ _
    simp only [Finset.sum_const, nsmul_eq_mul, ne_eq, hc, not_false_eq_true, top_mul]
    refine (tendsto_nhds_top_iff_natCast_lt.2 fun n => ?_)
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α (n + 1)
    filter_upwards [Filter.eventually_ge_atTop s] with t ht
    exact lt_of_lt_of_le (lt_of_lt_of_le
      (by simp only [Nat.cast_lt, hs, Nat.lt_succ_self n] : (n : ℕ∞) < s.card)
      (by simpa using Finset.card_le_card ht))
      (le_mul_of_one_le_right' (ENat.one_le_iff_ne_zero.2 hc)))

/-- The infinite sum of a constant `c : ENat` over a set `s` is `s.encard * c`. -/
public theorem ENat.tsum_set_const {α : Type*} (s : Set α) (c : ENat) :
    ∑' (_ : s), c = s.encard * c := by rw [ENat.tsum_const, Set.encard]

/-- The infinite sum of `1 : ENat` over a set `s` is `s.encard`. -/
public theorem ENat.tsum_set_one {α : Type*} (s : Set α) : ∑' (_ : s), 1 = s.encard := by
  rw [ENat.tsum_const, mul_one, Set.encard]
