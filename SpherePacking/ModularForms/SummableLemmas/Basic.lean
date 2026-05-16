module
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence

open scoped Topology BigOperators Nat

open UpperHalfPlane Complex

/-- Rewrite a `tsum` over `ℕ+` as a shifted `tsum` over `ℕ`. -/
public lemma tsum_pnat_eq_tsum_succ3 {α : Type*} [TopologicalSpace α] [AddCommMonoid α] [T2Space α]
  (f : ℕ → α) : ∑' (n : ℕ+), f ↑n = ∑' (n : ℕ), f (n + 1) := by
  simpa using tsum_pnat_eq_tsum_succ (f := f)

/-- If `f 0 = 0`, then summability over `ℕ+` is equivalent to summability over `ℕ`. -/
public theorem nat_pos_tsum2 {α : Type _} [TopologicalSpace α] [AddCommMonoid α]
    (f : ℕ → α) (hf : f 0 = 0) : (Summable fun x : ℕ+ => f x) ↔ Summable f := by
  simpa [Function.comp] using
    (PNat.coe_injective.summable_iff (f := f) (by
      intro x hx
      rcases Nat.eq_zero_or_pos x with rfl | hx'
      · simpa using hf
      · exact (hx ⟨⟨x, hx'⟩, rfl⟩).elim))

/-- If `f 0 = 0`, then the `tsum` over `ℕ+` agrees with the `tsum` over `ℕ`. -/
public theorem tsum_pNat {α : Type _} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α]
    [T2Space α] [CompleteSpace α] (f : ℕ → α) (hf : f 0 = 0) : ∑' n : ℕ+, f n = ∑' n, f n := by
  by_cases hf2 : Summable f
  · simpa [hf2.tsum_eq_zero_add, hf] using (tsum_pnat_eq_tsum_succ (f := f))
  have hf2' : ¬ Summable fun x : ℕ+ => f x := by simpa [nat_pos_tsum2 f hf] using hf2
  simp [tsum_eq_zero_of_not_summable hf2, tsum_eq_zero_of_not_summable hf2']

/-- Closed form for ∑ n·rⁿ over ℕ+ when ‖r‖ < 1. -/
public lemma tsum_pnat_coe_mul_geometric {r : ℝ} (hr : ‖r‖ < 1) :
    (∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ)) = r / (1 - r) ^ 2 := by
  simpa [tsum_pNat (fun n => n * r ^ n) (by simp)] using tsum_coe_mul_geometric_of_norm_lt_one hr
