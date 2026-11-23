module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Order.T5
public import SpherePacking.ForMathlib.ENat

/-!
# Extended Cardinality

Auxiliary lemmas about `Set.encard` and infinite sums over `ℕ∞`.

The basic `tsum` API over `ℕ∞` (`CompleteLattice.summable`, `tsum_add`, `tsum_le_tsum`,
`tsum_insert`, `tsum_iUnion_eq_tsum`, ...) is mathlib's generic `CompleteLattice` API in
`Mathlib.Topology.Algebra.InfiniteSum.Order` (mathlib #38489). The `ℕ∞`-specific lemmas below are
taken from the (closed) mathlib4 PR #23503 by Peter Nelson.
-/

@[expose] public section


-- TODO (BM): make `Scott` a def so we don't end up with a weird topology on ENat

namespace ENat

open Function Set

section tsum

variable {α : Type*} {f g : α → ℕ∞} {s : Set α}

protected theorem tsum_sub (hfin : ∑' a, g a ≠ ⊤) (h : g ≤ f) :
    ∑' a, (f a - g a) = ∑' a, f a - ∑' a, g a := by
  rw [← add_left_inj_of_ne_top hfin, ← tsum_add,
    tsum_congr (fun i ↦ tsub_add_cancel_of_le (h i)), tsub_add_cancel_of_le (tsum_le_tsum h)]

/-- The generic `mul_tsum` needs `IsQuantale ℕ∞`, which mathlib does not provide. -/
protected theorem mul_tsum (c : ℕ∞) : c * ∑' a, f a = ∑' a, c * f a := by
  simp_rw [tsum_eq_iSup_sum, ENat.mul_iSup, Finset.mul_sum]

/-- The generic `tsum_mul` needs `IsQuantale ℕ∞`, which mathlib does not provide. -/
protected theorem tsum_mul (c : ℕ∞) : (∑' a, f a) * c = ∑' a, f a * c := by
  simp_rw [tsum_eq_iSup_sum, ENat.iSup_mul, Finset.sum_mul]

theorem _root_.Set.Infinite.exists_finite_subset_encard_gt (hs : s.Infinite) (b : ℕ) :
    ∃ t ⊆ s, b < t.encard ∧ t.Finite := by
  obtain ⟨t, hts, hcard⟩ := hs.exists_subset_card_eq (b + 1)
  exact ⟨t, by simpa, by simp [encard_coe_eq_coe_finsetCard, hcard, Nat.cast_lt, - Nat.cast_add]⟩

protected theorem tsum_subtype_eq_top_iff_of_finite (hs : s.Finite) :
    ∑' (x : s), f x = ⊤ ↔ ∃ a ∈ s, f a = ⊤ := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | @insert a s₀ has₀ hs₀ ih => simp [tsum_insert has₀, ih]

protected theorem tsum_eq_top_of_support_infinite (hf : f.support.Infinite) : ∑' a, f a = ⊤ := by
  rw [tsum_eq_iSup_sum, iSup_eq_top]
  intro b hb
  lift b to ℕ using hb.ne
  obtain ⟨t, htf, hbt, hfin⟩ := hf.exists_finite_subset_encard_gt b
  refine ⟨hfin.toFinset, hbt.trans_le ?_⟩
  rw [hfin.encard_eq_coe_toFinset_card, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  simp only [Nat.cast_one, Order.one_le_iff_ne_zero]
  exact htf <| by simpa using hi

protected theorem tsum_const_eq_top {ι : Type*} [Infinite ι] {c : ℕ∞} (hc : c ≠ 0) :
    ∑' (_ : ι), c = ⊤ :=
  ENat.tsum_eq_top_of_support_infinite <| by rwa [Function.support_const hc, infinite_univ_iff]

protected theorem tsum_eq_top_iff : ∑' a, f a = ⊤ ↔ f.support.Infinite ∨ ∃ a, f a = ⊤ := by
  rw [iff_def, or_imp, and_iff_right ENat.tsum_eq_top_of_support_infinite, or_iff_not_imp_left,
    not_infinite]
  refine ⟨fun htop hfin ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
  · rw [← tsum_subtype_support, ENat.tsum_subtype_eq_top_iff_of_finite hfin] at htop
    exact Exists.elim htop <| fun a h ↦ ⟨a, h.2⟩
  rw [← top_le_iff, ← ha]
  exact le_tsum f a

protected theorem tsum_subtype_eq_top_iff :
    ∑' (a : s), f a = ⊤ ↔ (s ∩ f.support).Infinite ∨ ∃ a ∈ s, f a = ⊤ := by
  simp only [ENat.tsum_eq_top_iff, Subtype.exists, exists_prop]
  apply or_congr _ Iff.rfl
  have heq : Subtype.val '' (support fun a : s ↦ f ↑a) = s ∩ support f := by
    ext x
    simp only [Set.mem_image, Function.mem_support, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨a, ha⟩, hfa, hax⟩; exact ⟨hax ▸ ha, hax ▸ hfa⟩
    · rintro ⟨hx, hfx⟩; exact ⟨⟨x, hx⟩, hfx, rfl⟩
  rw [← heq, Set.infinite_image_iff Subtype.val_injective.injOn]

protected theorem tsum_subtype_eq_top_of_inter_support_infinite
    (hf : (s ∩ f.support).Infinite) : ∑' (a : s), f a = ⊤ :=
  ENat.tsum_subtype_eq_top_iff.2 <| Or.inl hf

protected theorem tsum_subtype_const_eq_top_of_ne_zero (hs : s.Infinite) {c : ℕ∞}
    (hc : c ≠ 0) : ∑' (_ : s), c = ⊤ :=
  ENat.tsum_subtype_eq_top_of_inter_support_infinite (f := fun _ ↦ c)
    <| by rwa [support_const hc, inter_univ]

end tsum

end ENat

theorem Set.encard_iUnion_of_pairwiseDisjoint {ι α : Type*} {s : ι → Set α}
    (hs : Set.PairwiseDisjoint Set.univ s) : (⋃ i, s i).encard = ∑' i, (s i).encard := by
  simpa [ENat.tsum_set_one] using tsum_iUnion (f := fun _ : α ↦ (1 : ℕ∞)) hs
