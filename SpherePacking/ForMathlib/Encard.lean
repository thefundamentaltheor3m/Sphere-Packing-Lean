module
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Instances.ENat
public import Mathlib.Data.ENat.Lattice

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Order.T5
public import SpherePacking.ForMathlib.ENat


-- TODO (BM): make `Scott` a def so we don't end up with a weird topology on ENat

/-!
The contents of this section are taken from mathlib4 PR #23503 by Peter Nelson, and should be
removed once that PR is merged.
-/

namespace ENat

open Function Set

section tsum

variable {ι : Sort*} {α β : Type*} {f g : α → ℕ∞} {s t : Set α}

/-- The sum of an `ENat`-valued series is the supremum of its finite partial sums. -/
protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  tendsto_atTop_iSup fun _ _ ↦ Finset.sum_le_sum_of_subset

/-- Any `ENat`-valued series is summable. -/
@[simp] protected theorem summable : Summable f :=
  hasSum.summable

protected theorem tsum_eq_iSup_sum : ∑' x, f x = (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  ENat.hasSum.tsum_eq

protected theorem tsum_comm {f : α → β → ℕ∞} : ∑' (a) (b), f a b = ∑' (b) (a), f a b :=
  Summable.tsum_comm' ENat.summable (fun _ ↦ ENat.summable) fun _ ↦ ENat.summable

protected theorem tsum_prod {f : α → β → ℕ∞} : ∑' p : α × β, f p.1 p.2 = ∑' (a) (b), f a b :=
  Summable.tsum_prod' ENat.summable fun _ ↦ ENat.summable

protected theorem tsum_add : ∑' a, (f a + g a) = ∑' a, f a + ∑' a, g a :=
  Summable.tsum_add ENat.summable ENat.summable

protected theorem tsum_le_tsum (h : f ≤ g) : ∑' a, f a ≤ ∑' a, g a :=
  Summable.tsum_le_tsum h ENat.summable ENat.summable

protected theorem sum_le_tsum {f : α → ℕ∞} (s : Finset α) : ∑ x ∈ s, f x ≤ ∑' x, f x :=
  Summable.sum_le_tsum s (fun _ _ ↦ zero_le _) ENat.summable

protected theorem le_tsum (a : α) : f a ≤ ∑' a, f a :=
  Summable.le_tsum' ENat.summable a

protected theorem le_tsum_of_mem {s : Set α} {a : α} (ha : a ∈ s) : f a ≤ ∑' x : s, f x :=
  ENat.le_tsum (⟨a,ha⟩ : s)

@[simp] protected theorem tsum_eq_zero : ∑' i, f i = 0 ↔ ∀ i, f i = 0 :=
  Summable.tsum_eq_zero_iff ENat.summable

protected theorem tsum_eq_top_of_eq_top : (∃ a, f a = ⊤) → ∑' a, f a = ⊤
  | ⟨a, ha⟩ => top_unique <| ha ▸ ENat.le_tsum a

protected theorem tsum_subtype_eq_top_of_eq_top {s : Set α} (h : ∃ a ∈ s, f a = ⊤) :
    ∑' a : s, f a = ⊤ :=
  let ⟨a, ha, has⟩ := h
  ENat.tsum_eq_top_of_eq_top ⟨⟨a, ha⟩, has⟩

protected theorem tsum_subtype_union_disjoint {s t : Set α} (hd : Disjoint s t) :
    ∑' (x : ↑(s ∪ t)), f x = ∑' (x : s), f x + ∑' (x : t), f x :=
  Summable.tsum_union_disjoint hd ENat.summable ENat.summable

protected theorem tsum_subtype_le_of_subset {s t : Set α} (h : s ⊆ t) :
    ∑' (x : s), f x ≤ ∑' (x : t), f x := by
  rw [← Set.diff_union_of_subset h, ENat.tsum_subtype_union_disjoint disjoint_sdiff_left]
  exact le_add_self

protected theorem tsum_subtype_union_le (s t : Set α) :
    ∑' (x : ↑(s ∪ t)), f (x : α) ≤ ∑' (x : s), f x + ∑' (x : t), f x := by
  rw [← Set.diff_union_self, ENat.tsum_subtype_union_disjoint disjoint_sdiff_left]
  exact add_le_add_left (ENat.tsum_subtype_le_of_subset diff_subset) _

protected theorem tsum_subtype_insert {s : Set α} {a : α} (h : a ∉ s) :
    ∑' (x : ↑(insert a s)), f x = f a + ∑' (x : s), f x := by
  rw [← singleton_union, ENat.tsum_subtype_union_disjoint, tsum_singleton]
  rwa [disjoint_singleton_left]

protected theorem tsum_sub (hfin : ∑' a, g a ≠ ⊤) (h : g ≤ f) :
    ∑' a, (f a - g a) = ∑' a, f a - ∑' a, g a := by
  rw [← WithTop.add_right_inj hfin, ← ENat.tsum_add,
    tsum_congr (fun i ↦ tsub_add_cancel_of_le (h i)), tsub_add_cancel_of_le (ENat.tsum_le_tsum h)]

protected theorem mul_tsum (c : ℕ∞) : c * ∑' a, f a = ∑' a, c * f a := by
  simp_rw [ENat.tsum_eq_iSup_sum, ENat.mul_iSup, Finset.mul_sum]

protected theorem tsum_mul (c : ℕ∞) : (∑' a, f a) * c = ∑' a, f a * c := by
  simp_rw [ENat.tsum_eq_iSup_sum, ENat.iSup_mul, Finset.sum_mul]

theorem _root_.Set.Infinite.exists_finite_subset_encard_gt (hs : s.Infinite) (b : ℕ) :
    ∃ t ⊆ s, b < t.encard ∧ t.Finite := by
  obtain ⟨t, hts, hcard⟩ := hs.exists_subset_card_eq (b + 1)
  exact ⟨t, by simpa, by simp [encard_coe_eq_coe_finsetCard, hcard, Nat.cast_lt, - Nat.cast_add]⟩

@[simp]
theorem add_eq_top {x y : ℕ∞} : x + y = ⊤ ↔ x = ⊤ ∨ y = ⊤ :=
  WithTop.add_eq_top

theorem add_ne_top {x y : ℕ∞} : x + y ≠ ⊤ ↔ x ≠ ⊤ ∧ y ≠ ⊤ :=
  by simp

protected theorem tsum_subtype_eq_top_iff_of_finite (hs : s.Finite) :
    ∑' (x : s), f x = ⊤ ↔ ∃ a ∈ s, f a = ⊤ := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | @insert a s₀ has₀ hs₀ ih => simp [ENat.tsum_subtype_insert has₀, ih]

protected theorem tsum_eq_top_of_support_infinite (hf : f.support.Infinite) : ∑' a, f a = ⊤ := by
  rw [ENat.tsum_eq_iSup_sum, iSup_eq_top]
  intro b hb
  lift b to ℕ using hb.ne
  obtain ⟨t, htf, hbt, hfin⟩ := hf.exists_finite_subset_encard_gt b
  refine ⟨hfin.toFinset, hbt.trans_le ?_⟩
  rw [hfin.encard_eq_coe_toFinset_card, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  simp only [Nat.cast_one, ENat.one_le_iff_ne_zero]
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
  exact ENat.le_tsum a

protected theorem tsum_subtype_eq_top_iff {s : Set α} :
    ∑' (a : s), f a = ⊤ ↔ (s ∩ f.support).Infinite ∨ ∃ a ∈ s, f a = ⊤ := by
  have hsupp_img : (Subtype.val '' support (fun a : s ↦ f a)) = s ∩ f.support := by
    ext a; simp [mem_support, and_comm]
  have hsupp : (support (fun a : s ↦ f a)).Infinite ↔ (s ∩ f.support).Infinite := by
    simpa [hsupp_img] using (Set.infinite_image_iff (s := support (fun a : s ↦ f a))
      (f := Subtype.val) Subtype.val_injective.injOn).symm
  simp [ENat.tsum_eq_top_iff, hsupp]

protected theorem tsum_subtype_eq_top_of_inter_support_infinite {s : Set α}
    (hf : (s ∩ f.support).Infinite) : ∑' (a : s), f a = ⊤ :=
  ENat.tsum_subtype_eq_top_iff.2 <| Or.inl hf

protected theorem tsum_subtype_const_eq_top_of_ne_zero {s : Set α} (hs : s.Infinite) {c : ℕ∞}
    (hc : c ≠ 0) : ∑' (_ : s), c = ⊤ :=
  ENat.tsum_subtype_eq_top_of_inter_support_infinite (f := fun _ ↦ c)
    <| by rwa [support_const hc, inter_univ]

protected theorem tsum_comp_le_tsum_of_injective {φ : α → β} (hφ : Injective φ) (g : β → ℕ∞) :
    ∑' x, g (φ x) ≤ ∑' y, g y :=
  (summable (f := fun x => g (φ x))).tsum_le_tsum_of_inj φ hφ (fun _ _ ↦ zero_le _)
    (fun _ ↦ le_rfl) (summable (f := g))

protected theorem tsum_le_tsum_comp_of_surjective {φ : α → β} (hφ : Surjective φ) (g : β → ℕ∞) :
    ∑' y, g y ≤ ∑' x, g (φ x) :=
  calc ∑' y, g y = ∑' y, g (φ (surjInv hφ y)) := by simp [surjInv_eq hφ]
    _ ≤ ∑' x, g (φ x) := tsum_comp_le_tsum_of_injective (injective_surjInv hφ) _

protected theorem tsum_comp_eq_tsum_of_bijective {φ : α → β} (hφ : φ.Bijective) (g : β → ℕ∞) :
    ∑' x, g (φ x) = ∑' y, g y :=
  (tsum_comp_le_tsum_of_injective hφ.injective g).antisymm
    (tsum_le_tsum_comp_of_surjective hφ.surjective g)

protected theorem tsum_comp_eq_tsum_of_equiv (e : α ≃ β) (g : β → ℕ∞) :
    ∑' x, g (e x) = ∑' y, g y := by
  rw [ENat.tsum_comp_eq_tsum_of_bijective e.bijective]

protected theorem tsum_subtype_mono (f : α → ℕ∞) {s t : Set α} (h : s ⊆ t) :
    ∑' x : s, f x ≤ ∑' x : t, f x :=
  ENat.tsum_comp_le_tsum_of_injective (inclusion_injective h) _

protected theorem tsum_subtype_sigma {β : α → Type*} (f : ∀ a, β a → ℕ∞) :
    ∑' p : Σa, β a, f p.1 p.2 = ∑' (a) (b), f a b :=
  Summable.tsum_sigma' (fun _ ↦ ENat.summable) ENat.summable

protected theorem tsum_subtype_sigma' {β : α → Type*} (f : (Σ a, β a) → ℕ∞) :
    ∑' p : Σ a, β a, f p = ∑' (a) (b), f ⟨a, b⟩ :=
  Summable.tsum_sigma' (fun _ ↦ summable) summable

variable {ι : Type*}

protected theorem tsum_subtype_iUnion_le_tsum (f : α → ℕ∞) (t : ι → Set α) :
    ∑' x : ⋃ i, t i, f x ≤ ∑' i, ∑' x : (t i), f x :=
  calc ∑' x : ⋃ i, t i, f x ≤ ∑' x : Σ i, t i, f x.2 :=
    ENat.tsum_le_tsum_comp_of_surjective (sigmaToiUnion_surjective t) _
  _ = ∑' i, ∑' x : t i, f x := ENat.tsum_subtype_sigma' _

protected theorem tsum_subtype_biUnion_le_tsum (f : α → ℕ∞) (s : Set ι) (t : ι → Set α) :
    ∑' x : ⋃ i ∈ s , t i, f x ≤ ∑' i : s, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i ∈ s, t i, f x = ∑' x : ⋃ i : s, t i, f x := by rw [tsum_congr_subtype]; simp
  _ ≤ ∑' i : s, ∑' x : t i, f x := ENat.tsum_subtype_iUnion_le_tsum _ _

protected theorem tsum_subtype_biUnion_le (f : α → ℕ∞) (s : Finset ι) (t : ι → Set α) :
    ∑' x : ⋃ i ∈ s, t i, f x ≤ ∑ i ∈ s, ∑' x : t i, f x :=
  (ENat.tsum_subtype_biUnion_le_tsum f (SetLike.coe s) t).trans_eq <|
    Finset.tsum_subtype s fun i ↦ ∑' x : t i, f x

protected theorem tsum_subtype_iUnion_le [Fintype ι] (f : α → ℕ∞) (t : ι → Set α) :
    ∑' x : ⋃ i, t i, f x ≤ ∑ i, ∑' x : t i, f x := by
  have : ∑ i, ∑' x : t i, f x = ∑' i, ∑' x : t i, f x := by rw [tsum_fintype]
  exact this ▸ ENat.tsum_subtype_iUnion_le_tsum f t

theorem tsum_subtype_iUnion_eq_tsum (f : α → ℕ∞) (t : ι → Set α) (ht : Pairwise (Disjoint on t)) :
    ∑' x : ⋃ i, t i, f x = ∑' i, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i, t i, f x = ∑' x : Σ i, t i, f x.2 :=
    (tsum_comp_eq_tsum_of_bijective (sigmaToiUnion_bijective t (fun _ _ hij ↦ ht hij)) _).symm
    _ = _ := tsum_subtype_sigma' _

end ENat.tsum
open Function

/-- `encard` is additive on pairwise disjoint unions. -/
public theorem Set.encard_iUnion_of_pairwiseDisjoint {ι α : Type*} {s : ι → Set α}
    (hs : Set.PairwiseDisjoint Set.univ s) : (⋃ i, s i).encard = ∑' i, (s i).encard := by
  simpa [ENat.tsum_set_one] using
    (ENat.tsum_subtype_iUnion_eq_tsum (f := fun _ : α => (1 : ℕ∞)) (t := s) (by
      simpa [Set.PairwiseDisjoint, Set.pairwise_univ] using hs))
