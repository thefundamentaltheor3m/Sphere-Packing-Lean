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

@[simp] protected theorem tsum_eq_zero : ∑' i, f i = 0 ↔ ∀ i, f i = 0 :=
  Summable.tsum_eq_zero_iff ENat.summable

theorem _root_.Set.Infinite.exists_finite_subset_encard_gt (hs : s.Infinite) (b : ℕ) :
    ∃ t ⊆ s, b < t.encard ∧ t.Finite := by
  obtain ⟨t, hts, hcard⟩ := hs.exists_subset_card_eq (b + 1)
  exact ⟨t, by simpa, by simp [encard_coe_eq_coe_finsetCard, hcard, Nat.cast_lt, - Nat.cast_add]⟩

@[simp]
theorem add_eq_top {x y : ℕ∞} : x + y = ⊤ ↔ x = ⊤ ∨ y = ⊤ :=
  WithTop.add_eq_top

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

protected theorem tsum_subtype_sigma' {β : α → Type*} (f : (Σ a, β a) → ℕ∞) :
    ∑' p : Σ a, β a, f p = ∑' (a) (b), f ⟨a, b⟩ :=
  Summable.tsum_sigma' (fun _ ↦ summable) summable

variable {ι : Type*}

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
