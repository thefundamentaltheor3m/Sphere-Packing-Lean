module
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Instances.ENat
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Order.T5
public import SpherePacking.ForMathlib.ENat

/-!
The contents of this section are taken from mathlib4 PR #23503 by Peter Nelson, and should be
removed once that PR is merged.
-/

namespace ENat

open Function Set

variable {α β : Type*} {f : α → ℕ∞}

private theorem summable : Summable f :=
  HasSum.summable (a := ⨆ s : Finset α, ∑ a ∈ s, f a)
    (tendsto_atTop_iSup fun _ _ ↦ Finset.sum_le_sum_of_subset)

private theorem tsum_comp_le_tsum_of_injective {φ : α → β} (hφ : Injective φ) (g : β → ℕ∞) :
    ∑' x, g (φ x) ≤ ∑' y, g y :=
  (summable (f := fun x => g (φ x))).tsum_le_tsum_of_inj φ hφ (fun _ _ ↦ zero_le _)
    (fun _ ↦ le_rfl) (summable (f := g))

private theorem tsum_comp_eq_tsum_of_bijective {φ : α → β} (hφ : φ.Bijective) (g : β → ℕ∞) :
    ∑' x, g (φ x) = ∑' y, g y :=
  (tsum_comp_le_tsum_of_injective hφ.injective g).antisymm <|
    calc ∑' y, g y = ∑' y, g (φ (surjInv hφ.surjective y)) := by simp [surjInv_eq hφ.surjective]
      _ ≤ ∑' x, g (φ x) :=
        tsum_comp_le_tsum_of_injective (injective_surjInv hφ.surjective) _

private theorem tsum_subtype_iUnion_eq_tsum {ι : Type*} (f : α → ℕ∞) (t : ι → Set α)
    (ht : Pairwise (Disjoint on t)) :
    ∑' x : ⋃ i, t i, f x = ∑' i, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i, t i, f x = ∑' x : Σ i, t i, f x.2 :=
    (tsum_comp_eq_tsum_of_bijective (sigmaToiUnion_bijective t (fun _ _ hij ↦ ht hij)) _).symm
    _ = _ := Summable.tsum_sigma' (fun _ ↦ summable) summable

end ENat

/-- `encard` is additive on pairwise disjoint unions. -/
public theorem Set.encard_iUnion_of_pairwiseDisjoint {ι α : Type*} {s : ι → Set α}
    (hs : Set.PairwiseDisjoint Set.univ s) : (⋃ i, s i).encard = ∑' i, (s i).encard := by
  simpa [ENat.tsum_set_one] using
    (ENat.tsum_subtype_iUnion_eq_tsum (f := fun _ : α => (1 : ℕ∞)) (t := s) (by
      simpa [Set.PairwiseDisjoint, Set.pairwise_univ] using hs))
