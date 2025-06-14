import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.OmegaCompletePartialOrder
import Mathlib.MeasureTheory.Measure.AEDisjoint

-- The API of encard and tsum is quite unfriendly

theorem Set.encard_iUnion_of_pairwiseDisjoint {ι α : Type*} {s : ι → Set α}
    (hs : Set.PairwiseDisjoint Set.univ s) : (⋃ i, s i).encard = ∑' i, (s i).encard := by
  sorry
