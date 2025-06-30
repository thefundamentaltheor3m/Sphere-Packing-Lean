import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Instances.ENat

-- TODO (BM): make `Scott` a def so we don't end up with a weird topology on ENat

theorem Set.encard_iUnion_of_pairwiseDisjoint {ι α : Type*} {s : ι → Set α}
    (hs : Set.PairwiseDisjoint Set.univ s) : (⋃ i, s i).encard = ∑' i, (s i).encard := by
  sorry
