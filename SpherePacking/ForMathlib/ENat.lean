import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.OmegaCompletePartialOrder

axiom ENat.tsum_const_eq' {α : Type*} (s : Set α) (c : ENat) :
    ∑' (_ : s), c = s.encard * c
