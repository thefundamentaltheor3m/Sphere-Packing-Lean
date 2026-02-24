/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset


/-!
# `tprod`

Auxiliary lemma about inequalities for `∏'`.

-/

variable {β : Type*} {f g : β → ℝ}

/-- Monotonicity of `∏'` under pointwise inequalities, for nonnegative and multipliable families. -/
public lemma tprod_le_of_nonneg_of_multipliable (hfnn : 0 ≤ f) (hfg : f ≤ g)
    (hf : Multipliable f)
    (hg : Multipliable g) : ∏' b, f b ≤ ∏' b, g b := by
  exact le_of_tendsto_of_tendsto' hf.hasProd hg.hasProd fun s ↦
    Finset.prod_le_prod (fun i _ ↦ hfnn i) (fun i _ ↦ hfg i)
