/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

/-! The contents of this file should go to Topology.Algebra.InfiniteSum, either
 into Basic or into another file. -/

variable {β : Type*} {f g : β → ℝ}

/-- `HasProd` is monotone for nonnegative real-valued functions. This does not follow from
`hasProd_le` since multiplication on `ℝ` is not covariant. -/
theorem hasProd_le_nonneg {a₁ a₂ : ℝ} (h : ∀ i, f i ≤ g i) (h0 : ∀ i, 0 ≤ f i)
    (hf : HasProd f a₁) (hg : HasProd g a₂) : a₁ ≤ a₂ := by
  apply le_of_tendsto_of_tendsto' hf hg
  intro s
  exact Finset.prod_le_prod (fun i _ => h0 i) (fun i _ => h i)

lemma tprod_le_of_nonneg_of_multipliable (hfnn : 0 ≤ f) (hfg : f ≤ g) (hf : Multipliable f)
    (hg : Multipliable g) : ∏' b, f b ≤ ∏' b, g b :=
  hasProd_le_nonneg hfg hfnn hf.hasProd hg.hasProd
