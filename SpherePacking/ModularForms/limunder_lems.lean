module
public import Mathlib.Topology.Instances.Complex
import Mathlib.Order.Filter.AtTopBot.Interval

/-!
# Lemmas about `limUnder`

This file collects basic facts about `Filter.limUnder` along `atTop`, geared toward
limits of Cauchy sequences and expressing infinite sums as `limUnder` of partial sums.

## Main statements
* `limUnder_add`
* `limUnder_mul_const`
* `limUnder_sub`
* `limUnder_congr_eventually`
* `tsum_limUnder_atTop`
-/

open Filter

/-- For Cauchy sequences, `limUnder` commutes with addition. -/
public lemma limUnder_add {α : Type*} [Preorder α] [(atTop : Filter α).NeBot] (f g : α → ℂ)
    (hf : CauchySeq f) (hg : CauchySeq g) :
    (limUnder atTop f) + (limUnder atTop g) = limUnder atTop (f + g) := by
  simpa using (Filter.Tendsto.limUnder_eq ((hf.tendsto_limUnder).add (hg.tendsto_limUnder))).symm

/-- For Cauchy sequences, constant scalar multiplication commutes with `limUnder`. -/
public lemma limUnder_mul_const {α : Type*} [Preorder α] [(atTop : Filter α).NeBot] (f : α → ℂ)
    (hf : CauchySeq f) (c : ℂ) :
    c * limUnder atTop f = limUnder atTop (c • f) := by
  simpa using (Filter.Tendsto.limUnder_eq ((hf.tendsto_limUnder).const_mul c)).symm

/-- For Cauchy sequences, `limUnder` commutes with subtraction. -/
public lemma limUnder_sub {α : Type*} [Preorder α] [(atTop : Filter α).NeBot] (f g : α → ℂ)
    (hf : CauchySeq f) (hg : CauchySeq g) :
    (limUnder atTop f) - (limUnder atTop g) = limUnder atTop (f - g) := by
  simpa using (Filter.Tendsto.limUnder_eq ((hf.tendsto_limUnder).sub (hg.tendsto_limUnder))).symm

/-- If `f = g` eventually along `atTop`, then `limUnder atTop f = limUnder atTop g`. -/
public lemma limUnder_congr_eventually (f g : ℕ → ℂ) (h : ∀ᶠ n in atTop, f n = g n)
  (hf : CauchySeq f) :
  limUnder atTop f = limUnder atTop g := by
  exact (Filter.Tendsto.limUnder_eq ((CauchySeq.tendsto_limUnder hf).congr' h)).symm

/-- A summable series over `ℤ` is the `limUnder` of its symmetric partial sums over `Ico (-N) N`. -/
public lemma tsum_limUnder_atTop (f : ℤ → ℂ) (hf : Summable f) : ∑' n, f n =
    limUnder atTop (fun N : ℕ => ∑ n ∈ Finset.Ico (-N : ℤ) N, f n) := by
  simpa using (Filter.Tendsto.limUnder_eq (hf.hasSum.comp (Finset.tendsto_Ico_neg (R := ℤ)))).symm
